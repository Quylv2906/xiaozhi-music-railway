#!/usr/bin/env python3
"""
Mochi YouTube Audio Bridge & Payment Soundbox Server
Supports:
1. YouTube audio transcoding for ESP32 on-the-fly.
2. Free Google TTS for Vietnamese voice notifications.
3. SePay.vn & Casso.vn Webhook receiver for automatic TPBank payment notifications.
4. UDP Broadcast to Mochi AI Mini on port 8888.
5. Interactive Web UI test page at /payment_test.
"""

import http.server
import json
import logging
from logging.handlers import RotatingFileHandler
import os
import re
import socket
import socketserver
import ssl
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import yt_dlp

logging.basicConfig(level=logging.INFO, format='%(asctime)s [%(levelname)s] %(message)s')
_bridge_log = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'youtube-bridge.log')
_bridge_handler = RotatingFileHandler(_bridge_log, maxBytes=2_000_000, backupCount=3, encoding='utf-8')
_bridge_handler.setFormatter(logging.Formatter('%(asctime)s [%(levelname)s] %(message)s'))
logging.getLogger().addHandler(_bridge_handler)


def load_local_env(path: str) -> None:
    """Load local secrets without adding a dependency or exposing them to the Web UI."""
    try:
        with open(path, 'r', encoding='utf-8') as env_file:
            for raw_line in env_file:
                line = raw_line.strip()
                if not line or line.startswith('#') or '=' not in line:
                    continue
                key, value = line.split('=', 1)
                os.environ.setdefault(key.strip(), value.strip())
    except FileNotFoundError:
        pass


load_local_env(os.path.join(os.path.dirname(os.path.abspath(__file__)), '.env'))

PORT = int(os.environ.get('PORT', 8000))
HTTPS_PORT = int(os.environ.get('HTTPS_PORT', 8443))
MAX_REQUEST_BODY = 1024 * 1024
CERT_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cert.pem')
KEY_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'key.pem')
FFMPEG_PATH = os.environ.get('FFMPEG_PATH', r'C:\ffmpeg\bin\ffmpeg.exe')
VIETMAP_API_KEY = os.environ.get('VIETMAP_API_KEY', '').strip()
_traffic_signal_cache = {}
_traffic_signal_cache_lock = threading.Lock()
_speed_camera_cache = {}
_speed_camera_cache_lock = threading.Lock()

# Default Account Info for TPBank
BANK_NAME = "TPBank"
BANK_ACC = "0973861224"
BANK_OWNER = "LE VAN QUY"

ydl_search_opts = {
    'format': 'ba[protocol^=http]/ba/b',
    'noplaylist': True,
    'quiet': True,
    'no_warnings': True,
}
ydl = yt_dlp.YoutubeDL(ydl_search_opts)

def get_lan_ip():
    """Detects local LAN IP of this machine."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(('8.8.8.8', 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return '192.168.1.77'

LAN_IP = get_lan_ip()

mochi_cached_ip = '192.168.1.158'

def find_mochi_ip() -> str:
    global mochi_cached_ip
    try:
        output = subprocess.check_output(['arp', '-a'], timeout=1).decode('utf-8', 'ignore')
        for line in output.splitlines():
            if 'c4-9e-7e-3a-60-4c' in line.lower() or 'c4:9e:7e:3a:60:4c' in line.lower():
                parts = line.strip().split()
                if parts and parts[0].startswith('192.168.'):
                    mochi_cached_ip = parts[0]
                    return mochi_cached_ip
    except Exception:
        pass
    return mochi_cached_ip

def send_mochi_udp(data: dict):
    """Broadcasts a JSON packet to Mochi on UDP port 8888."""
    cur_ip = get_lan_ip()
    target_ip = find_mochi_ip()
    msg = json.dumps(data, ensure_ascii=False).encode('utf-8')
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
    try:
        targets = []
        if target_ip:
            targets.append(target_ip)
        try:
            parts = cur_ip.split('.')
            if len(parts) == 4:
                targets.append(f"{parts[0]}.{parts[1]}.{parts[2]}.255")
        except Exception:
            pass
        targets.extend(['255.255.255.255', '192.168.1.255', '192.168.1.31', '192.168.1.28'])
        sent_ips = set()
        for ip in targets:
            if ip not in sent_ips:
                try:
                    sock.sendto(msg, (ip, 8888))
                    sent_ips.add(ip)
                except Exception:
                    pass
        logging.info("Sent UDP payment to port 8888 (targets: %s): %s", list(sent_ips), data)
    except Exception as e:
        logging.error("Failed to broadcast UDP: %s", e)
    finally:
        sock.close()


def decode_polyline(encoded: str):
    """Decode VIETMAP's standard precision-5 polyline into [lon, lat] pairs."""
    points = []
    index = lat = lng = 0
    try:
        while index < len(encoded):
            for is_lat in (True, False):
                value = shift = 0
                while index < len(encoded):
                    byte = ord(encoded[index]) - 63
                    index += 1
                    value |= (byte & 0x1F) << shift
                    shift += 5
                    if byte < 0x20:
                        break
                delta = ~(value >> 1) if value & 1 else value >> 1
                if is_lat:
                    lat += delta
                else:
                    lng += delta
            points.append([lng / 1e5, lat / 1e5])
    except (IndexError, ValueError):
        return []
    return points


def vietmap_instruction_maneuver(sign):
    """Translate GraphHopper-compatible VIETMAP instruction signs to OSRM-like maneuvers."""
    mapping = {
        -3: ('turn', 'sharp left'), -2: ('turn', 'left'), -1: ('turn', 'slight left'),
         0: ('continue', 'straight'),  1: ('turn', 'slight right'), 2: ('turn', 'right'),
         3: ('turn', 'sharp right'),  4: ('arrive', ''), 6: ('roundabout', ''),
        -6: ('roundabout', ''),       7: ('fork', 'slight right'), -7: ('fork', 'slight left'),
        -8: ('uturn', ''),
    }
    return mapping.get(sign, ('continue', 'straight'))


def normalize_vietmap_route(payload: dict):
    """Return the small OSRM-shaped response consumed by the existing Mochi HUD."""
    path = (payload.get('paths') or [None])[0]
    if not isinstance(path, dict):
        raise ValueError('VIETMAP returned no route path')
    coordinates = decode_polyline(path.get('points', ''))
    if not coordinates:
        raise ValueError('VIETMAP route contains no drawable points')
    steps = []
    for item in path.get('instructions') or []:
        if not isinstance(item, dict):
            continue
        interval = item.get('interval') or [0, 0]
        try:
            point_index = min(max(int(interval[0]), 0), len(coordinates) - 1)
        except (TypeError, ValueError, IndexError):
            point_index = 0
        maneuver_type, modifier = vietmap_instruction_maneuver(item.get('sign'))
        steps.append({
            'name': item.get('street_name') or '',
            'distance': item.get('distance') or 0,
            'duration': item.get('time') or 0,
            'maneuver': {
                'type': maneuver_type,
                'modifier': modifier,
                'location': coordinates[point_index],
            },
        })
    return {
        'code': 'Ok',
        'routes': [{
            'distance': path.get('distance') or 0,
            'duration': path.get('time') or 0,
            'geometry': {'coordinates': coordinates},
            'legs': [{'steps': steps}],
            'source': 'vietmap',
        }],
    }


def get_osm_traffic_signals(points):
    """Fetch mapped traffic-signal positions near route maneuvers from OSM."""
    # Use route maneuvers as a bounded sample. This gives a useful density of
    # markers without bulk-downloading an entire city from the public OSM API.
    points = points[:16]
    cache_key = tuple((round(lat, 4), round(lng, 4)) for lat, lng in points)
    now = time.monotonic()
    with _traffic_signal_cache_lock:
        cached = _traffic_signal_cache.get(cache_key)
        if cached and now - cached[0] < 600:
            return cached[1]

    signals, seen = [], set()
    for lat, lng in points:
        delta = 0.00100  # roughly 110 m around each route maneuver
        bbox = f'{lng - delta:.6f},{lat - delta:.6f},{lng + delta:.6f},{lat + delta:.6f}'
        try:
            request = urllib.request.Request(
                'https://api.openstreetmap.org/api/0.6/map?bbox=' + bbox,
                headers={'User-Agent': 'MochiHUD/1.0 (local navigation display)'},
            )
            with urllib.request.urlopen(request, timeout=7) as response:
                root = ET.fromstring(response.read())
        except Exception as exc:
            # A busy public OSM tile must not hide valid signals found at the
            # other route maneuvers.
            logging.info('Skipping unavailable OSM signal area: %s', exc)
            continue
        for node in root.findall('node'):
            tags = {tag.get('k'): tag.get('v') for tag in node.findall('tag')}
            if tags.get('highway') != 'traffic_signals':
                continue
            node_lat, node_lng = float(node.get('lat')), float(node.get('lon'))
            signal_key = (round(node_lat, 6), round(node_lng, 6))
            if signal_key in seen:
                continue
            seen.add(signal_key)
            signals.append({
                'lat': node_lat, 'lng': node_lng,
                'name': tags.get('name') or 'Đèn tín hiệu giao thông',
                'source': 'OpenStreetMap',
            })
    with _traffic_signal_cache_lock:
        _traffic_signal_cache[cache_key] = (now, signals)
    return signals

def get_osm_speed_cameras(points):
    """Return explicitly mapped OSM fixed speed/enforcement camera nodes."""
    points = points[:16]
    cache_key = tuple((round(lat, 4), round(lng, 4)) for lat, lng in points)
    now = time.monotonic()
    with _speed_camera_cache_lock:
        cached = _speed_camera_cache.get(cache_key)
        if cached and now - cached[0] < 600:
            return cached[1]
    cameras, seen = [], set()
    for lat, lng in points:
        delta = 0.0015
        bbox = f'{lng - delta:.6f},{lat - delta:.6f},{lng + delta:.6f},{lat + delta:.6f}'
        request = urllib.request.Request('https://api.openstreetmap.org/api/0.6/map?bbox=' + bbox,
            headers={'User-Agent': 'MochiHUD/1.0 (local navigation display)'})
        with urllib.request.urlopen(request, timeout=10) as response:
            root = ET.fromstring(response.read())
        for node in root.findall('node'):
            tags = {tag.get('k'): tag.get('v') for tag in node.findall('tag')}
            if tags.get('highway') != 'speed_camera' and tags.get('enforcement') not in ('maxspeed', 'traffic_signals'):
                continue
            node_lat, node_lng = float(node.get('lat')), float(node.get('lon'))
            marker = (round(node_lat, 6), round(node_lng, 6))
            if marker in seen:
                continue
            seen.add(marker)
            raw_limit = tags.get('maxspeed', '')
            limit_match = re.search(r'\d{1,3}', raw_limit)
            cameras.append({'lat': node_lat, 'lng': node_lng,
                'name': tags.get('name') or 'Camera tốc độ (OSM)',
                'limit': int(limit_match.group()) if limit_match else 0,
                'source': 'OpenStreetMap'})
    with _speed_camera_cache_lock:
        _speed_camera_cache[cache_key] = (now, cameras)
    return cameras


def format_vietnamese_amount(n: int) -> str:
    """Converts a number into natural spoken Vietnamese words."""
    if n >= 1_000_000:
        tri = n // 1_000_000
        rem = n % 1_000_000
        if rem == 0:
            return f"{tri} triệu"
        nghin = rem // 1_000
        return f"{tri} triệu {nghin} nghìn" if nghin > 0 else f"{tri} triệu"
    if n >= 1_000:
        nghin = n // 1_000
        return f"{nghin} nghìn"
    return f"{n}"

def parse_vietnamese_bank_notification(text: str, title: str = "") -> tuple[int, str, str]:
    """
    Parses notification text from Vietnamese banks (TPBank, Vietcombank, MB, Techcombank, MoMo, etc.)
    Returns (amount, sender, content).
    """
    full = f"{title} {text}".strip()
    logging.info("Parsing bank notification: %s", full)

    # 1. Ignore negative transactions (money spent)
    has_minus = bool(re.search(r'-\s*[0-9.,]{2,15}\s*(?:VND|đ|d)?', full, re.IGNORECASE))
    has_plus = bool(re.search(r'\+\s*[0-9.,]{2,15}\s*(?:VND|đ|d)?', full, re.IGNORECASE))
    if has_minus and not has_plus:
        logging.info("Ignored debit transaction (money spent).")
        return 0, "", ""

    # 2. Extract amount (e.g. +50,000 VND or +50.000d)
    amount = 0
    m_plus = re.search(r'\+\s*([0-9.,]{2,15})\s*(?:VND|đ|d)?', full, re.IGNORECASE)
    if m_plus:
        clean = re.sub(r'[^\d]', '', m_plus.group(1))
        if clean:
            amount = int(clean)

    if amount == 0:
        m_vnd = re.search(r'([0-9.,]{2,15})\s*(?:VND|đ|d\b)', full, re.IGNORECASE)
        if m_vnd:
            clean = re.sub(r'[^\d]', '', m_vnd.group(1))
            if clean:
                amount = int(clean)

    if amount == 0:
        # Match standalone numbers like 50,000 or 50.000 or 50000
        m_any = re.search(r'(?:^|[^\d])([1-9][0-9.,]{3,12})(?:[^\d]|$)', full)
        if m_any:
            clean = re.sub(r'[^\d]', '', m_any.group(1))
            if clean:
                val = int(clean)
                if val >= 1000:
                    amount = val

    if amount < 1000:
        return 0, "", ""

    # 3. Extract sender
    sender = "Khách hàng"
    m_sender = re.search(r'(?:tu|từ|sender|nguoi gui|người gửi):\s*([^,.\n;]+)', full, re.IGNORECASE)
    if m_sender:
        sender = m_sender.group(1).strip()
    else:
        m_from = re.search(r'(?:tu|từ)\s+([a-zA-Z\u00C0-\u1EF9\s]{3,30})', full, re.IGNORECASE)
        if m_from:
            sender = m_from.group(1).strip().title()

    # 4. Extract content
    content = "Chuyển khoản TPBank"
    m_content = re.search(r'(?:ND|Nội dung|Noi dung|memo|ly do|lý do):\s*([^.\n;]+)', full, re.IGNORECASE)
    if m_content:
        content = m_content.group(1).strip()

    return amount, sender, content

HTML_TEST_PAGE = """<!DOCTYPE html>
<html lang="vi">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Loa Thanh Toán TPBank • Mochi AI Mini</title>
    <style>
        :root {
            --tp-purple: #7C3AED;
            --tp-purple-light: #A78BFA;
            --tp-dark: #0F172A;
            --tp-card: #1E293B;
            --tp-green: #10B981;
            --tp-cyan: #06B6D4;
        }
        * { box-sizing: border-box; margin: 0; padding: 0; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; }
        body { background: var(--tp-dark); color: #F1F5F9; padding: 20px; display: flex; justify-content: center; }
        .container { width: 100%; max-width: 600px; }
        .header { text-align: center; margin-bottom: 24px; padding: 20px; background: linear-gradient(135deg, #4C1D95, #7C3AED); border-radius: 16px; box-shadow: 0 10px 25px rgba(124, 58, 237, 0.3); }
        .header h1 { font-size: 24px; font-weight: 800; margin-bottom: 6px; }
        .header p { color: #E9D5FF; font-size: 14px; }
        .card { background: var(--tp-card); border-radius: 14px; padding: 20px; margin-bottom: 20px; border: 1px solid #334155; }
        .card h2 { font-size: 16px; color: var(--tp-purple-light); margin-bottom: 14px; display: flex; align-items: center; gap: 8px; }
        .acc-info { display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-bottom: 10px; }
        .acc-box { background: #0F172A; padding: 12px; border-radius: 8px; border: 1px solid #283548; }
        .acc-box .label { font-size: 11px; color: #94A3B8; text-transform: uppercase; }
        .acc-box .val { font-size: 15px; font-weight: 700; color: var(--tp-cyan); margin-top: 2px; }
        label { display: block; font-size: 13px; color: #94A3B8; margin-top: 12px; margin-bottom: 6px; }
        input, select { width: 100%; padding: 12px; background: #0F172A; border: 1px solid #334155; border-radius: 8px; color: #fff; font-size: 15px; }
        input:focus { outline: none; border-color: var(--tp-purple-light); }
        .quick-grid { display: grid; grid-template-columns: repeat(4, 1fr); gap: 8px; margin-top: 14px; }
        .btn-quick { padding: 10px; background: #334155; border: none; border-radius: 8px; color: #fff; font-weight: 600; cursor: pointer; transition: 0.2s; }
        .btn-quick:hover { background: var(--tp-purple); }
        .btn-send { width: 100%; margin-top: 18px; padding: 14px; background: linear-gradient(135deg, #10B981, #059669); border: none; border-radius: 10px; color: white; font-size: 16px; font-weight: 700; cursor: pointer; box-shadow: 0 4px 15px rgba(16, 185, 129, 0.3); transition: 0.2s; }
        .btn-send:hover { opacity: 0.92; transform: translateY(-1px); }
        .webhook-box { background: #0F172A; padding: 12px; border-radius: 8px; border: 1px dashed #475569; word-break: break-all; font-family: monospace; font-size: 13px; color: #38BDF8; margin-top: 8px; }
        .log-box { max-height: 140px; overflow-y: auto; background: #0B0F17; padding: 10px; border-radius: 8px; font-family: monospace; font-size: 12px; color: #A7F3D0; }
        .toast { display: none; padding: 12px; background: #065F46; color: #A7F3D0; border-radius: 8px; margin-top: 12px; text-align: center; font-weight: 600; }
    
        
</style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>🔔 Loa Thanh Toán TPBank</h1>
            <p>Mochi AI Mini • Tự động hiển thị QR & Đọc biến động số dư</p>
        </div>

        <div class="card">
            <h2>💳 Thông tin Tài khoản Nhận tiền</h2>
            <div class="acc-info">
                <div class="acc-box">
                    <div class="label">Ngân hàng</div>
                    <div class="val">TPBank (Tiên Phong)</div>
                </div>
                <div class="acc-box">
                    <div class="label">Số tài khoản</div>
                    <div class="val">0973 861 224</div>
                </div>
            </div>
            <div class="acc-box">
                <div class="label">Chủ tài khoản</div>
                <div class="val">LE VAN QUY</div>
            </div>
        </div>

        <div class="card">
            <h2>⚡ Bắn Thử Thông Báo Nhận Tiền Sang Mochi</h2>
            <label>Số tiền (VNĐ):</label>
            <input type="number" id="amount" value="50000" step="10000">

            <div class="quick-grid">
                <button class="btn-quick" onclick="setAmt(20000)">20.000 đ</button>
                <button class="btn-quick" onclick="setAmt(50000)">50.000 đ</button>
                <button class="btn-quick" onclick="setAmt(100000)">100.000 đ</button>
                <button class="btn-quick" onclick="setAmt(200000)">200.000 đ</button>
            </div>

            <label>Tên người gửi:</label>
            <input type="text" id="sender" value="Nguyễn Văn A">

            <label>Nội dung chuyển khoản:</label>
            <input type="text" id="content" value="Ủng hộ Mochi AI">

            <button class="btn-send" onclick="sendNotify()">🔊 BẮN THÔNG BÁO TING TING SANG MOCHI</button>
            <button class="btn-send" style="background: linear-gradient(135deg, #7C3AED, #4F46E5); margin-top: 10px;" onclick="changeQr()">📱 ĐỔI MÃ QR TRÊN MÀN HÌNH MOCHI</button>

            <div id="toast" class="toast">✓ Đã gửi thông báo sang Mochi! Đang phát loa...</div>
        </div>

        <div class="card">
            <h2>🔗 Địa chỉ Webhook Tự Động (Dán vào SePay.vn)</h2>
            <p style="font-size: 13px; color: #94A3B8;">Khi đăng ký trên SePay.vn, dán link webhook này vào để khi có tiền về TPBank thật, SePay sẽ tự động gọi loa Mochi:</p>
            <div class="webhook-box" id="webhook-url">Đang tải...</div>
        </div>

        <div class="card" style="border: 1px solid #7C3AED;">
            <h2>🤖 Cấu hình Tự động trên Android (MacroDroid - Không cần SePay)</h2>
            <p style="font-size: 13px; color: #E9D5FF; margin-bottom: 10px;">
                Mỗi khi App TPBank nhận thông báo tiền về, MacroDroid trên Android sẽ tự động gửi thông báo sang Mochi:
            </p>
            <div class="webhook-box" id="macrodroid-url" style="color: #F472B6;">Đang tải...</div>
            <div style="margin-top: 12px; font-size: 13px; color: #94A3B8; line-height: 1.6;">
                <b>3 bước thiết lập trên MacroDroid:</b><br>
                1. <b>Kích hoạt (Trigger):</b> Sự kiện thiết bị &gt; Thông báo &gt; Đã nhận thông báo &gt; Chọn ứng dụng <b>TPBank</b>.<br>
                2. <b>Hành động (Action):</b> Ứng dụng &gt; Yêu cầu HTTP &gt; Phương thức <b>GET</b> &gt; Dán link ở trên vào ô URL.<br>
                3. Bấm Lưu Macro là xong!
            </div>
            <label style="margin-top: 14px;">Thử nghiệm giả lập thông báo từ điện thoại Android gửi sang:</label>
            <input type="text" id="sim-notif" value="TK 0973861224: +50,000 VND vao luc 09:00. ND: NGUYEN VAN A chuyen tien">
            <button class="btn-send" style="background: linear-gradient(135deg, #EC4899, #8B5CF6); margin-top: 10px;" onclick="testSimNotif()">🧪 THỬ GIẢ LẬP MACRODROID GỬI THÔNG BÁO</button>
        </div>

        <div class="card">
            <h2>📜 Nhật ký Giao dịch Gần nhất</h2>
            <div id="log-box" class="log-box">Chưa có giao dịch thử nghiệm nào.</div>
        </div>
    </div>

    <script>
        const host = window.location.host;
        document.getElementById('webhook-url').innerText = 'http://' + host + '/webhook/sepay';
        document.getElementById('macrodroid-url').innerText = 'http://' + host + '/api/bank_notify?title=[notif_title]&text=[notif_text]';

        async function testSimNotif() {
            const text = document.getElementById('sim-notif').value;
            try {
                const res = await fetch('/api/bank_notify?title=TPBank&text=' + encodeURIComponent(text));
                const data = await res.json();
                if (data.status === 'ok') {
                    showToast('✓ MacroDroid parse thành công: +' + data.amount.toLocaleString('vi-VN') + ' đ từ ' + data.sender);
                    addLog('🤖 MacroDroid: +' + data.amount.toLocaleString('vi-VN') + ' đ (' + data.spoken + ')');
                } else {
                    alert('Không tìm thấy số tiền hợp lệ: ' + data.reason);
                }
            } catch (err) {
                alert('Lỗi: ' + err.message);
            }
        }

        function setAmt(val) {
            document.getElementById('amount').value = val;
        }

        async function sendNotify() {
            const amount = parseInt(document.getElementById('amount').value) || 50000;
            const sender = document.getElementById('sender').value || 'Khách hàng';
            const content = document.getElementById('content').value || 'Thanh toan';

            try {
                const res = await fetch('/api/payment_notify', {
                    method: 'POST',
                    headers: {'Content-Type': 'application/json'},
                    body: JSON.stringify({ amount, sender, content })
                });
                const data = await res.json();
                showToast('✓ Đã bắn thông báo! Mochi đang reo: ' + data.spoken);
                addLog('✓ Thành công: +' + amount.toLocaleString('vi-VN') + ' đ từ ' + sender);
            } catch (err) {
                alert('Lỗi: ' + err.message);
            }
        }

        async function changeQr() {
            const amount = parseInt(document.getElementById('amount').value) || 0;
            try {
                await fetch('/api/qr_change', {
                    method: 'POST',
                    headers: {'Content-Type': 'application/json'},
                    body: JSON.stringify({ amount })
                });
                showToast('✓ Đã chuyển mã QR trên Mochi sang số tiền: ' + amount.toLocaleString('vi-VN') + ' đ');
                addLog('📱 Đổi QR: ' + amount.toLocaleString('vi-VN') + ' đ');
            } catch (err) {
                alert('Lỗi: ' + err.message);
            }
        }

        function showToast(msg) {
            const t = document.getElementById('toast');
            t.innerText = msg;
            t.style.display = 'block';
            setTimeout(() => { t.style.display = 'none'; }, 4000);
        }

        function addLog(text) {
            const box = document.getElementById('log-box');
            const time = new Date().toLocaleTimeString('vi-VN');
            box.innerHTML = '<div>[' + time + '] ' + text + '</div>' + box.innerHTML;
        }
    </script>
</body>
</html>
"""

HTML_MASCOT_PAGE = """<!DOCTYPE html>
<html lang="vi"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Mochi Studio</title><style>
body{margin:0;min-height:100vh;background:#0b1020;color:#eef2ff;font-family:system-ui,sans-serif;display:grid;place-items:center}.card{width:min(680px,92vw);padding:28px;border-radius:24px;background:#131b32;border:1px solid #29375f;box-shadow:0 24px 80px #0008}h1{margin:0;color:#7dd3fc}.face{font-size:82px;text-align:center;margin:12px}.grid{display:grid;grid-template-columns:repeat(3,1fr);gap:10px}button{border:0;border-radius:14px;padding:16px 8px;background:#1e2a4d;color:#fff;font-size:15px;cursor:pointer}button:hover{background:#2563eb}#status{text-align:center;color:#86efac;min-height:24px;margin:18px 0 0}.note{font-size:13px;color:#a5b4cf;text-align:center;margin-top:14px}</style></head>
<body><main class="card"><h1>✨ Mochi Studio</h1><div class="face" id="face">(•‿•)</div><p>Chọn cảm xúc để gửi ngay sang Mochi</p><div class="grid">
<button onclick="setMood('happy','(≧▽≦)')">Vui vẻ</button><button onclick="setMood('thinking','(•_•)?')">Suy nghĩ</button><button onclick="setMood('curious','(◕‿◕)')">Tò mò</button><button onclick="setMood('wink','(•‿-)')">Nháy mắt</button><button onclick="setMood('loving','(♥‿♥)')">Yêu thích</button><button onclick="setMood('cool','(⌐■_■)')">Ngầu</button><button onclick="setMood('surprised','(O_O)')">Ngạc nhiên</button><button onclick="setMood('sleepy','(-_-) zZ')">Buồn ngủ</button><button onclick="setMood('neutral','(•‿•)')">Bình thường</button>
</div><div id="status"></div><div class="note">Mochi Studio điều khiển biểu cảm qua mạng nội bộ.</div></main><script>async function setMood(emotion,face){const r=await fetch('/api/mochi/emotion?emotion='+encodeURIComponent(emotion));const d=await r.json();document.getElementById('face').textContent=face;document.getElementById('status').textContent=d.status==='ok'?'Đã gửi: '+emotion:'Không gửi được';}</script></body></html>"""

HTML_WAZE_PAGE = """<!DOCTYPE html>
<html lang="vi">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
    <title>Mochi Car HUD • Dẫn Đường Thông Minh v2.0</title>
    <!-- Fonts -->
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link href="https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700;800;900&family=Rajdhani:wght@600;700;800&display=swap" rel="stylesheet">
    <!-- Leaflet Assets -->
    <link rel="stylesheet" href="/leaflet.css?v=4">
    <script src="/leaflet.js?v=4"></script>
    <script>
        if (typeof L === 'undefined') {
            document.write('<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.css">');
            document.write('<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.js"><' + '/script>');
        }
    </script>
    <style>
        :root {
            --bg-dark: #050811;
            --bg-card: rgba(13, 20, 36, 0.82);
            --bg-card-hover: rgba(20, 32, 58, 0.9);
            --border-glass: rgba(255, 255, 255, 0.08);
            --border-cyan: rgba(0, 240, 255, 0.35);
            --cyan: #00F0FF;
            --cyan-glow: rgba(0, 240, 255, 0.35);
            --blue: #2563EB;
            --blue-gradient: linear-gradient(135deg, #2563EB, #06B6D4);
            --green: #10B981;
            --green-glow: rgba(16, 185, 129, 0.35);
            --red: #EF4444;
            --red-glow: rgba(239, 68, 68, 0.45);
            --amber: #F59E0B;
            --text-main: #F8FAFC;
            --text-muted: #94A3B8;
            --radius-lg: 20px;
            --radius-md: 14px;
            --radius-sm: 10px;
        }

        * { box-sizing: border-box; margin: 0; padding: 0; -webkit-tap-highlight-color: transparent; }
        body {
            font-family: 'Plus Jakarta Sans', -apple-system, BlinkMacSystemFont, sans-serif;
            background: var(--bg-dark);
            color: var(--text-main);
            min-height: 100vh;
            display: flex;
            justify-content: center;
            padding: 12px 10px 40px;
            background-image: 
                radial-gradient(circle at 50% 0%, rgba(37, 99, 235, 0.15) 0%, transparent 60%),
                radial-gradient(circle at 100% 100%, rgba(0, 240, 255, 0.08) 0%, transparent 50%);
            transition: background 0.3s ease;
        }

        .app-container { width: 100%; max-width: 480px; display: flex; flex-direction: column; gap: 12px; }

        /* ── TOP HEADER ── */
        .top-nav {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 10px 14px;
            background: var(--bg-card);
            backdrop-filter: blur(16px);
            -webkit-backdrop-filter: blur(16px);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-md);
            box-shadow: 0 4px 20px rgba(0,0,0,0.4);
        }
        .brand { display: flex; align-items: center; gap: 8px; font-weight: 800; font-size: 15px; letter-spacing: -0.3px; }
        .brand-icon {
            width: 32px; height: 32px;
            background: var(--blue-gradient);
            border-radius: 9px;
            display: flex; align-items: center; justify-content: center;
            font-size: 16px; box-shadow: 0 4px 12px var(--cyan-glow);
        }
        .header-actions { display: flex; align-items: center; gap: 8px; }

        .btn-header-tool {
            height: 32px;
            padding: 0 10px;
            background: rgba(30, 41, 59, 0.7);
            border: 1px solid var(--border-glass);
            border-radius: 8px;
            color: #FFF; font-size: 11px; font-weight: 700;
            cursor: pointer; display: flex; align-items: center; gap: 5px;
            transition: all 0.2s;
        }
        .btn-header-tool:hover, .btn-header-tool:active {
            background: rgba(37, 99, 235, 0.3);
            border-color: var(--cyan);
            color: var(--cyan);
        }
        .btn-header-tool.active-hud-btn {
            background: linear-gradient(135deg, #0284C7, #00F0FF);
            color: #040711;
            font-weight: 800;
            box-shadow: 0 0 14px var(--cyan-glow);
        }

        .status-badge {
            display: flex; align-items: center; gap: 6px;
            padding: 5px 10px;
            background: rgba(16, 185, 129, 0.12);
            border: 1px solid rgba(16, 185, 129, 0.3);
            border-radius: 20px;
            font-size: 11px; font-weight: 700; color: #6EE7B7;
        }
        .pulse-dot {
            width: 6px; height: 6px;
            background: #10B981;
            border-radius: 50%;
            box-shadow: 0 0 8px #10B981;
            animation: pulse-ring 1.8s infinite;
        }
        @keyframes pulse-ring { 0%,100%{opacity:1;transform:scale(1)} 50%{opacity:0.4;transform:scale(1.2)} }

        /* ── HTTPS NOTICE ── */
        .https-bar {
            display: none;
            background: linear-gradient(135deg, rgba(2, 132, 199, 0.2), rgba(15, 23, 42, 0.8));
            border: 1px solid rgba(56, 189, 248, 0.4);
            border-radius: var(--radius-md);
            padding: 10px 14px;
            font-size: 12px;
            display: flex; align-items: center; justify-content: space-between; gap: 10px;
        }
        .https-bar a {
            background: var(--blue-gradient);
            color: #FFF; text-decoration: none;
            padding: 6px 12px; border-radius: 8px;
            font-weight: 700; font-size: 11px; white-space: nowrap;
        }

        /* ── HERO NAVIGATION HUD SCREEN (TESLA / CARPLAY COCKPIT) ── */
        .hud-main {
            background: linear-gradient(165deg, rgba(14, 21, 38, 0.95), rgba(5, 8, 17, 0.98));
            border: 1.5px solid var(--border-cyan);
            border-radius: var(--radius-lg);
            padding: 16px;
            box-shadow: 0 12px 36px rgba(0, 0, 0, 0.7), 0 0 30px rgba(0, 240, 255, 0.1);
            position: relative;
            overflow: hidden;
            transition: all 0.3s ease;
        }
        .hud-main::before {
            content: '';
            position: absolute;
            top: 0; left: 10%; right: 10%; height: 1.5px;
            background: linear-gradient(90deg, transparent, var(--cyan), transparent);
        }

        /* Overspeed Screen Alarm */
        .hud-main.overspeed {
            border-color: var(--red);
            box-shadow: 0 0 35px rgba(239, 68, 68, 0.65), inset 0 0 20px rgba(239, 68, 68, 0.25);
            animation: overspeed-alarm 0.9s infinite alternate;
        }
        @keyframes overspeed-alarm {
            0% { border-color: rgba(239, 68, 68, 0.6); box-shadow: 0 0 20px rgba(239, 68, 68, 0.4); }
            100% { border-color: rgba(239, 68, 68, 1); box-shadow: 0 0 45px rgba(239, 68, 68, 0.85); }
        }

        /* Road Tag */
        .hud-road-tag {
            display: flex; align-items: center; justify-content: space-between;
            background: rgba(0, 240, 255, 0.06);
            border: 1px solid rgba(0, 240, 255, 0.22);
            border-radius: var(--radius-sm);
            padding: 8px 12px;
            font-size: 13px; font-weight: 700;
            color: var(--cyan);
            margin-bottom: 12px;
        }
        .hud-road-left { display: flex; align-items: center; gap: 8px; overflow: hidden; }
        .hud-road-left span.name { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 280px; }
        .hud-nav-mode-tag {
            font-size: 10px; font-weight: 800;
            background: rgba(0, 240, 255, 0.18);
            color: var(--cyan);
            padding: 2px 8px; border-radius: 12px;
            text-transform: uppercase;
        }

        /* Cockpit Body: Maneuver Card | Speedometer Gauge */
        .hud-body { display: grid; grid-template-columns: 1.15fr 0.85fr; gap: 12px; margin-bottom: 12px; }

        .maneuver-box {
            background: rgba(20, 29, 49, 0.6);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-md);
            padding: 12px;
            display: flex; flex-direction: column; justify-content: space-between;
            min-height: 126px;
            position: relative;
        }
        .maneuver-top { display: flex; align-items: center; gap: 10px; }
        .turn-icon-wrap {
            width: 52px; height: 52px;
            background: rgba(0, 240, 255, 0.12);
            border: 1.5px solid var(--cyan);
            border-radius: 14px;
            display: flex; align-items: center; justify-content: center;
            font-size: 28px; color: var(--cyan);
            box-shadow: 0 0 20px var(--cyan-glow);
            flex-shrink: 0;
            transition: all 0.2s;
        }
        .turn-icon-wrap.near-turn {
            border-color: var(--green);
            color: var(--green);
            box-shadow: 0 0 22px var(--green-glow);
            animation: turn-pulse 0.8s infinite alternate;
        }
        @keyframes turn-pulse { 0%{transform:scale(1);} 100%{transform:scale(1.08);} }

        .turn-dist-text { font-size: 24px; font-weight: 900; color: #FFF; letter-spacing: -0.5px; }
        .turn-dist-text.near-turn { color: #6EE7B7; text-shadow: 0 0 12px var(--green-glow); }
        .turn-inst-text {
            font-size: 12px; font-weight: 600;
            color: var(--text-muted); line-height: 1.4;
            margin-top: 6px;
            display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden;
        }

        /* Distance Progress Bar */
        .turn-progress-wrap {
            width: 100%; height: 5px;
            background: rgba(255, 255, 255, 0.08);
            border-radius: 4px; overflow: hidden;
            margin-top: 8px;
        }
        .turn-progress-bar {
            height: 100%; width: 100%;
            background: linear-gradient(90deg, #00F0FF, #10B981);
            border-radius: 4px;
            transition: width 0.3s ease, background 0.3s ease;
        }

        /* Circular Speedometer Arc Gauge */
        .speed-box {
            background: rgba(20, 29, 49, 0.6);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-md);
            padding: 8px 6px;
            display: flex; flex-direction: column; align-items: center; justify-content: center;
            position: relative;
            min-height: 126px;
            overflow: hidden;
        }
        .speed-arc-wrap {
            position: relative;
            width: 120px; height: 110px;
            display: flex; align-items: center; justify-content: center;
        }
        .speed-arc-svg {
            position: absolute; top: 0; left: 0;
            width: 120px; height: 120px;
            transform: rotate(-10deg);
        }
        .arc-track {
            fill: none;
            stroke: rgba(255, 255, 255, 0.08);
            stroke-width: 9;
            stroke-linecap: round;
        }
        .arc-active {
            fill: none;
            stroke: url(#speed-grad);
            stroke-width: 9;
            stroke-linecap: round;
            transition: stroke-dashoffset 0.25s cubic-bezier(0.4, 0, 0.2, 1), stroke 0.3s;
        }
        .speed-text-inner {
            display: flex; flex-direction: column; align-items: center; justify-content: center;
            margin-top: 10px; z-index: 2;
        }
        .speed-val {
            font-family: 'Rajdhani', sans-serif;
            font-size: 46px; font-weight: 800; line-height: 0.95;
            color: #FFF; letter-spacing: -1px;
            text-shadow: 0 0 16px var(--cyan-glow);
            transition: color 0.2s;
        }
        .speed-box.overspeed .speed-val {
            color: var(--red);
            text-shadow: 0 0 20px var(--red-glow);
        }
        .speed-unit { font-size: 11px; font-weight: 700; color: var(--text-muted); margin-top: 2px; }

        /* Speed Limit Sign Badge */
        .limit-badge {
            position: absolute; top: 6px; right: 6px;
            width: 32px; height: 32px;
            background: #FFF;
            border: 3.5px solid #DC2626;
            border-radius: 50%;
            display: flex; align-items: center; justify-content: center;
            font-size: 12px; font-weight: 900; color: #111;
            box-shadow: 0 2px 8px rgba(0,0,0,0.5);
            z-index: 5;
            transition: all 0.2s;
        }
        .speed-box.overspeed .limit-badge {
            transform: scale(1.15);
            box-shadow: 0 0 14px var(--red-glow);
            animation: sign-overspeed 0.6s infinite alternate;
        }
        @keyframes sign-overspeed { 0%{transform:scale(1.05);} 100%{transform:scale(1.2);} }

        /* Bottom stats bar */
        .hud-footer {
            display: flex; justify-content: space-between; align-items: center;
            background: rgba(0,0,0,0.35);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-sm);
            padding: 8px 12px;
            font-size: 11px; font-weight: 600; color: var(--text-muted);
        }
        .hud-footer .eta { color: var(--cyan); font-weight: 700; }

        /* ── INTERACTIVE MAP SECTION (CARPLAY DARK THEME) ── */
        .map-card {
            background: var(--bg-card);
            backdrop-filter: blur(16px);
            -webkit-backdrop-filter: blur(16px);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-lg);
            padding: 14px;
            display: flex; flex-direction: column; gap: 10px;
        }

        /* Floating Search */
        .search-bar { display: flex; gap: 8px; }
        .search-input-wrap { position: relative; flex: 1; }
        .search-input-wrap input {
            width: 100%; height: 42px;
            background: rgba(15, 23, 42, 0.85);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-sm);
            padding: 0 14px 0 38px;
            color: #FFF; font-size: 13px; font-family: inherit;
            outline: none; transition: all 0.2s;
        }
        .search-input-wrap input:focus {
            border-color: var(--cyan);
            box-shadow: 0 0 12px var(--cyan-glow);
        }
        .search-icon-inside {
            position: absolute; left: 12px; top: 50%; transform: translateY(-50%);
            color: var(--text-muted); font-size: 14px; pointer-events: none;
        }
        .btn-search-action {
            height: 42px; padding: 0 16px;
            background: var(--blue-gradient);
            border: none; border-radius: var(--radius-sm);
            color: #FFF; font-size: 13px; font-weight: 700;
            cursor: pointer; display: flex; align-items: center; gap: 4px;
            box-shadow: 0 4px 12px rgba(37, 99, 235, 0.3);
        }
        .btn-gps-locate {
            height: 42px; width: 42px;
            background: rgba(30, 41, 59, 0.8);
            border: 1px solid rgba(56, 189, 248, 0.3);
            border-radius: var(--radius-sm);
            color: #38BDF8; font-size: 16px;
            cursor: pointer; display: flex; align-items: center; justify-content: center;
        }

        /* ── LIVE AUTOCOMPLETE SEARCH DROPDOWN ── */
        .search-dropdown {
            position: absolute;
            top: calc(100% + 6px);
            left: 0;
            right: 0;
            background: rgba(11, 19, 43, 0.98);
            backdrop-filter: blur(16px);
            border: 1px solid rgba(0, 240, 255, 0.4);
            border-radius: 14px;
            box-shadow: 0 14px 40px rgba(0, 0, 0, 0.85), 0 0 15px rgba(0, 240, 255, 0.25);
            max-height: 280px;
            overflow-y: auto;
            z-index: 10000;
            padding: 6px;
        }
        .search-dropdown-item {
            display: flex;
            align-items: center;
            gap: 10px;
            padding: 10px 12px;
            border-radius: 10px;
            cursor: pointer;
            transition: all 0.15s ease;
            border-bottom: 1px solid rgba(255, 255, 255, 0.05);
        }
        .search-dropdown-item:last-child { border-bottom: none; }
        .search-dropdown-item:hover, .search-dropdown-item:active {
            background: rgba(14, 165, 233, 0.25);
            border-color: rgba(56, 189, 248, 0.4);
        }
        .dropdown-item-icon {
            font-size: 18px;
            width: 32px;
            height: 32px;
            border-radius: 8px;
            background: rgba(255, 255, 255, 0.08);
            display: flex;
            align-items: center;
            justify-content: center;
            flex-shrink: 0;
        }
        .dropdown-item-info {
            display: flex;
            flex-direction: column;
            min-width: 0;
            flex: 1;
        }
        .dropdown-item-title {
            font-size: 13px;
            font-weight: 700;
            color: #F8FAFC;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
        }
        .dropdown-item-sub {
            font-size: 11px;
            color: #94A3B8;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
            margin-top: 2px;
        }
        .dropdown-loading {
            padding: 12px;
            text-align: center;
            font-size: 12px;
            color: #38BDF8;
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 8px;
        }

        /* ── RECENT PLACES HISTORY BAR ── */
        .recent-places-wrap {
            margin-top: 8px;
            display: flex;
            flex-direction: column;
            gap: 6px;
        }
        .recent-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 0 4px;
        }
        .recent-title {
            font-size: 11px;
            font-weight: 700;
            color: #94A3B8;
            text-transform: uppercase;
            letter-spacing: 0.5px;
        }
        .btn-clear-recent {
            background: none;
            border: none;
            color: #F87171;
            font-size: 11px;
            cursor: pointer;
            font-weight: 600;
            padding: 2px 6px;
            border-radius: 4px;
            transition: background 0.2s;
        }
        .btn-clear-recent:hover {
            background: rgba(239, 68, 68, 0.15);
        }
        .recent-chips {
            display: flex;
            gap: 6px;
            overflow-x: auto;
            padding-bottom: 4px;
            scrollbar-width: none;
        }
        .recent-chips::-webkit-scrollbar { display: none; }
        .recent-chip {
            background: rgba(30, 41, 59, 0.7);
            border: 1px solid rgba(255, 255, 255, 0.12);
            color: #E2E8F0;
            padding: 5px 10px;
            border-radius: 14px;
            font-size: 11px;
            font-weight: 600;
            white-space: nowrap;
            cursor: pointer;
            display: flex;
            align-items: center;
            gap: 5px;
            transition: all 0.2s;
        }
        .recent-chip:hover {
            background: rgba(14, 165, 233, 0.3);
            border-color: #38BDF8;
            color: #38BDF8;
            transform: translateY(-1px);
        }

        /* City Quick Pills */
        .city-chips {
            display: flex; gap: 6px; overflow-x: auto; scrollbar-width: none;
            padding-bottom: 2px; -webkit-overflow-scrolling: touch;
        }
        .city-chips::-webkit-scrollbar { display: none; }
        .chip {
            padding: 6px 12px;
            background: rgba(30, 41, 59, 0.6);
            border: 1px solid var(--border-glass);
            border-radius: 20px;
            font-size: 11px; font-weight: 700; color: var(--text-muted);
            white-space: nowrap; cursor: pointer; transition: all 0.2s;
        }
        .chip:hover, .chip:active { background: var(--blue); color: #FFF; border-color: var(--cyan); }

        /* Leaflet Map */
        #map {
            height: 310px; width: 100%;
            border-radius: var(--radius-md);
            border: 1px solid var(--border-glass);
            z-index: 1;
            background: #0B111E;
        }
        /* CarPlay Dark Inversion Filter: 100% Free, NO API Key, No Watermark */
        #map .leaflet-tile-pane {
            filter: invert(100%) hue-rotate(180deg) brightness(88%) contrast(96%);
        }

        .map-hint { font-size: 11px; color: var(--text-muted); text-align: center; line-height: 1.4; }

        /* Destination bar */
        .dest-summary {
            background: rgba(0, 0, 0, 0.35);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-sm);
            padding: 10px 12px;
            display: flex; justify-content: space-between; align-items: center; gap: 10px;
        }
        .dest-summary .label { font-size: 10px; text-transform: uppercase; color: var(--text-muted); font-weight: 700; }
        .dest-summary .place { font-size: 13px; font-weight: 700; color: var(--cyan); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 260px; }

        /* ── ACTION BUTTONS ── */
        .btn-send-mochi {
            width: 100%; padding: 14px;
            background: linear-gradient(135deg, #10B981, #059669);
            border: none; border-radius: var(--radius-md);
            color: #FFF; font-size: 14px; font-weight: 800;
            cursor: pointer; display: flex; align-items: center; justify-content: center; gap: 8px;
            box-shadow: 0 6px 20px rgba(16, 185, 129, 0.35);
            transition: all 0.2s;
        }
        .btn-send-mochi:active { transform: scale(0.98); }

        /* ── DUAL AUTOMATIC MODES ── */
        .auto-modes-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; }
        .btn-mode-auto {
            padding: 12px 10px;
            background: rgba(20, 29, 49, 0.7);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-sm);
            color: #FFF; font-size: 12px; font-weight: 700; font-family: inherit;
            cursor: pointer; display: flex; flex-direction: column; align-items: center; gap: 4px;
            text-align: center; transition: all 0.2s;
        }
        .btn-mode-auto span.title { font-weight: 800; font-size: 12px; }
        .btn-mode-auto span.desc { font-size: 10px; color: var(--text-muted); font-weight: 500; }

        .btn-mode-auto.active-gps {
            background: linear-gradient(135deg, #059669, #10B981);
            border-color: #34D399;
            box-shadow: 0 4px 16px rgba(16, 185, 129, 0.35);
        }
        .btn-mode-auto.active-sim {
            background: linear-gradient(135deg, #DC2626, #EF4444);
            border-color: #F87171;
            box-shadow: 0 4px 16px rgba(239, 68, 68, 0.35);
        }

        /* ── SIMULATION CONTROLLER BAR ── */
        .sim-controls-bar {
            display: flex;
            align-items: center;
            justify-content: space-between;
            background: rgba(15, 23, 42, 0.95);
            border: 1px solid rgba(239, 68, 68, 0.5);
            border-radius: var(--radius-sm);
            padding: 8px 12px;
            margin-top: 6px;
            gap: 8px;
            box-shadow: 0 4px 16px rgba(0, 0, 0, 0.6);
            animation: slide-up 0.2s ease-out;
        }
        .sim-status-chip {
            font-size: 11px;
            font-weight: 800;
            color: #F87171;
            display: flex;
            align-items: center;
            gap: 6px;
        }
        .sim-btns-group {
            display: flex;
            gap: 6px;
        }
        .btn-sim-ctrl {
            background: rgba(30, 41, 59, 0.85);
            border: 1px solid rgba(255, 255, 255, 0.15);
            color: #F8FAFC;
            font-size: 11px;
            font-weight: 700;
            padding: 5px 10px;
            border-radius: 8px;
            cursor: pointer;
            transition: all 0.15s;
        }
        .btn-sim-ctrl:hover {
            background: rgba(14, 165, 233, 0.3);
            border-color: #38BDF8;
            color: #38BDF8;
        }
        .btn-sim-ctrl.btn-sim-stop {
            background: rgba(239, 68, 68, 0.2);
            border-color: #EF4444;
            color: #F87171;
        }
        .btn-sim-ctrl.btn-sim-stop:hover {
            background: #EF4444;
            color: #FFF;
        }

        /* ── DYNAMIC MAP ZOOM LOD (CHỐNG RỐI BẢN ĐỒ KHI THU NHỎ) ── */
        .map-zoom-out .custom-sig { display: none !important; }
        .map-zoom-out .poi-marker-camera { display: none !important; }
        .map-zoom-out .poi-marker-fuel { display: none !important; }
        .map-zoom-out .poi-marker-toll { transform: scale(0.8); }

        /* ── COLLAPSIBLE TEST & CONTROLS ── */
        .details-panel {
            background: var(--bg-card);
            border: 1px solid var(--border-glass);
            border-radius: var(--radius-md);
            overflow: hidden;
        }
        .details-summary {
            padding: 12px 16px;
            font-size: 12px; font-weight: 700; color: var(--text-muted);
            cursor: pointer; user-select: none;
            display: flex; justify-content: space-between; align-items: center;
        }
        .details-content { padding: 0 14px 14px; display: flex; flex-direction: column; gap: 10px; border-top: 1px solid var(--border-glass); margin-top: 4px; padding-top: 12px; }

        /* ── GOOGLE DIRECTIONS & ROADS LIST ── */
        .directions-list {
            display: flex;
            flex-direction: column;
            gap: 6px;
            max-height: 290px;
            overflow-y: auto;
            padding-right: 4px;
        }
        .directions-list::-webkit-scrollbar { width: 4px; }
        .directions-list::-webkit-scrollbar-track { background: rgba(0,0,0,0.2); border-radius: 4px; }
        .directions-list::-webkit-scrollbar-thumb { background: rgba(56, 189, 248, 0.4); border-radius: 4px; }

        .dir-step-item {
            display: flex;
            align-items: center;
            gap: 10px;
            padding: 9px 12px;
            background: rgba(15, 23, 42, 0.65);
            border: 1px solid rgba(255, 255, 255, 0.08);
            border-radius: 10px;
            cursor: pointer;
            transition: all 0.2s ease;
            position: relative;
        }
        .dir-step-item:hover {
            background: rgba(30, 41, 59, 0.85);
            border-color: rgba(56, 189, 248, 0.4);
            transform: translateX(2px);
        }
        .dir-step-item.active-step {
            background: linear-gradient(90deg, rgba(2, 132, 199, 0.35), rgba(15, 23, 42, 0.9));
            border: 1.5px solid #38BDF8;
            box-shadow: 0 0 16px rgba(56, 189, 248, 0.25);
        }
        .dir-step-item.active-step::before {
            content: '';
            position: absolute;
            left: 0; top: 0; bottom: 0;
            width: 4px;
            background: #00F0FF;
            border-top-left-radius: 10px;
            border-bottom-left-radius: 10px;
        }
        .dir-step-num {
            font-size: 10px;
            font-weight: 800;
            color: var(--text-muted);
            min-width: 16px;
            text-align: center;
        }
        .dir-step-item.active-step .dir-step-num {
            color: #00F0FF;
        }
        .dir-step-icon {
            font-size: 18px;
            min-width: 28px;
            height: 28px;
            border-radius: 50%;
            background: rgba(255, 255, 255, 0.06);
            display: flex;
            align-items: center;
            justify-content: center;
            color: #F8FAFC;
        }
        .dir-step-item.active-step .dir-step-icon {
            background: rgba(56, 189, 248, 0.2);
            color: #38BDF8;
        }
        .dir-step-info {
            flex: 1;
            min-width: 0;
        }
        .dir-step-road {
            font-size: 12px;
            font-weight: 700;
            color: #F1F5F9;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
        }
        .dir-step-item.active-step .dir-step-road {
            color: #FFFFFF;
            font-weight: 800;
        }
        .dir-step-sub {
            font-size: 10px;
            font-weight: 500;
            color: var(--text-muted);
            margin-top: 1px;
        }
        .dir-step-dist {
            font-size: 12px;
            font-weight: 800;
            color: #38BDF8;
            font-family: 'Rajdhani', sans-serif;
            letter-spacing: -0.3px;
            white-space: nowrap;
        }
        .dir-step-item.active-step .dir-step-dist {
            color: #00F0FF;
            font-size: 13px;
        }
        .empty-directions {
            text-align: center;
            padding: 18px 12px;
            font-size: 11px;
            color: var(--text-muted);
            font-style: italic;
        }

        /* ── MAP ELEMENTS LAYER FILTER BAR ── */
        .map-elements-bar {
            display: flex;
            gap: 6px;
            overflow-x: auto;
            padding: 4px 0 6px;
            margin-bottom: 4px;
            scrollbar-width: none;
        }
        .map-elements-bar::-webkit-scrollbar { display: none; }
        .layer-pill {
            display: flex;
            align-items: center;
            gap: 5px;
            padding: 5px 10px;
            background: rgba(15, 23, 42, 0.7);
            border: 1px solid rgba(255, 255, 255, 0.1);
            border-radius: 20px;
            color: var(--text-muted);
            font-size: 11px;
            font-weight: 700;
            cursor: pointer;
            white-space: nowrap;
            transition: all 0.2s ease;
            user-select: none;
        }
        .layer-pill:hover {
            border-color: rgba(56, 189, 248, 0.5);
            color: #FFFFFF;
        }
        .layer-pill.active {
            background: rgba(30, 41, 59, 0.95);
            border-color: #38BDF8;
            color: #FFFFFF;
            box-shadow: 0 0 10px rgba(56, 189, 248, 0.25);
        }
        .pill-dot {
            width: 7px;
            height: 7px;
            border-radius: 50%;
            display: inline-block;
        }

        /* Custom POI Markers on Leaflet Map */
        .poi-marker-traffic {
            background: #0B0F19;
            border: 1.5px solid #38BDF8;
            border-radius: 8px;
            padding: 3px 4px;
            box-shadow: 0 4px 12px rgba(0,0,0,0.85), 0 0 10px rgba(56, 189, 248, 0.4);
            display: flex;
            flex-direction: column;
            gap: 2.5px;
            align-items: center;
            cursor: pointer;
        }
        .poi-marker-traffic .p-light {
            width: 7px; height: 7px; border-radius: 50%; opacity: 0.25;
        }
        .poi-marker-traffic .p-light.red { background: #EF4444; }
        .poi-marker-traffic .p-light.yellow { background: #F59E0B; }
        .poi-marker-traffic .p-light.green { background: #10B981; }
        .poi-marker-traffic .p-light.active {
            opacity: 1;
            box-shadow: 0 0 8px currentColor;
        }

        .poi-marker-camera {
            background: rgba(15, 23, 42, 0.95);
            border: 2px solid #EF4444;
            border-radius: 14px;
            padding: 2px 6px;
            display: flex;
            align-items: center;
            gap: 4px;
            box-shadow: 0 4px 14px rgba(239, 68, 68, 0.5);
            white-space: nowrap;
            cursor: pointer;
        }
        .poi-marker-camera .cam-spd {
            font-size: 11px; font-weight: 900; color: #FFFFFF;
            background: #EF4444; border-radius: 6px; padding: 0 4px; line-height: 1.2;
        }

        .poi-marker-toll {
            background: rgba(30, 41, 59, 0.95);
            border: 1.5px solid #F59E0B;
            border-radius: 10px;
            padding: 2px 6px;
            display: flex;
            align-items: center;
            gap: 3px;
            box-shadow: 0 4px 12px rgba(245, 158, 11, 0.4);
            font-size: 10px; font-weight: 800; color: #F59E0B;
            cursor: pointer;
        }

        .poi-marker-fuel {
            background: #064E3B;
            border: 1.5px solid #10B981;
            border-radius: 50%;
            width: 24px; height: 24px;
            display: flex; align-items: center; justify-content: center;
            box-shadow: 0 4px 10px rgba(16, 185, 129, 0.4);
            font-size: 13px;
            cursor: pointer;
        }

        /* Proximity Alert Banner */
        .hud-alert-banner {
            background: linear-gradient(135deg, rgba(239, 68, 68, 0.95), rgba(185, 28, 28, 0.95));
            border: 1.5px solid #FCA5A5;
            border-radius: 12px;
            padding: 8px 14px;
            display: none;
            align-items: center;
            justify-content: space-between;
            margin-bottom: 8px;
            box-shadow: 0 8px 24px rgba(239, 68, 68, 0.6);
            animation: pulse-alert 0.8s infinite alternate;
        }
        @keyframes pulse-alert {
            from { transform: scale(0.99); opacity: 0.92; }
            to { transform: scale(1.01); opacity: 1; }
        }
        .hud-alert-banner .alert-text {
            font-size: 12px; font-weight: 800; color: #FFFFFF;
            display: flex; align-items: center; gap: 8px;
        }
        .hud-alert-banner .alert-dist {
            font-size: 14px; font-weight: 900; color: #FEF08A;
            font-family: 'Rajdhani', sans-serif;
        }

        .preset-row { display: grid; grid-template-columns: repeat(3, 1fr); gap: 6px; }
        .btn-preset-small {
            padding: 8px 6px;
            background: rgba(30, 41, 59, 0.6);
            border: 1px solid var(--border-glass);
            border-radius: 8px;
            color: #FFF; font-size: 11px; font-weight: 700; cursor: pointer; text-align: center;
        }

        .speed-slider-wrap { display: flex; align-items: center; gap: 10px; margin-top: 4px; }
        .speed-slider-wrap input[type=range] { flex: 1; accent-color: var(--cyan); }
        .speed-pill-display { font-size: 13px; font-weight: 800; color: var(--cyan); min-width: 60px; text-align: right; }

        .speed-limit-row { display: flex; gap: 6px; }
        .btn-lim {
            flex: 1; padding: 7px 0;
            background: rgba(30, 41, 59, 0.6);
            border: 1px solid var(--border-glass);
            border-radius: 8px; color: #FFF; font-weight: 800; font-size: 12px; cursor: pointer;
        }
        .btn-lim.active { background: #DC2626; border-color: #EF4444; }

        .toast-msg {
            position: fixed; bottom: 20px; left: 50%; transform: translateX(-50%);
            background: rgba(16, 185, 129, 0.95);
            border: 1px solid #34D399;
            color: #FFF; padding: 10px 20px;
            border-radius: 30px; font-size: 13px; font-weight: 700;
            box-shadow: 0 10px 25px rgba(0,0,0,0.5);
            display: none; z-index: 99999;
            animation: slide-up 0.25s ease-out;
        }
        @keyframes slide-up { from { opacity: 0; transform: translate(-50%, 15px); } to { opacity: 1; transform: translate(-50%, 0); } }

        /* ── HUD MIRROR MODE (PHẢN CHIẾU KÍNH LÁI XE HƠI) ── */
        body.hud-mirror-mode {
            background: #000000 !important;
            padding: 0 !important;
            margin: 0 !important;
            display: flex;
            align-items: center;
            justify-content: center;
            min-height: 100vh;
            overflow: hidden;
        }
        body.hud-mirror-mode .top-nav,
        body.hud-mirror-mode .https-bar,
        body.hud-mirror-mode .map-card,
        body.hud-mirror-mode .auto-modes-grid,
        body.hud-mirror-mode .btn-send-mochi,
        body.hud-mirror-mode .details-panel,
        body.hud-mirror-mode .toast-msg {
            display: none !important;
        }
        body.hud-mirror-mode .app-container {
            max-width: 100vw;
            width: 100%;
            height: 100vh;
            display: flex;
            flex-direction: column;
            justify-content: center;
            align-items: center;
            transform: scaleX(-1); /* Lật gương ngang phản chiếu kính lái */
            padding: 16px;
        }
        body.hud-mirror-mode .hud-main {
            width: 100%;
            max-width: 540px;
            background: #000000;
            border: 2px solid rgba(0, 240, 255, 0.7);
            box-shadow: 0 0 60px rgba(0, 240, 255, 0.35);
            border-radius: 26px;
            padding: 24px 20px;
        }
        body.hud-mirror-mode .hud-road-tag { font-size: 16px; padding: 12px 16px; }
        body.hud-mirror-mode .turn-icon-wrap { width: 68px; height: 68px; font-size: 38px; }
        body.hud-mirror-mode .turn-dist-text { font-size: 34px; }
        body.hud-mirror-mode .turn-inst-text { font-size: 15px; }
        body.hud-mirror-mode .speed-val { font-size: 60px; }
        body.hud-mirror-mode .speed-arc-wrap { width: 140px; height: 130px; }
        body.hud-mirror-mode .speed-arc-svg { width: 140px; height: 140px; }

        .btn-exit-hud {
            display: none;
            position: fixed; top: 16px; left: 16px;
            background: rgba(239, 68, 68, 0.85);
            border: 1px solid #F87171;
            color: #FFF; font-size: 12px; font-weight: 800;
            padding: 8px 14px; border-radius: 20px;
            cursor: pointer; z-index: 999999;
            box-shadow: 0 4px 16px rgba(0,0,0,0.6);
            transform: scaleX(-1); /* Un-mirror so text is readable */
        }
        body.hud-mirror-mode .btn-exit-hud { display: block !important; }

        /* ── HUD VIEW SWITCHER TABS ── */
        .hud-view-switcher {
            display: flex; gap: 8px; justify-content: center; margin-bottom: 2px;
        }
        .btn-hud-tab {
            padding: 6px 14px;
            background: rgba(30, 41, 59, 0.6);
            border: 1px solid var(--border-glass);
            border-radius: 20px;
            color: var(--text-muted); font-size: 11px; font-weight: 800;
            cursor: pointer; transition: all 0.2s;
        }
        .btn-hud-tab.active {
            background: linear-gradient(135deg, #0284C7, #00F0FF);
            border-color: #38BDF8;
            color: #040711;
            box-shadow: 0 0 14px var(--cyan-glow);
        }

        /* ── VIETMAP PRO 3-COLUMN COCKPIT HUD ── */
        .vietmap-hud-container {
            background: #000000;
            border: 2px solid rgba(255, 255, 255, 0.15);
            border-radius: 18px;
            padding: 14px 10px;
            display: grid;
            grid-template-columns: 0.95fr 1.35fr 0.85fr;
            gap: 8px;
            box-shadow: 0 14px 40px rgba(0, 0, 0, 0.8), inset 0 0 30px rgba(0, 0, 0, 0.95);
            position: relative;
            overflow: hidden;
            user-select: none;
            transition: all 0.3s ease;
        }
        .vietmap-hud-container.overspeed {
            border-color: #EF4444;
            box-shadow: 0 0 35px rgba(239, 68, 68, 0.8), inset 0 0 25px rgba(239, 68, 68, 0.3);
            animation: overspeed-flash 0.8s infinite alternate;
        }
        @keyframes overspeed-flash {
            from { border-color: rgba(239, 68, 68, 0.6); }
            to { border-color: rgba(239, 68, 68, 1); }
        }

        .vm-col {
            display: flex;
            flex-direction: column;
            justify-content: space-between;
            position: relative;
        }
        .vm-col:not(:first-child) {
            border-left: 1px solid rgba(255, 255, 255, 0.08);
            padding-left: 8px;
        }

        /* Col 1: Speed */
        .vm-col-speed {
            align-items: center;
            justify-content: space-around;
            padding: 4px 0;
        }
        .vm-limit-sign {
            width: 64px; height: 64px;
            background: #FFFFFF;
            border: 6.5px solid #EF4444;
            border-radius: 50%;
            display: flex; align-items: center; justify-content: center;
            box-shadow: 0 4px 14px rgba(0, 0, 0, 0.6);
            flex-shrink: 0;
        }
        .vm-limit-sign span {
            font-family: 'Plus Jakarta Sans', sans-serif;
            font-size: 28px; font-weight: 900; color: #000000;
            line-height: 1;
        }
        .vm-speed-display {
            display: flex; flex-direction: column; align-items: center; justify-content: center;
            margin-top: 6px;
        }
        .vm-speed-val {
            font-family: 'Rajdhani', sans-serif;
            font-size: 60px; font-weight: 800; line-height: 0.9;
            color: #FFFFFF;
            letter-spacing: -1.5px;
        }
        .vietmap-hud-container.overspeed .vm-speed-val {
            color: #EF4444;
            text-shadow: 0 0 16px rgba(239, 68, 68, 0.7);
        }
        .vm-speed-unit {
            font-size: 11px; font-weight: 700; color: var(--text-muted);
            margin-top: 2px;
        }

        /* Col 2: Navigation & 3D Lane Guidance */
        .vm-col-nav {
            display: flex; flex-direction: column; align-items: center; justify-content: space-between;
            text-align: center;
            padding: 2px 4px;
        }
        .vm-nav-top {
            display: flex; flex-direction: column; align-items: center; width: 100%;
        }
        .vm-turn-arrow {
            font-size: 36px; line-height: 1; color: #FFFFFF;
            font-weight: 900;
            filter: drop-shadow(0 0 10px rgba(255, 255, 255, 0.6));
        }
        .vm-dist-val {
            font-size: 21px; font-weight: 900; color: #FFFFFF;
            margin-top: 2px; letter-spacing: -0.5px;
        }
        .vm-eta-val {
            font-size: 10px; font-weight: 700; color: #94A3B8;
            margin-top: 1px; letter-spacing: 0.3px;
        }
        .vm-road-name {
            font-size: 13px; font-weight: 800; color: #F8FAFC;
            margin-top: 4px;
            white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 175px;
        }

        /* 3D Lane Guidance */
        .vm-lane-guidance {
            position: relative; width: 100%; height: 58px;
            margin-top: 6px;
            display: flex; justify-content: center; align-items: flex-end;
        }
        .vm-lane-svg {
            position: absolute; top: 0; left: 0;
            width: 100%; height: 100%;
            pointer-events: none;
        }
        .vm-lane-arrows {
            position: relative; z-index: 2;
            display: flex; justify-content: space-around;
            width: 80%;
            margin-bottom: 4px;
        }
        .vm-lane-arrow {
            font-size: 22px; font-weight: 900; color: #FFFFFF;
            line-height: 1;
            opacity: 0.8;
            transition: all 0.25s;
        }
        .vm-lane-arrow.active {
            color: #38BDF8;
            filter: drop-shadow(0 0 10px #00F0FF);
            opacity: 1;
            transform: scale(1.2);
        }

        /* Col 3: Traffic Light & Telemetry */
        .vm-col-stats {
            display: flex; flex-direction: column; gap: 8px;
            justify-content: space-between;
        }
        .vm-card-traffic {
            background: rgba(15, 23, 42, 0.65);
            border: 1px solid rgba(255, 255, 255, 0.1);
            border-radius: 10px;
            padding: 6px 8px;
            display: flex; flex-direction: column; align-items: center; gap: 4px;
        }
        .vm-traffic-light {
            display: flex; flex-direction: column; gap: 3.5px;
            background: #0B0F19;
            padding: 4px 6px; border-radius: 8px;
            border: 1px solid rgba(255, 255, 255, 0.15);
        }
        .vm-light {
            width: 9px; height: 9px; border-radius: 50%;
            opacity: 0.25;
        }
        .vm-light.light-red { background: #EF4444; }
        .vm-light.light-yellow { background: #F59E0B; }
        .vm-light.light-green { background: #10B981; }
        .vm-light.active {
            opacity: 1;
            box-shadow: 0 0 10px currentColor;
        }

        .vm-traffic-dist {
            font-size: 13px; font-weight: 900; color: #FFFFFF;
        }

        /* Telemetry Box */
        .vm-card-telemetry {
            background: rgba(15, 23, 42, 0.65);
            border: 1px solid rgba(255, 255, 255, 0.1);
            border-radius: 10px;
            padding: 6px 8px;
            display: flex; flex-direction: column; gap: 4px;
        }
        .vm-tele-row {
            display: flex; align-items: center; justify-content: space-between;
            font-size: 11px; font-weight: 800; color: #F1F5F9;
        }
        .vm-tele-icon { font-size: 11px; }

        /* HUD Mirror mode styling for Vietmap */
        body.hud-mirror-mode .vietmap-hud-container {
            width: 100%;
            max-width: 540px;
            border: 2px solid rgba(0, 240, 255, 0.7);
            box-shadow: 0 0 60px rgba(0, 240, 255, 0.35);
            border-radius: 26px;
            padding: 24px 20px;
        }
        body.hud-mirror-mode .hud-view-switcher { display: none !important; }
    </style>
</head>
<body>
    <button id="btn-exit-hud" class="btn-exit-hud" onclick="toggleHudMirrorMode()">✕ Thoát Chiếu Kính</button>

    <div class="app-container">

        <!-- HEADER -->
        <header class="top-nav">
            <div class="brand">
                <div class="brand-icon">🚗</div>
                <div>
                    <div>Mochi HUD</div>
                    <div style="font-size: 9px; color: var(--cyan); font-weight: 700; letter-spacing: 0.5px;">TESLA COCKPIT v2.0</div>
                </div>
            </div>
            <div class="header-actions">
                <button id="btn-sound-toggle" class="btn-header-tool" onclick="toggleSound()" title="Bật/Tắt âm thanh cảnh báo tốc độ">
                    🔊 <span id="lbl-sound">Âm báo</span>
                </button>
                <button id="btn-hud-mirror" class="btn-header-tool" onclick="toggleHudMirrorMode()" title="Chế độ phản chiếu kính lái ban đêm">
                    🪞 <span>Kính Lái</span>
                </button>
                <div class="status-badge" id="conn-badge">
                    <div class="pulse-dot"></div>
                    <span id="conn-text">Sẵn sàng</span>
                </div>
            </div>
        </header>

        <!-- HTTPS Warning Banner -->
        <div class="https-bar" id="https-banner">
            <div>
                <strong>⚠️ Cần HTTPS để đọc GPS iPhone:</strong>
                <div style="font-size: 11px; color: #BAE6FD; margin-top: 2px;">iOS chặn đọc GPS khi mở HTTP. Chạm vào nút bên cạnh để chuyển sang cổng HTTPS 8443 nhé!</div>
            </div>
            <a id="https-link" href="#">Chuyển HTTPS (8443) ➔</a>
        </div>

        
        <!-- HUD VIEW SWITCHER TABS -->
        <div class="hud-view-switcher">
            <button id="tab-vietmap" class="btn-hud-tab active" onclick="switchHudStyle('vietmap')">🚗 Vietmap Pro</button>
            <button id="tab-tesla" class="btn-hud-tab" onclick="switchHudStyle('tesla')">⚡ Tesla Cockpit</button>
            <button id="tab-fullmap" class="btn-hud-tab" onclick="switchHudStyle('fullmap')">🗺️ Full Map</button>
            <span style="border-left: 1px solid rgba(255,255,255,0.2); margin: 0 4px;"></span>
            <button id="veh-car" class="btn-hud-tab active" onclick="switchVehicleMode('car')">🚗 Ô Tô</button>
            <button id="veh-bike" class="btn-hud-tab" onclick="switchVehicleMode('bike')">🛵 Xe Máy</button>
        </div>

        <!-- PROXIMITY ALERT BANNER (CAMERA PHẠT NGUỘI / ĐÈN ĐỎ) -->
        <div class="hud-alert-banner" id="hud-alert-banner">
            <div class="alert-text">
                <span id="alert-banner-icon" style="font-size: 20px;">📷</span>
                <span id="alert-banner-msg">Sắp đến Camera phạt nguội tốc độ (60 km/h)</span>
            </div>
            <div class="alert-dist" id="alert-banner-dist">180 M</div>
        </div>

        <!-- VIETMAP PRO 3-COLUMN COCKPIT HUD SCREEN -->
        <section class="vietmap-hud-container" id="vietmap-hud-screen">
            <!-- CỘT 1: TỐC ĐỘ & BIỂN BÁO -->
            <div class="vm-col vm-col-speed">
                <div class="vm-limit-sign" id="vm-limit-sign" title="Giới hạn tốc độ">
                    <span id="vm-limit-val">60</span>
                </div>
                <div class="vm-speed-display">
                    <div class="vm-speed-val" id="vm-speed-val">0</div>
                    <div class="vm-speed-unit">km/h</div>
                </div>
            </div>

            <!-- CỘT 2: ĐIỀU HƯỚNG & LÀN ĐƯỜNG 3D -->
            <div class="vm-col vm-col-nav">
                <div class="vm-nav-top">
                    <div class="vm-turn-arrow" id="vm-turn-arrow">↑</div>
                    <div class="vm-dist-val" id="vm-dist-val">-- m</div>
                    <div class="vm-eta-val" id="vm-eta-val">ETA --:--</div>
                    <div class="vm-road-name" id="vm-road-name">Đang chờ tuyến đường...</div>
                </div>
                <!-- 3D Perspective Lane Guidance -->
                <div class="vm-lane-guidance">
                    <svg class="vm-lane-svg" viewBox="0 0 160 56">
                        <line x1="16" y1="54" x2="62" y2="2" stroke="#38BDF8" stroke-width="2.5" />
                        <line x1="144" y1="54" x2="98" y2="2" stroke="#38BDF8" stroke-width="2.5" />
                        <line x1="58" y1="54" x2="74" y2="2" stroke="#FFFFFF" stroke-width="1.8" stroke-dasharray="5 3.5" opacity="0.65" />
                        <line x1="102" y1="54" x2="86" y2="2" stroke="#FFFFFF" stroke-width="1.8" stroke-dasharray="5 3.5" opacity="0.65" />
                    </svg>
                    <div class="vm-lane-arrows">
                        <div class="vm-lane-arrow" id="vm-lane-left">↰</div>
                        <div class="vm-lane-arrow active" id="vm-lane-mid">↑</div>
                        <div class="vm-lane-arrow" id="vm-lane-right">↱</div>
                    </div>
                </div>
            </div>

            <!-- CỘT 3: ĐÈN GIAO THÔNG & THÔNG SỐ XE -->
            <div class="vm-col vm-col-stats">
                <!-- Hộp Đèn Giao Thông -->
                <div class="vm-card-traffic">
                    <div class="vm-traffic-light">
                        <span class="vm-light light-red" id="vm-light-red"></span>
                        <span class="vm-light light-yellow" id="vm-light-yellow"></span>
                        <span class="vm-light light-green" id="vm-light-green"></span>
                    </div>
                    <div class="vm-traffic-dist" id="vm-traffic-dist">-- M</div>
                </div>
                <!-- Hộp Thông Số Xe (OBD2) -->
                <div class="vm-card-telemetry">
                    <div class="vm-tele-row">
                        <span class="vm-tele-icon" style="color: #F87171;">🔋</span>
                        <span class="vm-tele-val" id="vm-tele-batt">14.4 V</span>
                    </div>
                    <div class="vm-tele-row">
                        <span class="vm-tele-icon" style="color: #38BDF8;">🌡️</span>
                        <span class="vm-tele-val" id="vm-tele-temp">92 °C</span>
                    </div>
                    <div class="vm-tele-row">
                        <span class="vm-tele-icon" style="color: #FBBF24;">🕒</span>
                        <span class="vm-tele-val" id="vm-tele-time">07:32</span>
                    </div>
                </div>
            </div>
        </section>

        <!-- HERO NAVIGATION HUD SCREEN -->
        <section class="hud-main" id="hud-main-screen">
            <div class="hud-road-tag">
                <div class="hud-road-left">
                    <span style="font-size: 16px;">🛣️</span>
                    <span id="prev-road" class="name">Đang chờ chọn tuyến đường...</span>
                </div>
                <div class="hud-nav-mode-tag" id="nav-mode-badge">GPS HUD</div>
            </div>
            <div class="hud-body">
                <!-- Maneuver Left Card -->
                <div class="maneuver-box">
                    <div class="maneuver-top">
                        <div class="turn-icon-wrap" id="prev-arrow">↑</div>
                        <div>
                            <div class="turn-dist-text" id="prev-dist">-- m</div>
                            <div style="font-size: 10px; color: var(--text-muted); font-weight: 700;">ĐẾN ĐIỂM RẼ</div>
                        </div>
                    </div>
                    <div class="turn-inst-text" id="prev-inst">Chạm chọn điểm đến trên bản đồ bên dưới để bắt đầu lộ trình</div>
                    <div class="turn-progress-wrap">
                        <div class="turn-progress-bar" id="turn-progress-bar" style="width: 100%;"></div>
                    </div>
                </div>

                <!-- Speedometer Arc Gauge -->
                <div class="speed-box" id="prev-spd-card">
                    <div class="limit-badge" id="prev-limit-val" title="Giới hạn tốc độ">50</div>
                    <div class="speed-arc-wrap">
                        <svg class="speed-arc-svg" viewBox="0 0 140 140">
                            <defs>
                                <linearGradient id="speed-grad" x1="0%" y1="0%" x2="100%" y2="100%">
                                    <stop offset="0%" stop-color="#00F0FF" />
                                    <stop offset="70%" stop-color="#3B82F6" />
                                    <stop offset="100%" stop-color="#10B981" />
                                </linearGradient>
                            </defs>
                            <circle cx="70" cy="70" r="52" class="arc-track" stroke-dasharray="217.8 108.9" transform="rotate(150 70 70)" />
                            <circle cx="70" cy="70" r="52" id="speed-arc-active" class="arc-active" stroke-dasharray="217.8 108.9" stroke-dashoffset="217.8" transform="rotate(150 70 70)" />
                        </svg>
                        <div class="speed-text-inner">
                            <div class="speed-val" id="prev-spd-val">0</div>
                            <div class="speed-unit">km/h</div>
                        </div>
                    </div>
                </div>
            </div>
            <div class="hud-footer">
                <div class="eta" id="prev-eta">⏱ Dự kiến: --:--</div>
                <div class="desc" id="gps-status-txt">📡 GPS: Sẵn sàng</div>
            </div>
        </section>

        <!-- MAP SECTION (DARK THEME CARPLAY) -->
        <section class="map-card">
            <div class="search-bar">
                <div class="search-input-wrap">
                    <span class="search-icon-inside">🔍</span>
                    <input type="text" id="map-search-inp" placeholder="Tìm địa chỉ, toà nhà, điểm đến..." onkeydown="if(event.key==='Enter') searchLocation()" oninput="onSearchInput(this.value)" onfocus="onSearchFocus()" autocomplete="off">
                    <div id="search-dropdown" class="search-dropdown" style="display:none;"></div>
                </div>
                <button class="btn-search-action" onclick="searchLocation()">Tìm</button>
                <button class="btn-gps-locate" onclick="locateMe()" title="Định vị vị trí hiện tại">🎯</button>
            </div>

            <!-- RECENT PLACES HISTORY QUICK ACCESS -->
            <div class="recent-places-wrap" id="recent-places-wrap" style="display:none;">
                <div class="recent-header">
                    <span class="recent-title">🕒 Nơi đã từng đến:</span>
                    <button class="btn-clear-recent" onclick="clearRecentPlaces()" title="Xoá lịch sử">Xoá lịch sử</button>
                </div>
                <div class="recent-chips" id="recent-chips-bar"></div>
            </div>

            <div class="city-chips">
                <div class="chip" onclick="jumpToCity('hcm')">📍 TP.HCM</div>
                <div class="chip" onclick="jumpToCity('hn')">📍 Hà Nội</div>
                <div class="chip" onclick="jumpToCity('dn')">📍 Đà Nẵng</div>
                <div class="chip" onclick="jumpToCity('bd')">📍 Bình Dương</div>
                <div class="chip" onclick="jumpToCity('ct')">📍 Cần Thơ</div>
            </div>

            <!-- MAP POI & ROAD ELEMENTS LAYER FILTER -->
            <div class="map-elements-bar">
                <button class="layer-pill active" id="layer-signals" onclick="toggleMapLayer('signals')">
                    <span class="pill-dot" style="background:#10B981;"></span>🚦 Đèn Giao Thông
                </button>
                <button class="layer-pill active" id="layer-cameras" onclick="toggleMapLayer('cameras')">
                    <span class="pill-dot" style="background:#EF4444;"></span>📷 Phạt Nguội & Tốc Độ
                </button>
                <button class="layer-pill active" id="layer-tolls" onclick="toggleMapLayer('tolls')">
                    <span class="pill-dot" style="background:#F59E0B;"></span>🛑 Trạm Thu Phí
                </button>
                <button class="layer-pill active" id="layer-fuel" onclick="toggleMapLayer('fuel')">
                    <span class="pill-dot" style="background:#38BDF8;"></span>⛽ Cây Xăng & Sạc
                </button>
            </div>

            <div id="map"></div>
            <div class="map-hint">💡 Chạm vào bất kỳ điểm nào trên bản đồ để đặt đích đến! Bản đồ hiển thị tông màu tối CarPlay chống chói mắt.</div>

            <div class="dest-summary">
                <div>
                    <div class="label">Nơi đến đã chọn:</div>
                    <div class="place" id="selected-dest-txt">Chưa chọn điểm đến</div>
                </div>
            </div>

            <!-- Main Big Action Button -->
            <button class="btn-send-mochi" onclick="sendFromMap()">
                <span>📲 Bắn Tuyến Đường Sang Màn Hình Mochi</span>
            </button>
        </section>

        <!-- DUAL AUTOMATIC MODES -->
        <div class="auto-modes-grid">
            <button id="btn-real-gps" class="btn-mode-auto" onclick="toggleRealGpsDrive()">
                <span class="title">🚗 Lái Xe Thực Tế</span>
                <span class="desc" id="gps-desc-text">Theo dõi GPS iPhone liên tục</span>
            </button>
            <button id="btn-sim-drive" class="btn-mode-auto" onclick="toggleSimulatedDrive()">
                <span class="title">🎮 Mô Phỏng Lộ Trình</span>
                <span class="desc" id="sim-desc-text">Chạy demo xe ảo trên đường</span>
            </button>
        </div>

        <!-- SIMULATION ACTIVE CONTROLLER BAR -->
        <div id="sim-controls-bar" class="sim-controls-bar" style="display:none;">
            <div class="sim-status-chip">
                <span>🔴</span>
                <span id="sim-progress-txt">Chặng 1 / 1</span>
            </div>
            <div class="sim-btns-group">
                <button class="btn-sim-ctrl" id="btn-sim-speed" onclick="toggleSimSpeed()" title="Đổi tốc độ mô phỏng">⏩ 1x</button>
                <button class="btn-sim-ctrl" onclick="simSkipStep()" title="Bỏ qua đến chặng tiếp theo">⏭ Chặng kế</button>
                <button class="btn-sim-ctrl btn-sim-stop" onclick="toggleSimulatedDrive()" title="Dừng mô phỏng">⏹ Dừng</button>
            </div>
        </div>

        <!-- GOOGLE DIRECTIONS / TURN-BY-TURN STEPS LIST -->
        <details id="directions-panel" class="details-panel" open>
            <summary class="details-summary" style="background: rgba(15, 23, 42, 0.7); border-bottom: 1px solid var(--border-glass);">
                <span style="display: flex; align-items: center; gap: 6px;">🧭 <b>Chi Tiết Từng Chặng (Google Directions)</b></span>
                <span id="directions-count-badge" style="font-size: 11px; padding: 2px 8px; border-radius: 12px; background: rgba(56, 189, 248, 0.2); color: #38BDF8; font-weight: 800;">0 chặng</span>
            </summary>
            <div class="details-content" style="padding: 10px 12px; margin-top: 0;">
                <div id="directions-list" class="directions-list">
                    <div class="empty-directions">Chạm chọn điểm đến trên bản đồ để xem toàn bộ danh sách các ngã rẽ và đoạn đường.</div>
                </div>
            </div>
        </details>

        <!-- COLLAPSIBLE PRESETS & SPEED CONTROLS -->
        <details class="details-panel">
            <summary class="details-summary">
                <span>⚙️ Bảng Điều Khiển Nâng Cao & Thử Nghiệm</span>
                <span>▼</span>
            </summary>
            <div class="details-content">
                <div style="font-size: 11px; font-weight: 700; color: var(--text-muted); text-transform: uppercase;">Gửi nhanh tình huống mẫu sang Mochi:</div>
                <div class="preset-row">
                    <button class="btn-preset-small" onclick="sendPreset(0)">⬆️ Thẳng</button>
                    <button class="btn-preset-small" onclick="sendPreset(1)">➜ Phải</button>
                    <button class="btn-preset-small" onclick="sendPreset(2)">⬅ Trái</button>
                    <button class="btn-preset-small" onclick="sendPreset(3)">↶ Quay đầu</button>
                    <button class="btn-preset-small" onclick="sendPreset(4)" style="color:#F87171;">⚠️ Quá tốc độ</button>
                    <button class="btn-preset-small" onclick="sendPreset(5)" style="color:#34D399;">🏁 Đến đích</button>
                    <button class="btn-preset-small" onclick="sendPreset(6)">↖ Chếch trái</button>
                    <button class="btn-preset-small" onclick="sendPreset(7)">↗ Chếch phải</button>
                    <button class="btn-preset-small" onclick="sendPreset(8)">↺ Bùng binh</button>
                </div>

                <div style="font-size: 11px; font-weight: 700; color: var(--text-muted); text-transform: uppercase; margin-top: 6px;">Tốc độ giả lập (km/h):</div>
                <div class="speed-slider-wrap">
                    <input type="range" min="0" max="120" value="48" id="rng-speed" oninput="updateSpeedPreview(this.value)">
                    <div class="speed-pill-display" id="lbl-speed-val">48 km/h</div>
                </div>

                <div style="font-size: 11px; font-weight: 700; color: var(--text-muted); text-transform: uppercase; margin-top: 6px;">Biển giới hạn tốc độ (km/h):</div>
                <div class="speed-limit-row">
                    <button class="btn-lim" onclick="setLimit(40)">40</button>
                    <button class="btn-lim active" onclick="setLimit(50)">50</button>
                    <button class="btn-lim" onclick="setLimit(60)">60</button>
                    <button class="btn-lim" onclick="setLimit(80)">80</button>
                    <button class="btn-lim" onclick="setLimit(100)">100</button>
                </div>
            </div>
        </details>

    </div>

    <!-- Toast Notification -->
    <div id="toast" class="toast-msg">✓ Đã bắn dữ liệu sang Mochi!</div>

    <script>
        let lMap = null, lUserMarker = null, lDestMarker = null, lPolyline = null, lPolylineGlow = null;
        let userPos = [10.7769, 106.7009]; // Default: TP.HCM
        let destPos = null;
        let selectedRoadName = "";
        let currentLimit = 50;
        let currentSpeed = 0;
        let currentInstruction = "Đi thẳng";
        let currentDistance = "-- m";
        let currentEta = "--:--";
        let currentArrow = "↑";
        let currentDistanceMeters = 0;

        // Sound Chime State
        let soundEnabled = true;
        let audioCtx = null;
        let lastWarningTime = 0;

        // Screen Wake Lock
        let wakeLock = null;

        // Route coordinates for simulation
        let routeCoordinates = [];
        let simTimer = null;
        let simIndex = 0;

        // Real GPS Watcher
        let realGpsWatchId = null;

        // Turn-by-Turn Steps (Google Roads / Directions)
        let navigationSteps = [];
        let currentStepIdx = 0;

        function getDistanceMeters(p1, p2) {
            if (!p1 || !p2) return 0;
            const R = 6371000;
            const dLat = (p2[0] - p1[0]) * Math.PI / 180;
            const dLon = (p2[1] - p1[1]) * Math.PI / 180;
            const a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
                      Math.cos(p1[0] * Math.PI / 180) * Math.cos(p2[0] * Math.PI / 180) *
                      Math.sin(dLon / 2) * Math.sin(dLon / 2);
            const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
            return R * c;
        }

        // POI Database (Traffic Lights, Speed Cameras, Tolls, Fuel)
        const ROAD_POIS = [
            // TP.HCM CAMERAS
            { type: 'camera', name: 'Camera Hầm Thủ Thiêm', limit: 60, pos: [10.7712, 106.7065] },
            { type: 'camera', name: 'Camera Võ Văn Kiệt - Trần Đình Xu', limit: 60, pos: [10.7578, 106.6908] },
            { type: 'camera', name: 'Camera Phạm Văn Đồng - Phan Văn Trị', limit: 60, pos: [10.8242, 106.6948] },
            { type: 'camera', name: 'Camera Cầu Sài Gòn', limit: 60, pos: [10.7997, 106.7231] },
            { type: 'camera', name: 'Camera Mai Chí Thọ', limit: 60, pos: [10.7831, 106.7389] },
            { type: 'camera', name: 'Camera Xa Lộ Hà Nội - Bình Thái', limit: 60, pos: [10.8291, 106.7628] },
            { type: 'camera', name: 'Camera Nguyễn Văn Linh - Tân Thuận', limit: 60, pos: [10.7381, 106.7210] },
            { type: 'camera', name: 'Camera QL1A - Cầu Vượt Tân Thới Hiệp', limit: 50, pos: [10.8542, 106.6431] },

            // HÀ NỘI CAMERAS
            { type: 'camera', name: 'Camera Vành Đai 3 Trên Cao', limit: 80, pos: [20.9984, 105.7952] },
            { type: 'camera', name: 'Camera Cầu Nhật Tân', limit: 80, pos: [21.0892, 105.8197] },
            { type: 'camera', name: 'Camera Giải Phóng - Kim Đồng', limit: 50, pos: [20.9782, 105.8431] },
            { type: 'camera', name: 'Camera Cầu Thăng Long', limit: 80, pos: [21.1021, 105.7865] },

            // TRẠM THU PHÍ (TOLL PLAZAS / ETC)
            { type: 'toll', name: 'Trạm Thu Phí Long Phước (Cao Tốc)', fee: '35.000đ', pos: [10.8062, 106.8402] },
            { type: 'toll', name: 'Trạm Thu Phí Cầu Phú Mỹ', fee: '15.000đ', pos: [10.7431, 106.7412] },
            { type: 'toll', name: 'Trạm Thu Phí Xa Lộ Hà Nội', fee: '28.000đ', pos: [10.8354, 106.7720] },
            { type: 'toll', name: 'Trạm Thu Phí An Sương - An Lạc (QL1A)', fee: '15.000đ', pos: [10.7689, 106.6021] },
            { type: 'toll', name: 'Trạm Thu Phí Pháp Vân - Cầu Giẽ', fee: '45.000đ', pos: [20.9521, 105.8542] },

            // CÂY XĂNG & TRẠM SẠC ĐIỆN (FUEL & EV)
            { type: 'fuel', name: 'Petrolimex Số 01 (Quận 1)', pos: [10.7785, 106.6975] },
            { type: 'fuel', name: 'Petrolimex Hai Bà Trưng (Quận 3)', pos: [10.7862, 106.6912] },
            { type: 'fuel', name: 'PVOIL Điện Biên Phủ (Bình Thạnh)', pos: [10.8012, 106.7115] },
            { type: 'fuel', name: 'Trạm sạc VinFast EV - Landmark 81', pos: [10.7951, 106.7218] },
            { type: 'fuel', name: 'Petrolimex Giải Phóng (Hà Nội)', pos: [20.9892, 105.8421] }
        ];

        let mapLayerGroups = { signals: null, cameras: null, tolls: null, fuel: null };
        let layerVisibility = { signals: true, cameras: true, tolls: true, fuel: true };
        let dynamicRouteSignals = [];

        function toggleMapLayer(layerKey) {
            layerVisibility[layerKey] = !layerVisibility[layerKey];
            const btn = document.getElementById('layer-' + layerKey);
            if (btn) btn.classList.toggle('active', layerVisibility[layerKey]);
            const grp = mapLayerGroups[layerKey];
            if (grp && lMap) {
                if (layerVisibility[layerKey]) lMap.addLayer(grp);
                else lMap.removeLayer(grp);
            }
            showToast((layerVisibility[layerKey] ? 'Đã bật: ' : 'Đã ẩn: ') + layerKey);
        }

        function renderPoisOnMap() {
            if (!lMap) return;
            if (mapLayerGroups.cameras) mapLayerGroups.cameras.clearLayers();
            if (mapLayerGroups.tolls) mapLayerGroups.tolls.clearLayers();
            if (mapLayerGroups.fuel) mapLayerGroups.fuel.clearLayers();

            ROAD_POIS.forEach(poi => {
                let iconHtml = '';
                let iconSize = [30, 30];
                let iconAnchor = [15, 15];

                if (poi.type === 'camera') {
                    iconHtml = `<div class="poi-marker-camera" title="${poi.name}"><span class="cam-ico">📷</span><span class="cam-spd">${poi.limit}</span></div>`;
                    iconSize = [54, 24];
                    iconAnchor = [27, 12];
                    const m = L.marker(poi.pos, {
                        icon: L.divIcon({ className: 'custom-poi', html: iconHtml, iconSize: iconSize, iconAnchor: iconAnchor })
                    }).bindPopup(`<b>📷 ${poi.name}</b><br>Giới hạn tốc độ: <b>${poi.limit} km/h</b><br>Phạt nguội tự động 24/7`);
                    if (mapLayerGroups.cameras) mapLayerGroups.cameras.addLayer(m);
                } else if (poi.type === 'toll') {
                    iconHtml = `<div class="poi-marker-toll" title="${poi.name}">🛑 <span>${poi.fee || 'ETC'}</span></div>`;
                    iconSize = [64, 22];
                    iconAnchor = [32, 11];
                    const m = L.marker(poi.pos, {
                        icon: L.divIcon({ className: 'custom-poi', html: iconHtml, iconSize: iconSize, iconAnchor: iconAnchor })
                    }).bindPopup(`<b>🛑 ${poi.name}</b><br>Phí lượt: <b>${poi.fee}</b><br>Hỗ trợ VETC & ePass`);
                    if (mapLayerGroups.tolls) mapLayerGroups.tolls.addLayer(m);
                } else if (poi.type === 'fuel') {
                    iconHtml = `<div class="poi-marker-fuel" title="${poi.name}">⛽</div>`;
                    iconSize = [24, 24];
                    iconAnchor = [12, 12];
                    const m = L.marker(poi.pos, {
                        icon: L.divIcon({ className: 'custom-poi', html: iconHtml, iconSize: iconSize, iconAnchor: iconAnchor })
                    }).bindPopup(`<b>⛽ ${poi.name}</b><br>Nhiên liệu xăng dầu & Trạm sạc`);
                    if (mapLayerGroups.fuel) mapLayerGroups.fuel.addLayer(m);
                }
            });
        }

        function renderRouteSignals() {
            if (!mapLayerGroups.signals) return;
            mapLayerGroups.signals.clearLayers();
            dynamicRouteSignals = [];

            if (!navigationSteps || navigationSteps.length === 0) return;

            const totalRouteDist = navigationSteps.reduce((acc, s) => acc + (s.distanceM || 0), 0);
            const isLongTrip = totalRouteDist > 25000; // > 25km (interprovincial / highway trip like HCM -> Đà Lạt)

            let lastSigDist = -99999;
            let currentRouteDist = 0;
            let count = 0;
            const maxSignals = isLongTrip ? 3 : 4;

            navigationSteps.forEach((st, idx) => {
                const stepDist = st.distanceM || 0;
                currentRouteDist += stepDist;

                if (!st.location || idx === 0 || idx >= navigationSteps.length - 1) return;

                // On long inter-provincial trips, traffic lights ONLY exist in the departure urban zone (first 5km)
                // or the destination city center (last 5km). Highway stretches (QL, CT, passes) have ZERO signals.
                if (isLongTrip) {
                    const isNearStart = currentRouteDist <= 5000;
                    const isNearEnd = (totalRouteDist - currentRouteDist) <= 5000;
                    if (!isNearStart && !isNearEnd) return;
                }

                const nameLower = (st.name || '').toLowerCase();
                const actLower = (st.action || '').toLowerCase();

                // Skip highways, expressways, mountain passes, provincial roads, bypasses
                const isHighway = nameLower.includes('quốc lộ') || nameLower.includes('ql') ||
                                  nameLower.includes('đèo') || nameLower.includes('cao tốc') ||
                                  nameLower.includes('ct') || nameLower.includes('ah') ||
                                  nameLower.includes('đường cao tốc') || nameLower.includes('đt') ||
                                  nameLower.includes('bến phà') || nameLower.includes('ranh giới') ||
                                  nameLower.includes('tránh');

                // Must be an actual turning maneuver at a junction (not straight highway cruising)
                const isTurnManeuver = actLower.includes('rẽ') || actLower.includes('bùng binh') || actLower.includes('quay đầu');

                // Must be an urban street with turns
                const isUrban = (nameLower.includes('đường') || nameLower.includes('phố') ||
                                 nameLower.includes('ngã') || nameLower.includes('hẻm')) && !isHighway && isTurnManeuver;

                // Spacing: at least 1.8km between traffic signals to avoid clustering
                const hasSpacing = (currentRouteDist - lastSigDist) >= 1800;

                if (isUrban && hasSpacing && count < maxSignals && stepDist < 750) {
                    lastSigDist = currentRouteDist;
                    count++;

                    const sig = {
                        id: 'sig_' + idx,
                        stepIdx: idx,
                        name: 'Đèn giao thông ' + st.name,
                        pos: st.location,
                        state: (count % 2 === 0 ? 'green' : 'yellow')
                    };
                    dynamicRouteSignals.push(sig);

                    const iconHtml = `
                    <div class="poi-marker-traffic" id="map-sig-${idx}" title="Đèn tín hiệu giao thông: ${st.name}">
                        <span class="p-light red ${sig.state === 'red' ? 'active' : ''}"></span>
                        <span class="p-light yellow ${sig.state === 'yellow' ? 'active' : ''}"></span>
                        <span class="p-light green ${sig.state === 'green' ? 'active' : ''}"></span>
                    </div>`;

                    const m = L.marker(st.location, {
                        icon: L.divIcon({ className: 'custom-sig', html: iconHtml, iconSize: [16, 34], iconAnchor: [8, 17] })
                    }).bindPopup(`<b>🚦 Đèn tín hiệu giao thông</b><br>Ngã rẽ: <b>${st.instruction}</b><br>Cự ly chặng: ${st.distanceText}`);
                    mapLayerGroups.signals.addLayer(m);
                }
            });
        }

        // Real signal positions: OSM records a traffic-signal node at the
        // physical intersection. It does not expose the live red/yellow/green
        // state, so this layer deliberately renders a neutral marker.
        async function renderRouteSignals() {
            if (!mapLayerGroups.signals) return;
            mapLayerGroups.signals.clearLayers();
            dynamicRouteSignals = [];
            const candidates = (navigationSteps || [])
                .filter((step, index, all) => step.location && index > 0 && index < all.length - 1)
                .slice(0, 24);
            if (!candidates.length) return;
            try {
                const points = candidates.map(step => `${step.location[1]},${step.location[0]}`).join(';');
                const response = await fetch('/api/traffic-signals?points=' + encodeURIComponent(points));
                if (!response.ok) throw new Error('Signal lookup failed');
                const data = await response.json();
                (data.signals || []).forEach((signal, index) => {
                    const position = [signal.lat, signal.lng];
                    let nearestStep = 0;
                    let nearestDistance = Infinity;
                    candidates.forEach(step => {
                        const distance = getDistanceMeters(position, step.location);
                        if (distance < nearestDistance) {
                            nearestDistance = distance;
                            nearestStep = step.index;
                        }
                    });
                    dynamicRouteSignals.push({
                        id: 'osm_signal_' + index, stepIdx: nearestStep,
                        name: signal.name, pos: position, state: 'unknown', source: signal.source
                    });
                    const icon = '<div title="Den tin hieu giao thong (vi tri ban do, khong co mau realtime)" style="width:22px;height:42px;padding:3px 0;border-radius:8px;display:flex;flex-direction:column;align-items:center;justify-content:space-around;background:#0F172A;border:2px solid #CBD5E1;box-shadow:0 0 10px #64748B"><i style="width:8px;height:8px;border-radius:50%;background:#FF3B30;box-shadow:0 0 5px #FF3B30"></i><i style="width:8px;height:8px;border-radius:50%;background:#FFD60A;box-shadow:0 0 5px #FFD60A"></i><i style="width:8px;height:8px;border-radius:50%;background:#34C759;box-shadow:0 0 5px #34C759"></i></div>';
                    const marker = L.marker(position, {
                        icon: L.divIcon({ className: 'custom-sig', html: icon, iconSize: [22, 42], iconAnchor: [11, 21] })
                    }).bindPopup(`<b>Den tin hieu giao thong</b><br>Vi tri: OpenStreetMap<br>Trang thai mau den: chua co du lieu realtime`);
                    mapLayerGroups.signals.addLayer(marker);
                });
            } catch (error) {
                console.warn('OSM traffic-signal lookup failed:', error);
            }
        }

        async function renderRouteCameras() {
            if (!mapLayerGroups.cameras) return;
            const candidates = (navigationSteps || []).filter((s, i, a) => s.location && i > 0 && i < a.length - 1).slice(0, 24);
            if (!candidates.length) return;
            try {
                const points = candidates.map(s => `${s.location[1]},${s.location[0]}`).join(';');
                const response = await fetch('/api/speed-cameras?points=' + encodeURIComponent(points));
                if (!response.ok) throw new Error('Camera lookup failed');
                const data = await response.json();
                (data.cameras || []).forEach(camera => {
                    const pos = [camera.lat, camera.lng];
                    if (ROAD_POIS.some(p => p.type === 'camera' && getDistanceMeters(p.pos, pos) < 15)) return;
                    const cam = {type: 'camera', name: camera.name, limit: camera.limit || 0, pos: pos, source: 'OpenStreetMap'};
                    ROAD_POIS.push(cam);
                    const label = cam.limit || '!';
                    const marker = L.marker(pos, {icon: L.divIcon({className: 'custom-poi', html: `<div class="poi-marker-camera" title="Camera OSM"><span class="cam-ico">📷</span><span class="cam-spd">${label}</span></div>`, iconSize: [30,30], iconAnchor: [15,15]})})
                        .bindPopup(`<b>Camera tốc độ</b><br>Nguồn: OpenStreetMap${cam.limit ? '<br>Giới hạn: ' + cam.limit + ' km/h' : ''}`);
                    mapLayerGroups.cameras.addLayer(marker);
                });
            } catch (error) { console.warn('OSM speed-camera lookup failed:', error); }
        }

        const CITIES = {
            hcm: { name: "TP. Hồ Chí Minh", coords: [10.7769, 106.7009] },
            hn: { name: "Hà Nội", coords: [21.0285, 105.8542] },
            dn: { name: "Đà Nẵng", coords: [16.0544, 108.2022] },
            bd: { name: "Bình Dương", coords: [10.9805, 106.6519] },
            ct: { name: "Cần Thơ", coords: [10.0452, 105.7469] }
        };

        function showToast(msg) {
            const t = document.getElementById('toast');
            t.innerText = msg;
            t.style.display = 'block';
            setTimeout(() => { t.style.display = 'none'; }, 2400);
        }

        /* ── SOUND CHIME (WEB AUDIO API SYNTHESIZER) ── */
        function toggleSound() {
            soundEnabled = !soundEnabled;
            const btn = document.getElementById('btn-sound-toggle');
            const lbl = document.getElementById('lbl-sound');
            if (soundEnabled) {
                btn.style.color = 'var(--cyan)';
                lbl.innerText = 'Bật';
                playBeep(880, 0.12);
                showToast('🔊 Đã bật âm cảnh báo tốc độ');
            } else {
                btn.style.color = 'var(--text-muted)';
                lbl.innerText = 'Tắt';
                showToast('🔇 Đã tắt âm cảnh báo');
            }
        }

        function playBeep(freq = 880, duration = 0.12) {
            if (!soundEnabled) return;
            try {
                if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
                if (audioCtx.state === 'suspended') audioCtx.resume();
                const osc = audioCtx.createOscillator();
                const gain = audioCtx.createGain();
                osc.connect(gain);
                gain.connect(audioCtx.destination);
                osc.type = 'sine';
                osc.frequency.setValueAtTime(freq, audioCtx.currentTime);
                gain.gain.setValueAtTime(0.18, audioCtx.currentTime);
                gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + duration);
                osc.start();
                osc.stop(audioCtx.currentTime + duration);
            } catch (e) {}
        }

        function triggerOverspeedChime() {
            const now = Date.now();
            if (now - lastWarningTime > 4000) {
                lastWarningTime = now;
                playBeep(880, 0.1);
                setTimeout(() => playBeep(1174, 0.16), 130);
            }
        }

        /* ── HUD MIRROR MODE (PHẢN CHIẾU KÍNH LÁI) ── */
        async function toggleHudMirrorMode() {
            const isMirror = document.body.classList.toggle('hud-mirror-mode');
            const btn = document.getElementById('btn-hud-mirror');
            if (btn) btn.classList.toggle('active-hud-btn', isMirror);

            if (isMirror) {
                showToast('🪞 Đã bật Chế độ Chiếu Kính Lái ban đêm!');
                // Request Screen Wake Lock so display does not turn off
                if ('wakeLock' in navigator) {
                    try {
                        wakeLock = await navigator.wakeLock.request('screen');
                    } catch (e) {}
                }
            } else {
                showToast('Đã quay lại chế độ Bản đồ thông thường');
                if (wakeLock) {
                    try { await wakeLock.release(); wakeLock = null; } catch (e) {}
                }
            }
        }

        function jumpToCity(key) {
            const c = CITIES[key];
            if (!c) return;
            setUserPosition(c.coords[0], c.coords[1], true);
            showToast("📍 Đã chuyển tới " + c.name);
        }

        function setLimit(lim) {
            currentLimit = lim;
            document.querySelectorAll('.btn-lim').forEach(b => {
                b.classList.toggle('active', parseInt(b.innerText) === lim);
            });
            document.getElementById('prev-limit-val').innerText = lim;
            checkOverspeed();
        }

        function updateSpeedPreview(val) {
            currentSpeed = parseInt(val) || 0;
            document.getElementById('lbl-speed-val').innerText = currentSpeed + ' km/h';
            renderSpeedGauge(currentSpeed);
            checkOverspeed();
        }

        function renderSpeedGauge(spd) {
            document.getElementById('prev-spd-val').innerText = spd;
            // 217.8 is the arc length for 240 degrees at radius 52
            const maxSpd = 120.0;
            const ratio = Math.max(0, Math.min(1, spd / maxSpd));
            const arcOffset = 217.8 - (ratio * 217.8);
            const arcEl = document.getElementById('speed-arc-active');
            if (arcEl) {
                arcEl.style.strokeDashoffset = arcOffset.toFixed(1);
            }
        }

        function checkOverspeed() {
            const isOver = (currentLimit > 0 && currentSpeed > currentLimit);
            const mainScreen = document.getElementById('hud-main-screen');
            const spdCard = document.getElementById('prev-spd-card');
            const arcEl = document.getElementById('speed-arc-active');

            if (mainScreen) mainScreen.classList.toggle('overspeed', isOver);
            if (spdCard) spdCard.classList.toggle('overspeed', isOver);

            if (arcEl) {
                arcEl.style.stroke = isOver ? '#EF4444' : 'url(#speed-grad)';
            
            updateVietmapHUD(currentSpeed, currentLimit, currentArrow, currentDistance, currentEta, selectedRoadName, currentInstruction);
}

            if (isOver) {
                triggerOverspeedChime();
            }
        }

        function updateDistanceProgress(distM) {
            currentDistanceMeters = distM;
            const bar = document.getElementById('turn-progress-bar');
            const arrowWrap = document.getElementById('prev-arrow');
            const distTxt = document.getElementById('prev-dist');

            // Closer than 100m is imminent turn!
            const isNear = distM > 0 && distM <= 100;
            if (arrowWrap) arrowWrap.classList.toggle('near-turn', isNear);
            if (distTxt) distTxt.classList.toggle('near-turn', isNear);

            if (bar) {
                if (distM <= 0) {
                    bar.style.width = '0%';
                } else {
                    // Normalizes between 0 and 500m
                    const pct = Math.max(6, Math.min(100, Math.round((distM / 500) * 100)));
                    bar.style.width = pct + '%';
                    if (isNear) {
                        bar.style.background = '#10B981';
                    } else if (distM <= 250) {
                        bar.style.background = 'linear-gradient(90deg, #F59E0B, #10B981)';
                    } else {
                        bar.style.background = 'linear-gradient(90deg, #00F0FF, #3B82F6)';
                    }
                }
            }
        }

        /* ── LEAFLET MAP INITIALIZATION (CARPLAY DARK THEME) ── */
        function initMap() {
            currentArrow = "↑";
            currentInstruction = "Đang chờ tuyến đường...";
            currentDistance = "-- m";
            currentSpeed = 0;
            currentLimit = 60;
            const vmArrow = document.getElementById('vm-turn-arrow');
            if (vmArrow) vmArrow.innerText = "↑";
            const vmDist = document.getElementById('vm-dist-val');
            if (vmDist) vmDist.innerText = "-- m";
            const vmRoad = document.getElementById('vm-road-name');
            if (vmRoad) vmRoad.innerText = "Đang chờ tuyến đường...";
            const lLeft = document.getElementById('vm-lane-left');
            const lMid = document.getElementById('vm-lane-mid');
            const lRight = document.getElementById('vm-lane-right');
            if (lLeft) lLeft.className = 'vm-lane-arrow';
            if (lMid) lMid.className = 'vm-lane-arrow active';
            if (lRight) lRight.className = 'vm-lane-arrow';

            switchHudStyle('vietmap');
            updateLiveClock();

            // Check HTTPS
            if (location.protocol === 'http:') {
                const banner = document.getElementById('https-banner');
                const link = document.getElementById('https-link');
                if (banner && link) {
                    banner.style.display = 'flex';
                    link.href = 'https://' + location.hostname + ':8443/waze';
                }
            }

            try {
                lMap = L.map('map', { attributionControl: false, zoomControl: true }).setView(userPos, 14);

                // Official OpenStreetMap: 100% Free, No Watermark, No API Key
                L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
                    maxZoom: 19
                }).addTo(lMap);

                // POI and Traffic Element Layer Groups
                mapLayerGroups.signals = L.layerGroup().addTo(lMap);
                mapLayerGroups.cameras = L.layerGroup().addTo(lMap);
                mapLayerGroups.tolls = L.layerGroup().addTo(lMap);
                mapLayerGroups.fuel = L.layerGroup().addTo(lMap);
                renderPoisOnMap();

                // Keep verified signal markers visible even in route overview.
                // There are only a small, route-scoped set of markers now.
                lMap.on('zoomend', () => {
                    if (layerVisibility.signals && mapLayerGroups.signals && !lMap.hasLayer(mapLayerGroups.signals)) {
                        lMap.addLayer(mapLayerGroups.signals);
                    }
                });

                // User Start Pin (High-contrast Cyan Glow)
                const userIcon = L.divIcon({
                    className: 'user-pin',
                    html: '<div style="background:#00F0FF;width:20px;height:20px;border-radius:50%;border:3px solid #FFF;box-shadow:0 0 16px #00F0FF;"></div>',
                    iconSize: [20, 20],
                    iconAnchor: [10, 10]
                });
                lUserMarker = L.marker(userPos, { icon: userIcon, draggable: true }).addTo(lMap);
                lUserMarker.on('dragend', (e) => {
                    userPos = [e.target.getLatLng().lat, e.target.getLatLng().lng];
                    if (destPos) recalculateRoute();
                });

                // Click on map to set Destination
                lMap.on('click', (e) => {
                    setDestination(e.latlng.lat, e.latlng.lng);
                });

                // Map Zoom Level of Detail (LOD) listener to keep overview uncluttered
                function updateMapLod() {
                    if (!lMap) return;
                    const z = lMap.getZoom();
                    const mapEl = document.getElementById('map');
                    if (mapEl) {
                        if (z < 12) mapEl.classList.add('map-zoom-out');
                        else mapEl.classList.remove('map-zoom-out');
                    }
                }
                lMap.on('zoomend', updateMapLod);
                updateMapLod();

                // Invalidate size for mobile rendering
                setTimeout(() => { if (lMap) { lMap.invalidateSize(); updateMapLod(); } }, 200);

                // Initial gauge rendering
                renderSpeedGauge(currentSpeed);
                renderRecentPlacesBar();

                // Auto locate on start if available
                locateMe(true);
            } catch (err) {
                console.error("Map init error:", err);
            }
        }

        function setUserPosition(lat, lng, pan = false) {
            userPos = [lat, lng];
            if (lUserMarker) lUserMarker.setLatLng([lat, lng]);
            if (pan && lMap) lMap.setView([lat, lng], 15);
            if (destPos) recalculateRoute();
        }

        async function setDestination(lat, lng, knownName = null) {
            destPos = [lat, lng];

            // Place Red Dest Marker
            const destIcon = L.divIcon({
                className: 'dest-pin',
                html: '<div style="background:#EF4444;width:22px;height:22px;border-radius:50%;border:3.5px solid #FFF;box-shadow:0 0 16px #EF4444;"></div>',
                iconSize: [22, 22],
                iconAnchor: [11, 11]
            });
            if (lDestMarker) {
                lDestMarker.setLatLng([lat, lng]);
            } else {
                lDestMarker = L.marker([lat, lng], { icon: destIcon, draggable: true }).addTo(lMap);
                lDestMarker.on('dragend', (e) => {
                    setDestination(e.target.getLatLng().lat, e.target.getLatLng().lng);
                });
            }

            if (knownName) {
                selectedRoadName = knownName;
                document.getElementById('selected-dest-txt').innerText = knownName;
                document.getElementById('prev-road').innerText = knownName;
                saveRecentPlace(knownName, lat, lng);
            } else {
                document.getElementById('selected-dest-txt').innerText = "Đang tra cứu tên đường...";
                try {
                    const res = await fetch(`/api/reverse?lat=${lat}&lon=${lng}`);
                    const data = await res.json();
                    const addr = data.address || {};
                    const road = addr.road || addr.quarter || addr.suburb || data.name || "Điểm đến";
                    const city = addr.city || addr.town || "";
                    selectedRoadName = road + (city ? ` (${city})` : "");
                    document.getElementById('selected-dest-txt').innerText = selectedRoadName;
                    document.getElementById('prev-road').innerText = selectedRoadName;
                    saveRecentPlace(selectedRoadName, lat, lng);
                } catch (e) {
                    selectedRoadName = `Tọa độ: ${lat.toFixed(4)}, ${lng.toFixed(4)}`;
                    document.getElementById('selected-dest-txt').innerText = selectedRoadName;
                    document.getElementById('prev-road').innerText = selectedRoadName;
                    saveRecentPlace(selectedRoadName, lat, lng);
                }
            }

            recalculateRoute();
        }

        async function recalculateRoute() {
            if (!destPos || !userPos) return;

            try {
                let data = null;
                // Try backend proxy /api/route first
                try {
                    const proxyUrl = `/api/route?start=${userPos[1]},${userPos[0]}&end=${destPos[1]},${destPos[0]}`;
                    const res = await fetch(proxyUrl);
                    if (res.ok) data = await res.json();
                } catch (e) {
                    console.warn("Proxy route failed, trying direct OSRM:", e);
                }

                if (!data || !data.routes || data.routes.length === 0) {
                    const directUrl = `https://router.project-osrm.org/route/v1/driving/${userPos[1]},${userPos[0]};${destPos[1]},${destPos[0]}?overview=full&geometries=geojson&steps=true`;
                    const res = await fetch(directUrl);
                    if (!res.ok) throw new Error("OSRM err");
                    data = await res.json();
                }

                if (!data.routes || data.routes.length === 0) throw new Error("No route");

                const route = data.routes[0];
                routeCoordinates = route.geometry.coordinates.map(c => [c[1], c[0]]);

                // Draw Glowing Polyline (Dual-layer for Neon effect)
                if (lPolylineGlow) lMap.removeLayer(lPolylineGlow);
                if (lPolyline) lMap.removeLayer(lPolyline);

                lPolylineGlow = L.polyline(routeCoordinates, {
                    color: '#0284C7',
                    weight: 12,
                    opacity: 0.35,
                    lineJoin: 'round',
                    lineCap: 'round'
                }).addTo(lMap);

                lPolyline = L.polyline(routeCoordinates, {
                    color: '#00F0FF',
                    weight: 6,
                    opacity: 0.95,
                    lineJoin: 'round',
                    lineCap: 'round'
                }).addTo(lMap);

                lMap.fitBounds(lPolyline.getBounds(), { padding: [35, 35] });

                // Distance
                const distM = route.distance;
                currentDistance = distM < 1000 ? Math.round(distM) + ' m' : (distM / 1000).toFixed(1) + ' km';
                const pDist = document.getElementById('prev-dist');
                const vDist = document.getElementById('vm-dist-val');
                if (pDist) pDist.innerText = currentDistance;
                if (vDist) vDist.innerText = currentDistance;

                // ETA
                const durSec = route.duration;
                const now = new Date();
                now.setSeconds(now.getSeconds() + durSec);
                currentEta = now.toLocaleTimeString('vi-VN', { hour: '2-digit', minute: '2-digit' });
                const pEta = document.getElementById('prev-eta');
                const vEta = document.getElementById('vm-eta-val');
                if (pEta) pEta.innerText = '⏱ Dự kiến: ' + currentEta;
                if (vEta) vEta.innerText = 'ETA ' + currentEta;

                // ── PARSE ALL STEPS (GOOGLE ROADS / DIRECTIONS STYLE) ──
                navigationSteps = [];
                const legs = route.legs || [];
                const rawSteps = (legs.length > 0 && legs[0].steps) ? legs[0].steps : [];

                for (let i = 0; i < rawSteps.length; i++) {
                    const st = rawSteps[i];
                    const maneuver = st.maneuver || {};
                    const type = maneuver.type || '';
                    const mod = maneuver.modifier || '';
                    const stepDist = Math.round(st.distance || 0);
                    let roadName = (st.name && st.name.trim()) ? st.name.trim() : (i === 0 ? "Vị trí xuất phát" : (i === rawSteps.length - 1 ? (selectedRoadName || "Điểm đến") : "Đoạn đường tiếp theo"));

                    let arrow = '↑';
                    let action = 'Đi thẳng';
                    let lane = 1;

                    if (type === 'depart') {
                        arrow = '↑';
                        action = 'Khởi hành trên';
                        lane = 1;
                    } else if (type === 'arrive') {
                        arrow = '🏁';
                        action = 'Đến điểm hẹn:';
                        lane = 1;
                    } else if (mod.includes('uturn') || type === 'uturn') {
                        arrow = '↶';
                        action = 'Quay đầu xe tại';
                        lane = 0;
                    } else if (type === 'roundabout' || type === 'rotary') {
                        arrow = '↺';
                        action = 'Vào bùng binh rẽ vào';
                        lane = mod.includes('left') ? 0 : 2;
                    } else if (mod.includes('sharp left')) {
                        arrow = '↰';
                        action = 'Rẽ ngoặt trái vào';
                        lane = 0;
                    } else if (mod.includes('slight left') || (type === 'fork' && mod.includes('left'))) {
                        arrow = '↖';
                        action = 'Chếch trái vào';
                        lane = 0;
                    } else if (mod.includes('sharp right')) {
                        arrow = '↱';
                        action = 'Rẽ ngoặt phải vào';
                        lane = 2;
                    } else if (mod.includes('slight right') || (type === 'fork' && mod.includes('right'))) {
                        arrow = '↗';
                        action = 'Chếch phải vào';
                        lane = 2;
                    } else if (mod.includes('left')) {
                        arrow = '↰';
                        action = 'Rẽ trái vào';
                        lane = 0;
                    } else if (mod.includes('right')) {
                        arrow = '↱';
                        action = 'Rẽ phải vào';
                        lane = 2;
                    } else if (mod.includes('straight') || type === 'continue' || type === 'new name') {
                        arrow = '↑';
                        action = 'Đi thẳng tiếp tục';
                        lane = 1;
                    } else {
                        // OSRM did not provide an explicit maneuver.  A road curve is
                        // not a turn, so never infer left/right from bearing changes.
                        arrow = '↑';
                        action = 'Đi thẳng tiếp tục';
                        lane = 1;
                    }

                    const loc = (maneuver.location && maneuver.location.length >= 2) ? [maneuver.location[1], maneuver.location[0]] : null;

                    navigationSteps.push({
                        index: i,
                        name: roadName,
                        action: action,
                        instruction: `${action} ${roadName}`,
                        arrow: arrow,
                        distanceM: stepDist,
                        distanceText: stepDist < 1000 ? `${stepDist} m` : `${(stepDist / 1000).toFixed(1)} km`,
                        location: loc,
                        lane: lane
                    });
                }

                if (navigationSteps.length === 0) {
                    navigationSteps.push({
                        index: 0,
                        name: selectedRoadName || "Lộ trình",
                        action: "Đi thẳng",
                        instruction: "Đi thẳng về phía trước",
                        arrow: "↑",
                        distanceM: Math.round(distM),
                        distanceText: currentDistance,
                        location: destPos,
                        lane: 1
                    });
                }

                renderDirectionsList();
                renderRouteSignals();
                renderRouteCameras();
                updateActiveStep(0);

            } catch (err) {
                console.warn("Routing fallback:", err);
                if (lPolylineGlow) lMap.removeLayer(lPolylineGlow);
                if (lPolyline) lMap.removeLayer(lPolyline);
                lPolyline = L.polyline([userPos, destPos], { color: '#64748B', weight: 4, dashArray: '6, 6' }).addTo(lMap);
            }
        }

        function renderDirectionsList() {
            const listEl = document.getElementById('directions-list');
            const badgeEl = document.getElementById('directions-count-badge');
            if (!listEl) return;

            if (!navigationSteps || navigationSteps.length === 0) {
                listEl.innerHTML = `<div class="empty-directions">Chạm chọn điểm đến trên bản đồ để xem toàn bộ danh sách các ngã rẽ và đoạn đường.</div>`;
                if (badgeEl) badgeEl.innerText = "0 chặng";
                return;
            }

            if (badgeEl) badgeEl.innerText = `${navigationSteps.length} chặng • ${currentDistance}`;

            let html = '';
            navigationSteps.forEach((st, idx) => {
                const isActive = (idx === currentStepIdx);
                let subText = '';
                if (idx === navigationSteps.length - 1) {
                    subText = 'Điểm kết thúc hành trình';
                } else if (st.action && st.action.includes('Rẽ')) {
                    subText = `Sau ngã rẽ chạy thẳng ${st.distanceText} trên ${st.name}`;
                } else {
                    subText = `Đoạn đường tiếp theo: ${st.distanceText}`;
                }
                html += `
                <div class="dir-step-item ${isActive ? 'active-step' : ''}" id="dir-step-${idx}" onclick="focusStep(${idx})">
                    <div class="dir-step-num">${idx + 1}</div>
                    <div class="dir-step-icon">${st.arrow}</div>
                    <div class="dir-step-info">
                        <div class="dir-step-road">${st.instruction}</div>
                        <div class="dir-step-sub">${subText}</div>
                    </div>
                    <div class="dir-step-dist">${st.distanceText}</div>
                </div>`;
            });
            listEl.innerHTML = html;
        }

        function focusStep(idx) {
            if (!navigationSteps || idx < 0 || idx >= navigationSteps.length) return;
            const st = navigationSteps[idx];
            simStepIdx = idx;
            simStepPhase = 0;
            if (st.location && lMap) {
                userPos = st.location;
                if (lUserMarker) lUserMarker.setLatLng(userPos);
                lMap.setView(st.location, 16, { animate: true });
                showToast(`📍 Chặng ${idx + 1}: ${st.instruction}`);
            }
            updateActiveStep(idx, st.distanceM, true);
        }

        function updateActiveStep(idx, remainingDistM = null, isDirectFocus = false) {
            if (!navigationSteps || navigationSteps.length === 0) return;
            if (idx < 0) idx = 0;
            if (idx >= navigationSteps.length) idx = navigationSteps.length - 1;
            currentStepIdx = idx;

            const curStep = navigationSteps[idx];
            const isLast = (idx >= navigationSteps.length - 1);
            const nextStep = isLast ? curStep : navigationSteps[idx + 1];

            // Distance to complete this step and reach upcoming maneuver
            let distM = remainingDistM !== null ? remainingDistM : curStep.distanceM;
            if (isLast) distM = 0;
            let distText = distM < 1000 ? Math.round(distM) + " m" : (distM / 1000).toFixed(1) + " km";

            // Current street car is currently driving on
            const activeRoad = curStep.name || selectedRoadName || "Đang di chuyển";

            // Realistic GPS Navigation Logic:
            // When cruising (> 200m before upcoming turn), car is going straight along activeRoad.
            // When approaching junction (<= 200m), HUD alerts the driver of upcoming turn.
            let driverArrow = "↑";
            let driverInstruction = "";
            // A straight maneuver is always shown in the centre lane.  Vehicle
            // type changes the visual HUD only; it must not change navigation.
            let targetLane = 1;

            if (isDirectFocus) {
                // User directly tapped this step in the list to preview it
                driverArrow = curStep.arrow || "↑";
                driverInstruction = curStep.instruction;
                targetLane = curStep.lane !== undefined ? curStep.lane : 1;
            } else if (isLast) {
                driverArrow = "🏁";
                driverInstruction = "Đã đến nơi an toàn!";
                targetLane = 1;
            } else if (distM <= 200) {
                // Approaching upcoming turn countdown
                driverArrow = nextStep.arrow || "↑";
                driverInstruction = nextStep.instruction;
                targetLane = nextStep.lane !== undefined ? nextStep.lane : 1;
            } else {
                // Cruising along current road -> GO STRAIGHT
                driverArrow = "↑";
                driverInstruction = (idx === 0 && curStep.action.includes('Khởi hành'))
                    ? curStep.instruction
                    : `Đi thẳng trên ${activeRoad}`;
                targetLane = 1;
            }

            currentArrow = driverArrow;
            currentInstruction = driverInstruction;
            currentDistance = distText;

            // Update Vietmap Cockpit Elements
            const vmArrow = document.getElementById('vm-turn-arrow');
            const vmDist = document.getElementById('vm-dist-val');
            const vmRoad = document.getElementById('vm-road-name');
            if (vmArrow) vmArrow.innerText = driverArrow;
            if (vmDist) vmDist.innerText = distText;
            if (vmRoad) vmRoad.innerText = activeRoad;

            const lLeft = document.getElementById('vm-lane-left');
            const lMid = document.getElementById('vm-lane-mid');
            const lRight = document.getElementById('vm-lane-right');
            if (lLeft) lLeft.className = 'vm-lane-arrow' + (targetLane === 0 ? ' active' : '');
            if (lMid) lMid.className = 'vm-lane-arrow' + (targetLane === 1 ? ' active' : '');
            if (lRight) lRight.className = 'vm-lane-arrow' + (targetLane === 2 ? ' active' : '');

            // Update Tesla Cockpit Elements
            const pArrow = document.getElementById('prev-arrow');
            const pDist = document.getElementById('prev-dist');
            const pRoad = document.getElementById('prev-road');
            const pInst = document.getElementById('prev-inst');
            if (pArrow) pArrow.innerText = driverArrow;
            if (pDist) pDist.innerText = distText;
            if (pRoad) pRoad.innerText = activeRoad;
            if (pInst) pInst.innerText = driverInstruction;

            updateDistanceProgress(distM);

            // Realistic Traffic Light Check:
            let tfDistText = "-- M";
            let lightState = 'none';

            let nearbySig = null;
            let minSigDist = 999999;
            if (dynamicRouteSignals && dynamicRouteSignals.length > 0 && userPos) {
                dynamicRouteSignals.forEach(s => {
                    if (s.pos) {
                        const d = getDistanceMeters(userPos, s.pos);
                        if (d < minSigDist) {
                            minSigDist = d;
                            nearbySig = s;
                        }
                    }
                });
            }

            // Proximity check: either by GPS position or by remaining step distance if next junction has signal
            const checkTfDist = remainingDistM !== null ? remainingDistM : (curStep.distanceM || 0);
            const hasSigAtNextTurn = dynamicRouteSignals && dynamicRouteSignals.some(s => s.stepIdx === (idx + 1) || s.stepIdx === idx);

            if ((nearbySig && minSigDist <= 300 && minSigDist > 0) || (hasSigAtNextTurn && checkTfDist <= 300 && checkTfDist > 0)) {
                let tfDistM = Math.round(nearbySig && minSigDist <= 300 ? minSigDist : checkTfDist);
                tfDistText = tfDistM + " M";
                // Position is mapped, but no public real-time signal colour is
                // available. Never fabricate a red/yellow/green state.
                lightState = 'unknown';
            } else {
                tfDistText = "-- M";
                lightState = 'none';
            }

            const tfDistEl = document.getElementById('vm-traffic-dist');
            if (tfDistEl) tfDistEl.innerText = tfDistText;

            const lRed = document.getElementById('vm-light-red');
            const lYel = document.getElementById('vm-light-yellow');
            const lGrn = document.getElementById('vm-light-green');
            if (lRed) lRed.classList.toggle('active', lightState === 'red');
            if (lYel) lYel.classList.toggle('active', lightState === 'yellow');
            if (lGrn) lGrn.classList.toggle('active', lightState === 'green');

            // Proximity Check for Speed Enforcement Cameras
            let nearestCam = null;
            let minCamDist = 999999;
            if (userPos && ROAD_POIS) {
                ROAD_POIS.filter(p => p.type === 'camera').forEach(cam => {
                    const d = getDistanceMeters(userPos, cam.pos);
                    if (d < minCamDist) {
                        minCamDist = d;
                        nearestCam = cam;
                    }
                });
            }

            const alertBanner = document.getElementById('hud-alert-banner');
            const alertMsg = document.getElementById('alert-banner-msg');
            const alertDist = document.getElementById('alert-banner-dist');
            if (nearestCam && minCamDist <= 300) {
                if (alertBanner) alertBanner.style.display = 'flex';
                if (alertMsg) alertMsg.innerText = `Sắp đến ${nearestCam.name} (${nearestCam.limit} km/h)`;
                if (alertDist) alertDist.innerText = Math.round(minCamDist) + ' M';
                if (currentSpeed > nearestCam.limit) {
                    triggerOverspeedChime();
                }
            } else {
                if (alertBanner) alertBanner.style.display = 'none';
            }

            // The compact Mochi HUD has no secondary alert banner. While a
            // mapped camera is within range, use its instruction line so the
            // warning is visible on the physical device as well.
            const mochiInstruction = (nearestCam && minCamDist <= 300)
                ? `CANH BAO CAMERA OSM ${Math.round(minCamDist)} m`
                : driverInstruction;

            // Highlight in Google Directions List
            document.querySelectorAll('.dir-step-item').forEach((el, i) => {
                if (i === idx) {
                    el.classList.add('active-step');
                    el.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
                } else {
                    el.classList.remove('active-step');
                }
            });

            // ── Arrow & Lane Code for Mochi LCD ──
            const arrowCode = getArrowCode(driverArrow, driverInstruction);

            // Send to Mochi UDP Port 8888
            sendToMochi({
                road: activeRoad,
                instruction: mochiInstruction,
                distance: distText,
                speed: currentSpeed,
                speed_limit: currentLimit,
                eta: currentEta,
                style: activeHudStyle,
                vehicle: currentVehicleMode,
                traffic_dist: tfDistText,
                traffic_light: lightState,
                arrow: arrowCode,
                lane: targetLane,
                auto: true
            });
        }

        /* ── HELPER: MAP ARROW ICON / TEXT TO FIRMWARE CODE ── */
        function getArrowCode(arrowStr, instStr = '') {
            const a = (arrowStr || '').trim();
            if (a === '↑' || a === 'straight') return 'straight';
            if (a === '↖' || a === 'slight_left') return 'slight_left';
            if (a === '↗' || a === 'slight_right') return 'slight_right';
            if (a === '↰' || a === 'sharp_left') return 'sharp_left';
            if (a === '↱' || a === 'sharp_right') return 'sharp_right';
            if (a === '⬅' || a === 'left') return 'left';
            if (a === '➜' || a === 'right') return 'right';
            if (a === '↺' || a === 'roundabout' || a === 'rotary') return 'roundabout';
            if (a === '↶' || a === 'uturn') return 'uturn';
            if (a === '🏁' || a === 'arrive') return 'arrive';

            const combined = ((instStr || '') + ' ' + (arrowStr || '')).toLowerCase();
            if (combined.includes('chếch trái') || combined.includes('slight left')) return 'slight_left';
            if (combined.includes('chếch phải') || combined.includes('slight right')) return 'slight_right';
            if (combined.includes('rẽ ngoặt trái') || combined.includes('sharp left')) return 'sharp_left';
            if (combined.includes('rẽ ngoặt phải') || combined.includes('sharp right')) return 'sharp_right';
            if (combined.includes('rẽ trái') || combined.includes('quẹo trái') || combined.includes('turn left')) {
                return 'left';
            }
            if (combined.includes('rẽ phải') || combined.includes('chếch phải') || combined.includes('quẹo phải') || combined.includes('turn right')) {
                return 'right';
            }
            if (combined.includes('quay đầu') || combined.includes('u-turn') || combined.includes('uturn')) {
                return 'uturn';
            }
            if (combined.includes('đến nơi') || combined.includes('kết thúc') || combined.includes('arrive') || combined.includes('an toàn')) {
                return 'arrive';
            }
            return 'straight';
        }

        /* ── RECENT PLACES HISTORY ENGINE ── */
        const RECENT_PLACES_KEY = 'mochi_recent_places';

        function getRecentPlaces() {
            try {
                const raw = localStorage.getItem(RECENT_PLACES_KEY);
                return raw ? JSON.parse(raw) : [];
            } catch (e) {
                return [];
            }
        }

        function saveRecentPlace(name, lat, lon) {
            if (!name || !lat || !lon) return;
            let list = getRecentPlaces();
            list = list.filter(item => item.name !== name && (Math.abs(item.lat - lat) > 0.0005 || Math.abs(item.lon - lon) > 0.0005));
            list.unshift({ name: name, lat: lat, lon: lon, time: Date.now() });
            if (list.length > 8) list = list.slice(0, 8);
            try {
                localStorage.setItem(RECENT_PLACES_KEY, JSON.stringify(list));
            } catch (e) {}
            renderRecentPlacesBar();
        }

        function clearRecentPlaces() {
            try {
                localStorage.removeItem(RECENT_PLACES_KEY);
            } catch (e) {}
            renderRecentPlacesBar();
            showToast("🗑️ Đã xoá lịch sử nơi đã đến");
        }

        function renderRecentPlacesBar() {
            const wrap = document.getElementById('recent-places-wrap');
            const bar = document.getElementById('recent-chips-bar');
            if (!wrap || !bar) return;
            const list = getRecentPlaces();
            if (!list || list.length === 0) {
                wrap.style.display = 'none';
                return;
            }
            wrap.style.display = 'flex';
            bar.innerHTML = list.map(item => `
                <div class="recent-chip" onclick="selectRecentPlace(${item.lat}, ${item.lon}, '${item.name.replace(/'/g, "\\'")}')">
                    <span>🕒</span>
                    <span>${item.name}</span>
                </div>
            `).join('');
        }

        function selectRecentPlace(lat, lon, name) {
            if (lMap) lMap.setView([lat, lon], 16);
            setDestination(lat, lon, name);
            const inp = document.getElementById('map-search-inp');
            if (inp) inp.value = name;
            closeSearchDropdown();
            showToast(`📍 Chọn: ${name}`);
        }

        /* ── LIVE SEARCH AUTOCOMPLETE ── */
        let searchDebounceTimer = null;

        function onSearchInput(val) {
            clearTimeout(searchDebounceTimer);
            const query = (val || '').trim();
            if (query.length < 2) {
                closeSearchDropdown();
                return;
            }
            searchDebounceTimer = setTimeout(() => {
                performAutocomplete(query);
            }, 250);
        }

        function onSearchFocus() {
            const val = document.getElementById('map-search-inp').value.trim();
            if (val.length >= 2) {
                performAutocomplete(val);
            }
        }

        function closeSearchDropdown() {
            const dd = document.getElementById('search-dropdown');
            if (dd) dd.style.display = 'none';
        }

        async function performAutocomplete(query) {
            const dd = document.getElementById('search-dropdown');
            if (!dd) return;
            dd.style.display = 'block';
            dd.innerHTML = '<div class="dropdown-loading"><span>⏳</span><span>Đang tìm kiếm điểm đến...</span></div>';
            try {
                const res = await fetch(`/api/search?q=${encodeURIComponent(query)}&limit=6`);
                const results = await res.json();
                if (!results || results.length === 0) {
                    dd.innerHTML = '<div class="dropdown-loading" style="color:#94A3B8;"><span>🔍</span><span>Không tìm thấy địa điểm nào phù hợp</span></div>';
                    return;
                }
                let html = '';
                results.forEach(item => {
                    const rawName = item.display_name || '';
                    const parts = rawName.split(',');
                    const title = parts[0].trim();
                    const subtitle = parts.slice(1, 4).join(',').trim();
                    const lat = parseFloat(item.lat);
                    const lon = parseFloat(item.lon);

                    let icon = '📍';
                    const lower = rawName.toLowerCase();
                    if (lower.includes('cà phê') || lower.includes('coffee') || lower.includes('quán')) icon = '☕';
                    else if (lower.includes('nhà hàng') || lower.includes('quán ăn') || lower.includes('food')) icon = '🍽️';
                    else if (lower.includes('bệnh viện') || lower.includes('hospital')) icon = '🏥';
                    else if (lower.includes('trường') || lower.includes('đại học') || lower.includes('school')) icon = '🏫';
                    else if (lower.includes('chung cư') || lower.includes('tòa nhà') || lower.includes('building') || lower.includes('landmark')) icon = '🏢';
                    else if (lower.includes('chợ') || lower.includes('siêu thị') || lower.includes('mall')) icon = '🛍️';
                    else if (lower.includes('sân bay') || lower.includes('airport')) icon = '✈️';
                    else if (lower.includes('cầu') || lower.includes('bridge')) icon = '🌉';
                    else if (lower.includes('khách sạn') || lower.includes('hotel')) icon = '🏨';

                    html += `
                        <div class="search-dropdown-item" onclick="onSelectSuggestion(${lat}, ${lon}, '${title.replace(/'/g, "\\'")}')">
                            <div class="dropdown-item-icon">${icon}</div>
                            <div class="dropdown-item-info">
                                <div class="dropdown-item-title">${title}</div>
                                <div class="dropdown-item-sub">${subtitle || rawName}</div>
                            </div>
                        </div>
                    `;
                });
                dd.innerHTML = html;
            } catch (e) {
                dd.innerHTML = '<div class="dropdown-loading" style="color:#EF4444;"><span>⚠️</span><span>Lỗi tìm kiếm, thử lại sau</span></div>';
            }
        }

        function onSelectSuggestion(lat, lon, title) {
            closeSearchDropdown();
            const inp = document.getElementById('map-search-inp');
            if (inp) inp.value = title;
            if (lMap) lMap.setView([lat, lon], 16);
            setDestination(lat, lon, title);
            showToast(`📍 Đã chọn: ${title}`);
        }

        // Close dropdown when clicking outside
        document.addEventListener('click', (e) => {
            const wrap = document.querySelector('.search-input-wrap');
            if (wrap && !wrap.contains(e.target)) {
                closeSearchDropdown();
            }
        });

        async function searchLocation() {
            closeSearchDropdown();
            const q = document.getElementById('map-search-inp').value.trim();
            if (!q) return;
            try {
                const res = await fetch(`/api/search?q=${encodeURIComponent(q)}&limit=1`);
                const results = await res.json();
                if (results && results.length > 0) {
                    const lat = parseFloat(results[0].lat);
                    const lon = parseFloat(results[0].lon);
                    lMap.setView([lat, lon], 16);
                    setDestination(lat, lon, results[0].display_name.split(',')[0]);
                    showToast("📍 Đã tìm thấy: " + results[0].display_name.split(',')[0]);
                } else {
                    alert("Không tìm thấy địa điểm này. Bác hãy thử gõ tên cụ thể hơn nhé!");
                }
            } catch (e) {
                alert("Lỗi tìm kiếm: " + e);
            }
        }

        function locateMe(silent = false) {
            if (navigator.geolocation) {
                navigator.geolocation.getCurrentPosition(pos => {
                    const lat = pos.coords.latitude;
                    const lng = pos.coords.longitude;
                    setUserPosition(lat, lng, true);
                    const acc = Math.round(pos.coords.accuracy || 10);
                    document.getElementById('gps-status-txt').innerText = `📡 GPS iPhone: ±${acc}m`;
                    if (!silent) showToast(`✓ Đã định vị chính xác! (±${acc}m)`);
                }, err => {
                    if (!silent) {
                        alert("Không thể đọc GPS. Nếu dùng iPhone, bác hãy bấm 'Chuyển HTTPS (8443)' ở thanh trên cùng nhé!");
                    }
                }, { enableHighAccuracy: true, timeout: 8000 });
            }
        }

        let activeHudStyle = 'vietmap';
        let currentVehicleMode = 'car';
        let lastMochiNavSignature = '';
        let lastMochiNavSentAt = 0;

        /* ── SEND DATA TO MOCHI UDP ── */
        async function sendToMochi(payload = {}) {
            try {
                const arrow = payload.arrow || getArrowCode(currentArrow, payload.instruction || currentInstruction);
                let lane = payload.lane !== undefined ? payload.lane : 1;
                if (payload.lane === undefined) {
                    if (arrow === 'left') lane = 0;
                    else if (arrow === 'right') lane = 2;
                    else lane = 1;
                }
                const params = new URLSearchParams({
                    road: payload.road || selectedRoadName || "Điểm đến",
                    instruction: payload.instruction || currentInstruction,
                    distance: payload.distance || currentDistance,
                    speed: payload.speed !== undefined ? payload.speed : currentSpeed,
                    speed_limit: payload.speed_limit !== undefined ? payload.speed_limit : currentLimit,
                    eta: payload.eta || currentEta,
                    style: payload.style || activeHudStyle || "vietmap",
                    vehicle: payload.vehicle || currentVehicleMode || "car",
                    traffic_dist: payload.traffic_dist !== undefined ? payload.traffic_dist : "-- M",
                    traffic_light: payload.traffic_light !== undefined ? payload.traffic_light : "none",
                    arrow: arrow,
                    lane: lane
                });
                const signature = params.toString();
                const now = Date.now();
                if (payload.auto && signature === lastMochiNavSignature && now - lastMochiNavSentAt < 1000) return;
                lastMochiNavSignature = signature;
                lastMochiNavSentAt = now;
                await fetch('/api/nav?' + signature);
                showToast("✓ Đã gửi sang Mochi!");
            } catch (e) {
                console.error("Gửi thất bại:", e);
            }
        }

        function sendFromMap() {
            if (!destPos) {
                alert("Bác vui lòng chạm chọn một điểm đến trên bản đồ trước nhé!");
                return;
            }
            updateActiveStep(currentStepIdx);
            showToast("✓ Đã gửi sang Mochi!");
        }

        /* ── THEO DÕI GPS XE CHẠY THẬT (REAL DRIVE) ── */
        function toggleRealGpsDrive() {
            const btn = document.getElementById('btn-real-gps');
            const desc = document.getElementById('gps-desc-text');
            const navBadge = document.getElementById('nav-mode-badge');

            if (realGpsWatchId !== null) {
                // STOP
                navigator.geolocation.clearWatch(realGpsWatchId);
                realGpsWatchId = null;
                btn.classList.remove('active-gps');
                desc.innerText = "Theo dõi GPS iPhone liên tục";
                if (navBadge) navBadge.innerText = 'GPS HUD';
                showToast("⏹ Đã dừng theo dõi GPS");
            } else {
                // START
                if (!navigator.geolocation) {
                    alert("Trình duyệt không hỗ trợ Geolocation.");
                    return;
                }
                btn.classList.add('active-gps');
                desc.innerText = "🔴 ĐANG THEO DÕI XE CHẠY...";
                if (navBadge) navBadge.innerText = '🔴 LIVE GPS';
                showToast("🛰️ Bắt đầu theo dõi GPS thật!");

                realGpsWatchId = navigator.geolocation.watchPosition(pos => {
                    const lat = pos.coords.latitude;
                    const lng = pos.coords.longitude;
                    setUserPosition(lat, lng, false);

                    // Speed from GPS
                    let spd = 0;
                    if (pos.coords.speed !== null && pos.coords.speed >= 0) {
                        spd = Math.round(pos.coords.speed * 3.6); // m/s -> km/h
                    }
                    currentSpeed = spd;
                    renderSpeedGauge(spd);
                    document.getElementById('lbl-speed-val').innerText = spd + ' km/h';
                    checkOverspeed();

                    // Check distance to next turn maneuver
                    let distToManeuver = null;
                    if (navigationSteps && navigationSteps.length > 0) {
                        // Find closest maneuver step to keep in sync
                        let bestIdx = currentStepIdx;
                        let minDist = 999999;
                        for (let sIdx = 0; sIdx < navigationSteps.length; sIdx++) {
                            const stLoc = navigationSteps[sIdx].location;
                            if (stLoc) {
                                const d = getDistanceMeters([lat, lng], stLoc);
                                if (d < minDist) {
                                    minDist = d;
                                    bestIdx = sIdx;
                                }
                            }
                        }
                        if (bestIdx > currentStepIdx && minDist < 120) {
                            currentStepIdx = bestIdx;
                        }

                        const nextStepIdx = currentStepIdx + 1;
                        if (nextStepIdx < navigationSteps.length && navigationSteps[nextStepIdx].location) {
                            distToManeuver = Math.round(getDistanceMeters([lat, lng], navigationSteps[nextStepIdx].location));
                            if (distToManeuver < 45) {
                                currentStepIdx++;
                                showToast(`🔄 ${navigationSteps[currentStepIdx].instruction}`);
                            }
                        }
                    }

                    updateActiveStep(currentStepIdx, distToManeuver);

                }, err => {
                    console.warn("GPS watch error:", err);
                }, { enableHighAccuracy: true, maximumAge: 1000, timeout: 5000 });
            }
        }

        /* ── MÔ PHỎNG LỘ TRÌNH CHI TIẾT TỪNG CHẶNG (STEP-BY-STEP SIMULATION ENGINE) ── */
        let simStepIdx = 0;
        let simStepPhase = 0; // 0: cruising, 1: approaching turn (countdown), 2: turning
        let simSpeedMult = 1;

        function toggleSimulatedDrive() {
            const btn = document.getElementById('btn-sim-drive');
            const desc = document.getElementById('sim-desc-text');
            const navBadge = document.getElementById('nav-mode-badge');
            const ctrlBar = document.getElementById('sim-controls-bar');

            if (simTimer !== null) {
                // STOP
                stopSimDrive();
                showToast("⏹ Đã dừng mô phỏng");
            } else {
                // START
                if (!navigationSteps || navigationSteps.length === 0) {
                    alert("Bác vui lòng chọn một điểm đến trước để có lộ trình mô phỏng nhé!");
                    return;
                }

                btn.classList.add('active-sim');
                desc.innerText = "🔴 ĐANG CHẠY MÔ PHỎNG...";
                if (navBadge) navBadge.innerText = '🎮 DEMO DRIVE';
                if (ctrlBar) ctrlBar.style.display = 'flex';
                showToast("🏎️ Bắt đầu mô phỏng chi tiết từng chặng!");

                simStepIdx = 0;
                simStepPhase = 0;

                runSimStep();
            }
        }

        function runSimStep() {
            if (simTimer !== null) clearInterval(simTimer);
            updateSimInterval();
        }

        function updateSimInterval() {
            if (simTimer !== null) clearInterval(simTimer);
            const intervalMs = Math.round(1400 / simSpeedMult);

            simTimer = setInterval(() => {
                if (!navigationSteps || simStepIdx >= navigationSteps.length) {
                    stopSimDrive();
                    showToast("🏁 Đã đến nơi an toàn!");
                    return;
                }

                const curStep = navigationSteps[simStepIdx];
                const isLast = (simStepIdx >= navigationSteps.length - 1);
                const nextStep = isLast ? curStep : navigationSteps[simStepIdx + 1];

                // Update simulation control bar progress
                const progressTxt = document.getElementById('sim-progress-txt');
                if (progressTxt) progressTxt.innerText = `Chặng ${simStepIdx + 1} / ${navigationSteps.length}`;

                const stepDist = curStep.distanceM || 150;

                if (isLast) {
                    currentSpeed = 0;
                    renderSpeedGauge(0);
                    if (curStep.location && lMap) {
                        userPos = curStep.location;
                        if (lUserMarker) lUserMarker.setLatLng(userPos);
                        lMap.panTo(userPos, { animate: true });
                    }
                    updateActiveStep(simStepIdx, 0);
                    stopSimDrive();
                    showToast("🏁 Đã đến nơi an toàn: " + (selectedRoadName || curStep.name));
                    return;
                }

                const nameLower = (curStep.name || '').toLowerCase();
                const isHighway = nameLower.includes('quốc lộ') || nameLower.includes('ql') || nameLower.includes('cao tốc') || nameLower.includes('ct');

                // Dynamic sub-phases based on step distance for natural deceleration and countdown
                let phases = [];
                if (stepDist >= 5000) {
                    // Long highway (e.g. 5km - 45km)
                    phases = [
                        { ratio: 0.0, dist: stepDist, spd: isHighway ? 78 : 60 },
                        { ratio: 0.4, dist: Math.round(stepDist * 0.5), spd: isHighway ? 80 : 60 },
                        { ratio: 0.8, dist: 800, spd: 65 },
                        { ratio: 0.95, dist: 150, spd: 40 },
                        { ratio: 1.0, dist: 35, spd: 24 }
                    ];
                } else if (stepDist >= 1000) {
                    // Medium road (1km - 5km)
                    phases = [
                        { ratio: 0.0, dist: stepDist, spd: isHighway ? 68 : 50 },
                        { ratio: 0.5, dist: Math.round(stepDist * 0.45), spd: 48 },
                        { ratio: 0.85, dist: 120, spd: 35 },
                        { ratio: 1.0, dist: 35, spd: 22 }
                    ];
                } else if (stepDist >= 300) {
                    // Short street (300m - 1000m)
                    phases = [
                        { ratio: 0.0, dist: stepDist, spd: 45 },
                        { ratio: 0.6, dist: Math.round(stepDist * 0.35), spd: 35 },
                        { ratio: 1.0, dist: 30, spd: 22 }
                    ];
                } else {
                    // Small alley / quick corner (< 300m)
                    phases = [
                        { ratio: 0.0, dist: stepDist, spd: 35 },
                        { ratio: 1.0, dist: Math.min(25, Math.round(stepDist * 0.4)), spd: 22 }
                    ];
                }

                if (simStepPhase < phases.length) {
                    const p = phases[simStepPhase];

                    // Interpolate car position smoothly along this step towards the turn
                    if (curStep.location && nextStep.location) {
                        const r = p.ratio;
                        userPos = [
                            curStep.location[0] * (1 - r) + nextStep.location[0] * r,
                            curStep.location[1] * (1 - r) + nextStep.location[1] * r
                        ];
                        if (lUserMarker) lUserMarker.setLatLng(userPos);
                        if (lMap && (simStepPhase === 0 || simStepPhase === phases.length - 1)) {
                            lMap.panTo(userPos, { animate: true });
                        }
                    }

                    currentSpeed = Math.min(currentLimit, p.spd + Math.floor(Math.random() * 3));
                    renderSpeedGauge(currentSpeed);
                    checkOverspeed();

                    updateActiveStep(simStepIdx, p.dist);
                    simStepPhase++;

                } else {
                    // Turn maneuver executed at intersection!
                    if (nextStep.location) {
                        userPos = nextStep.location;
                        if (lUserMarker) lUserMarker.setLatLng(userPos);
                        if (lMap) lMap.panTo(userPos, { animate: true });
                    }

                    showToast(`🔄 Đã rẽ: ${nextStep.instruction}`);

                    // Advance to next step!
                    simStepIdx++;
                    simStepPhase = 0;
                    if (progressTxt) progressTxt.innerText = `Chặng ${simStepIdx + 1} / ${navigationSteps.length}`;

                    if (simStepIdx < navigationSteps.length) {
                        updateActiveStep(simStepIdx, navigationSteps[simStepIdx].distanceM);
                    }
                }

            }, intervalMs);
        }

        function stopSimDrive() {
            if (simTimer !== null) {
                clearInterval(simTimer);
                simTimer = null;
            }
            currentSpeed = 0;
            renderSpeedGauge(0);
            sendToMochi({ speed: 0 });
            const btn = document.getElementById('btn-sim-drive');
            const desc = document.getElementById('sim-desc-text');
            const navBadge = document.getElementById('nav-mode-badge');
            const ctrlBar = document.getElementById('sim-controls-bar');
            if (btn) btn.classList.remove('active-sim');
            if (desc) desc.innerText = "Chạy demo xe ảo trên đường";
            if (navBadge) navBadge.innerText = 'GPS HUD';
            if (ctrlBar) ctrlBar.style.display = 'none';
        }

        function simSkipStep() {
            if (navigationSteps && simStepIdx < navigationSteps.length - 1) {
                simStepIdx++;
                simStepPhase = 0;
                updateActiveStep(simStepIdx, navigationSteps[simStepIdx].distanceM);
                showToast(`⏭ Chuyển sang chặng ${simStepIdx + 1}`);
            }
        }

        function toggleSimSpeed() {
            if (simSpeedMult === 1) simSpeedMult = 2;
            else if (simSpeedMult === 2) simSpeedMult = 4;
            else simSpeedMult = 1;
            const btn = document.getElementById('btn-sim-speed');
            if (btn) btn.innerText = `⏩ ${simSpeedMult}x`;
            showToast(`Tốc độ mô phỏng: ${simSpeedMult}x`);
            if (simTimer !== null) updateSimInterval();
        }

        /* ── PRESETS CHO TEST NHANH ── */
        const presets = [
            { road: "Đ. Nguyễn Trãi", inst: "Đi thẳng qua ngã tư", dist: "1.5 km", distM: 1500, spd: 50, limit: 50, arrow: "↑", arrowCode: "straight", lane: 1, eta: "11:45", tfDist: "-- M", light: "none" },
            { road: "Đ. Lê Lợi", inst: "Chuẩn bị rẽ phải", dist: "250 m", distM: 250, spd: 35, limit: 50, arrow: "➜", arrowCode: "right", lane: 2, eta: "11:42", tfDist: "120 M", light: "green" },
            { road: "Vòng Xoay Bến Thành", inst: "Rẽ trái tại vòng xuyến", dist: "80 m", distM: 80, spd: 25, limit: 40, arrow: "⬅", arrowCode: "left", lane: 0, eta: "11:40", tfDist: "40 M", light: "yellow" },
            { road: "Cầu Kênh Tẻ", inst: "Quay đầu xe bên dưới cầu", dist: "45 m", distM: 45, spd: 20, limit: 40, arrow: "↶", arrowCode: "uturn", lane: 0, eta: "11:38", tfDist: "15 M", light: "red" },
            { road: "Đại lộ Nguyễn Văn Linh", inst: "CẢNH BÁO: QUÁ TỐC ĐỘ!", dist: "600 m", distM: 600, spd: 78, limit: 50, arrow: "⚠️", arrowCode: "straight", lane: 1, eta: "11:36", tfDist: "-- M", light: "none" },
            { road: "Tara Chung Cư", inst: "Đã đến nơi an toàn!", dist: "0 m", distM: 0, spd: 0, limit: 50, arrow: "🏁", arrowCode: "arrive", lane: 1, eta: "11:35", tfDist: "-- M", light: "none" },
            { road: "Nhánh ven kênh", inst: "Chếch trái vào nhánh", dist: "300 m", distM: 300, spd: 42, limit: 50, arrow: "↖", arrowCode: "slight_left", lane: 0, eta: "11:33", tfDist: "-- M", light: "none" },
            { road: "Cầu Kênh Tẻ", inst: "Chếch phải vào nhánh", dist: "220 m", distM: 220, spd: 38, limit: 50, arrow: "↗", arrowCode: "slight_right", lane: 2, eta: "11:32", tfDist: "-- M", light: "none" },
            { road: "Vòng xoay Bến Thành", inst: "Vào bùng binh, đi theo lối ra", dist: "80 m", distM: 80, spd: 25, limit: 40, arrow: "↺", arrowCode: "roundabout", lane: 1, eta: "11:31", tfDist: "40 M", light: "yellow" }
        ];

        function sendPreset(idx) {
            const p = presets[idx];
            selectedRoadName = p.road;
            currentInstruction = p.inst;
            currentDistance = p.dist;
            currentSpeed = p.spd;
            currentLimit = p.limit;
            currentArrow = p.arrow;
            currentEta = p.eta;

            document.getElementById('prev-road').innerText = p.road;
            document.getElementById('prev-inst').innerText = p.inst;
            document.getElementById('prev-dist').innerText = p.dist;
            document.getElementById('prev-arrow').innerText = p.arrow;
            document.getElementById('prev-limit-val').innerText = p.limit;
            document.getElementById('prev-eta').innerText = '⏱ Dự kiến: ' + p.eta;

            // Vietmap Cockpit Elements
            const vmArrow = document.getElementById('vm-turn-arrow');
            const vmDist = document.getElementById('vm-dist-val');
            const vmRoad = document.getElementById('vm-road-name');
            const vmLim = document.getElementById('vm-limit-val');
            const vmSpd = document.getElementById('vm-speed-val');
            const vmEta = document.getElementById('vm-eta-val');
            if (vmArrow) vmArrow.innerText = p.arrow;
            if (vmDist) vmDist.innerText = p.dist;
            if (vmRoad) vmRoad.innerText = p.road;
            if (vmLim) vmLim.innerText = p.limit;
            if (vmSpd) vmSpd.innerText = p.spd;
            if (vmEta) vmEta.innerText = 'ETA ' + p.eta;

            // Lane guidance on web
            const laneL = document.getElementById('vm-lane-left');
            const laneM = document.getElementById('vm-lane-mid');
            const laneR = document.getElementById('vm-lane-right');
            if (laneL) laneL.className = 'vm-lane-arrow' + (p.lane === 0 ? ' active' : '');
            if (laneM) laneM.className = 'vm-lane-arrow' + (p.lane === 1 ? ' active' : '');
            if (laneR) laneR.className = 'vm-lane-arrow' + (p.lane === 2 ? ' active' : '');

            const tfDistEl = document.getElementById('vm-traffic-dist');
            if (tfDistEl) tfDistEl.innerText = p.tfDist || "-- M";

            const lRed = document.getElementById('vm-light-red');
            const lYel = document.getElementById('vm-light-yellow');
            const lGrn = document.getElementById('vm-light-green');
            if (lRed) lRed.classList.toggle('active', p.light === 'red');
            if (lYel) lYel.classList.toggle('active', p.light === 'yellow');
            if (lGrn) lGrn.classList.toggle('active', p.light === 'green');

            renderSpeedGauge(p.spd);
            updateDistanceProgress(p.distM);
            checkOverspeed();

            sendToMochi({
                road: p.road,
                instruction: p.inst,
                distance: p.dist,
                speed: p.spd,
                speed_limit: p.limit,
                eta: p.eta,
                style: activeHudStyle,
                vehicle: currentVehicleMode,
                traffic_dist: p.tfDist || "-- M",
                traffic_light: p.light || "none",
                arrow: p.arrowCode,
                lane: p.lane
            });
        }

        
        /* ── VIETMAP & TESLA HUD SYNC & VIEW SWITCHER ── */
        function switchHudStyle(style) {
            activeHudStyle = style;
            const vmScreen = document.getElementById('vietmap-hud-screen');
            const teslaScreen = document.getElementById('hud-main-screen');
            const tabVm = document.getElementById('tab-vietmap');
            const tabTesla = document.getElementById('tab-tesla');
            const tabFullmap = document.getElementById('tab-fullmap');

            if (tabVm) tabVm.classList.remove('active');
            if (tabTesla) tabTesla.classList.remove('active');
            if (tabFullmap) tabFullmap.classList.remove('active');

            if (style === 'vietmap') {
                if (vmScreen) vmScreen.style.display = 'grid';
                if (teslaScreen) teslaScreen.style.display = 'none';
                if (tabVm) tabVm.classList.add('active');
                showToast("🚗 Đã đổi sang Vietmap Pro 3 Cột");
            } else if (style === 'tesla') {
                if (vmScreen) vmScreen.style.display = 'none';
                if (teslaScreen) teslaScreen.style.display = 'block';
                if (tabTesla) tabTesla.classList.add('active');
                showToast("⚡ Đã đổi sang Tesla Cockpit HUD");
            } else if (style === 'fullmap') {
                if (vmScreen) vmScreen.style.display = 'grid';
                if (teslaScreen) teslaScreen.style.display = 'none';
                if (tabFullmap) tabFullmap.classList.add('active');
                showToast("🗺️ Đã đổi Mochi sang Full Map Navigator");
            }
            sendToMochi({
                style: style,
                arrow: getArrowCode(currentArrow, currentInstruction),
                lane: (currentArrow === '↰' || currentArrow === 'left') ? 0 : ((currentArrow === '↱' || currentArrow === 'right') ? 2 : 1)
            });
        }

        function switchVehicleMode(veh) {
            currentVehicleMode = veh;
            const tabCar = document.getElementById('veh-car');
            const tabBike = document.getElementById('veh-bike');
            if (veh === 'bike') {
                if (tabCar) tabCar.classList.remove('active');
                if (tabBike) tabBike.classList.add('active');
                currentLimit = 50;
                showToast("🛵 Chế độ XE MÁY (tối đa 50 km/h)");
            } else {
                if (tabCar) tabCar.classList.add('active');
                if (tabBike) tabBike.classList.remove('active');
                currentLimit = 60;
                showToast("🚗 Chế độ Ô TÔ (tối đa 60 km/h)");
            }
            const limVal = document.getElementById('lbl-limit-val');
            if (limVal) limVal.innerText = currentLimit;
            renderSpeedLimitSign(currentLimit);
            sendToMochi({ vehicle: veh, speed_limit: currentLimit });
        }

        function updateVietmapHUD(spd, limit, arrow, distStr, etaStr, roadName, inst) {
            // Speed
            const spdEl = document.getElementById('vm-speed-val');
            if (spdEl) spdEl.innerText = spd;
            const limEl = document.getElementById('vm-limit-val');
            if (limEl) limEl.innerText = limit;

            // Overspeed check
            const isOver = (limit > 0 && spd > limit);
            const vmContainer = document.getElementById('vietmap-hud-screen');
            if (vmContainer) vmContainer.classList.toggle('overspeed', isOver);

            // Nav details
            const arrowEl = document.getElementById('vm-turn-arrow');
            const distEl = document.getElementById('vm-dist-val');
            const etaEl = document.getElementById('vm-eta-val');
            const roadEl = document.getElementById('vm-road-name');

            if (distEl) distEl.innerText = distStr || '-- m';
            if (etaEl) {
                const cleanEta = (etaStr || '').replace('⏱ Dự kiến: ', '').replace('ETA: ', '');
                etaEl.innerText = cleanEta ? 'ETA ' + cleanEta : 'ETA --:--';
            }
            if (roadEl) roadEl.innerText = roadName || 'Đang chờ tuyến đường...';

            // Maneuver Arrow & Lane Guidance Logic
            const laneL = document.getElementById('vm-lane-left');
            const laneM = document.getElementById('vm-lane-mid');
            const laneR = document.getElementById('vm-lane-right');

            const lowerInst = (inst || '').toLowerCase();
            if (lowerInst.includes('trái') || lowerInst.includes('left')) {
                if (arrowEl) arrowEl.innerText = '↰';
                if (laneL) { laneL.className = 'vm-lane-arrow active'; laneL.innerText = '↰'; }
                if (laneM) { laneM.className = 'vm-lane-arrow'; laneM.innerText = '↑'; }
                if (laneR) { laneR.className = 'vm-lane-arrow'; laneR.innerText = '↑'; }
            } else if (lowerInst.includes('phải') || lowerInst.includes('right')) {
                if (arrowEl) arrowEl.innerText = '↱';
                if (laneL) { laneL.className = 'vm-lane-arrow'; laneL.innerText = '↑'; }
                if (laneM) { laneM.className = 'vm-lane-arrow'; laneM.innerText = '↑'; }
                if (laneR) { laneR.className = 'vm-lane-arrow active'; laneR.innerText = '↱'; }
            } else if (lowerInst.includes('quay') || lowerInst.includes('uturn')) {
                if (arrowEl) arrowEl.innerText = '↶';
                if (laneL) { laneL.className = 'vm-lane-arrow active'; laneL.innerText = '↶'; }
                if (laneM) { laneM.className = 'vm-lane-arrow'; laneM.innerText = '↑'; }
                if (laneR) { laneR.className = 'vm-lane-arrow'; laneR.innerText = '↑'; }
            } else {
                if (arrowEl) arrowEl.innerText = arrow || '↑';
                if (laneL) { laneL.className = 'vm-lane-arrow'; laneL.innerText = '↰'; }
                if (laneM) { laneM.className = 'vm-lane-arrow active'; laneM.innerText = '↑'; }
                if (laneR) { laneR.className = 'vm-lane-arrow'; laneR.innerText = '↱'; }
            }
        }

        // Live Clock for Telemetry
        function updateLiveClock() {
            const timeEl = document.getElementById('vm-tele-time');
            if (timeEl) {
                timeEl.innerText = new Date().toLocaleTimeString('vi-VN', { hour: '2-digit', minute: '2-digit' });
            }
        }
        setInterval(updateLiveClock, 1000);

        window.addEventListener('load', initMap);
    </script>
</body>
</html>"""

def _yt_norm(s):
    s = unicodedata.normalize('NFD', (s or '').lower().replace('đ', 'd').replace('Đ', 'D'))
    s = ''.join(c for c in s if unicodedata.category(c) != 'Mn')
    return re.sub(r'[^a-z0-9\s]+', ' ', s).strip()

_YT_STOP_WORDS = {
    'cua', 'bai', 'hat', 'nhac', 'ca', 'khuc', 'ban', 'mo', 'bat', 'phat', 'nghe', 'tim',
    'cho', 'toi', 'minh', 'giup', 'gium', 'official', 'mv', 'audio', 'video', 'lyrics', 'lyric', 'ft', 'feat'
}

def _score_youtube_candidates(q_str, entries):
    q_norm = _yt_norm(q_str)
    q_tokens = [w for w in q_norm.split() if w not in _YT_STOP_WORDS and len(w) >= 2]
    if not q_tokens:
        q_tokens = [w for w in q_norm.split() if w]
    q_lower = q_str.lower()
    wants_beat = any(w in q_lower for w in ['beat', 'karaoke', 'instrumental', 'không lời', 'khong loi', 'backing track'])

    disqualifiers = [
        'beat', 'karaoke', 'instrumental', 'không lời', 'khong loi',
        'tone nam', 'tone nữ', 'tone nu', 'hạ tone', 'tăng tone',
        'backing track', 'guitar tab', 'piano tutorial', 'hướng dẫn',
        'parody', 'reaction', 'phim ca nhạc', 'lala school', 'trailer',
        'review phim', 'audiobook', 'sách nói', 'sach noi'
    ]

    scored = []
    for e in entries:
        t_raw = e.get('title') or ''
        u_raw = e.get('uploader') or ''
        t = t_raw.lower()
        u = u_raw.lower()
        d = e.get('duration') or 0

        if not wants_beat and any(bad in t for bad in disqualifiers):
            continue

        combined_norm = f"{_yt_norm(t_raw)} {_yt_norm(u_raw)}"
        title_norm = _yt_norm(t_raw)
        combined_words = set(combined_norm.split())
        hits = sum(1 for tok in q_tokens if tok in combined_words or (len(tok) >= 4 and tok in combined_norm))
        match_ratio = (hits / max(1, len(q_tokens))) if q_tokens else 1.0

        score = int(match_ratio * 240)
        core_phrase = ' '.join(q_tokens[:4]) if len(q_tokens) >= 2 else (q_tokens[0] if q_tokens else '')
        if core_phrase and core_phrase in title_norm:
            score += 120
        elif len(q_tokens) >= 3 and ' '.join(q_tokens[:2]) in title_norm:
            score += 65

        if len(q_tokens) >= 2 and match_ratio < 0.34:
            score -= 260

        is_relevant = (len(q_tokens) <= 1 or match_ratio >= 0.45)

        if not wants_beat:
            if is_relevant:
                if 'official audio' in t:
                    score += 150
                elif 'official music video' in t or 'official mv' in t or 'mv chính thức' in t:
                    score += 75
                elif 'official video' in t or 'music video' in t:
                    score += 60
                elif 'lyric video' in t or 'lyrics video' in t or '[lyrics]' in t or '(lyrics)' in t or 'vietsub' in t or 'lyrics' in t:
                    score += 70

                if 'topic' in u:
                    score += 110
                elif 'official' in u:
                    score += 40

            if 90 <= d <= 420:
                score += 20
            elif d > 900:
                score -= 50
            elif 0 < d < 60:
                score -= 80
        else:
            if 'karaoke' in t or 'beat' in t or 'instrumental' in t:
                score += 200
            if 'tone nam' in q_lower and 'tone nam' in t:
                score += 50
            if 'tone nữ' in q_lower and ('tone nữ' in t or 'tone nu' in t):
                score += 50
            if 'beat chuẩn' in t or 'beat gốc' in t:
                score += 30

        scored.append((score, match_ratio, e))

    scored.sort(key=lambda x: (x[0], x[1]), reverse=True)
    return scored

def select_best_video(query_str, ydl_instance):
    """
    Intelligently scores and selects the cleanest, most title-relevant official vocal music release.
    Falls back to core song title if an extra/misheard artist keyword yields low title overlap.
    """
    q = (query_str or '').strip()
    if not q:
        return None

    try:
        ydl_flat = yt_dlp.YoutubeDL({'quiet': True, 'extract_flat': 'in_playlist', 'noplaylist': True})
        res = ydl_flat.extract_info(f"ytsearch5:{q}", download=False)
        entries = [e for e in (res or {}).get('entries', []) if e]
        scored = _score_youtube_candidates(q, entries) if entries else []

        best_ratio = scored[0][1] if scored else 0.0
        # If YouTube top 5 didn't match song words (< 50%), retry with stripped artist/filler tail
        if best_ratio < 0.50:
            q_core = re.split(r'\b(?:của|cua|ft\.?|feat\.?|mr\.?|ms\.?)\b', q, maxsplit=1, flags=re.IGNORECASE)[0].strip()
            words_q = q.split()
            if (not q_core or len(q_core) == len(q)) and len(words_q) >= 4:
                q_core = ' '.join(words_q[:-2]).strip()
            if q_core and len(q_core.split()) >= 2 and q_core.lower() != q.lower():
                logging.info(f"Low title match ({best_ratio:.2f}) for '{q}'; retrying core song query '{q_core}'")
                res2 = ydl_flat.extract_info(f"ytsearch5:{q_core}", download=False)
                entries2 = [e for e in (res2 or {}).get('entries', []) if e]
                scored2 = _score_youtube_candidates(q_core, entries2) if entries2 else []
                if scored2 and (not scored or scored2[0][0] > scored[0][0] or scored2[0][1] > best_ratio + 0.15):
                    return scored2[0][2]

        if scored:
            return scored[0][2]
        if entries:
            return entries[0]
        return None
    except Exception as err:
        logging.error(f"Error in select_best_video for '{query_str}': {err}")
        return None

class YouTubeHandler(http.server.BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        logging.info("%s - %s", self.address_string(), format % args)

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query)

        if path == '/' or path == '/health':
            self.send_response(200)
            self.send_header('Content-Type', 'application/json; charset=utf-8')
            self.end_headers()
            self.wfile.write(json.dumps({
                'status': 'ok',
                'service': 'Mochi YouTube Audio Bridge & Payment Soundbox',
                'version': '2.0.0',
                'payment_endpoints': ['/payment_test', '/webhook/sepay', '/api/payment_notify']
            }).encode('utf-8'))
            return

        elif path == '/payment_test':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.end_headers()
            self.wfile.write(HTML_TEST_PAGE.encode('utf-8'))
            return

        elif path == '/mochi' or path == '/mascot':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store')
            self.end_headers()
            self.wfile.write(HTML_MASCOT_PAGE.encode('utf-8'))
            return

        elif path == '/waze' or path == '/nav':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.end_headers()
            self.wfile.write(HTML_WAZE_PAGE.encode('utf-8'))
            return

        elif path == '/leaflet.js' or path == '/static/leaflet.js':
            js_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'static', 'leaflet.js')
            if os.path.exists(js_file):
                self.send_response(200)
                self.send_header('Content-Type', 'application/javascript; charset=utf-8')
                self.send_header('Cache-Control', 'public, max-age=86400')
                self.end_headers()
                with open(js_file, 'rb') as f:
                    self.wfile.write(f.read())
                return
            self.send_error(404, 'Leaflet JS not found')
            return

        elif path == '/leaflet.css' or path == '/static/leaflet.css':
            css_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'static', 'leaflet.css')
            if os.path.exists(css_file):
                self.send_response(200)
                self.send_header('Content-Type', 'text/css; charset=utf-8')
                self.send_header('Cache-Control', 'public, max-age=86400')
                self.end_headers()
                with open(css_file, 'rb') as f:
                    self.wfile.write(f.read())
                return
            self.send_error(404, 'Leaflet CSS not found')
            return

        elif path == '/api/reverse':
            # Server-side reverse geocoding (proxies Nominatim to avoid CORS)
            lat = query.get('lat', [''])[0]
            lon = query.get('lon', [''])[0]
            if not lat or not lon:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(b'{"error":"lat and lon required"}')
                return
            try:
                nom_url = f"https://nominatim.openstreetmap.org/reverse?format=jsonv2&lat={lat}&lon={lon}&zoom=18&addressdetails=1"
                nom_req = urllib.request.Request(nom_url, headers={"User-Agent": "MochiHUD/1.0"})
                with urllib.request.urlopen(nom_req, timeout=10) as resp:
                    nom_data = json.load(resp)
                result = {
                    "display_name": nom_data.get("display_name", ""),
                    "address": nom_data.get("address", {}),
                    "name": nom_data.get("name", ""),
                }
                payload = json.dumps(result, ensure_ascii=False).encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.send_header('Access-Control-Allow-Origin', '*')
                self.send_header('Content-Length', str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            except Exception as e:
                logging.error("Reverse geocode error: %s", e)
                self.send_response(500)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": str(e)}).encode('utf-8'))
            return

        elif path == '/api/search':
            # Server-side forward geocoding (proxies Nominatim to avoid CORS)
            q = query.get('q', [''])[0]
            limit_val = query.get('limit', ['6'])[0]
            if not q:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(b'{"error":"q required"}')
                return
            try:
                encoded_q = urllib.parse.quote(q)
                nom_url = f"https://nominatim.openstreetmap.org/search?format=json&q={encoded_q}&countrycodes=vn&limit={limit_val}&addressdetails=1"
                nom_req = urllib.request.Request(nom_url, headers={"User-Agent": "MochiHUD/1.0 (mochi@ai.local)"})
                with urllib.request.urlopen(nom_req, timeout=10) as resp:
                    nom_data = json.load(resp)
                payload = json.dumps(nom_data, ensure_ascii=False).encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.send_header('Access-Control-Allow-Origin', '*')
                self.send_header('Content-Length', str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            except Exception as e:
                logging.error("Forward geocode error: %s", e)
                self.send_response(500)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": str(e)}).encode('utf-8'))
            return

        elif path == '/api/traffic-signals':
            raw_points = query.get('points', [''])[0]
            points = []
            try:
                for raw_point in raw_points.split(';')[:24]:
                    lng, lat = (float(value) for value in raw_point.split(',', 1))
                    if not (-90 <= lat <= 90 and -180 <= lng <= 180):
                        raise ValueError('coordinate outside range')
                    points.append((lat, lng))
            except (TypeError, ValueError):
                points = []
            if not points:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(b'{"error":"valid route points are required"}')
                return
            try:
                payload = json.dumps({'signals': get_osm_traffic_signals(points)}, ensure_ascii=False).encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.send_header('Access-Control-Allow-Origin', '*')
                self.send_header('Content-Length', str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            except Exception as e:
                logging.warning('OSM traffic-signal lookup failed: %s', e)
                self.send_response(502)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(b'{"error":"traffic-signal source unavailable"}')
            return

        elif path == '/api/speed-cameras':
            raw_points = query.get('points', [''])[0]
            points = []
            try:
                for raw_point in raw_points.split(';')[:24]:
                    lng, lat = (float(value) for value in raw_point.split(',', 1))
                    if not (-90 <= lat <= 90 and -180 <= lng <= 180):
                        raise ValueError('coordinate outside range')
                    points.append((lat, lng))
            except (TypeError, ValueError):
                points = []
            if not points:
                self.send_error(400, 'valid route points are required')
                return
            try:
                payload = json.dumps({'cameras': get_osm_speed_cameras(points)}, ensure_ascii=False).encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.send_header('Access-Control-Allow-Origin', '*')
                self.send_header('Content-Length', str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            except Exception as e:
                logging.warning('OSM speed-camera lookup failed: %s', e)
                self.send_error(502, 'speed-camera source unavailable')
            return

        elif path == '/api/route':
            # Server-side VIETMAP proxy. The key remains on this machine and is
            # never returned to the browser or the ESP32.
            start = query.get('start', [''])[0]
            end = query.get('end', [''])[0]
            if not start or not end or not VIETMAP_API_KEY:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(b'{"error":"start/end coordinates and VIETMAP service key are required"}')
                return
            try:
                start_lng, start_lat = (float(value) for value in start.split(',', 1))
                end_lng, end_lat = (float(value) for value in end.split(',', 1))
                vietmap_query = urllib.parse.urlencode([
                    ('apikey', VIETMAP_API_KEY), ('vehicle', 'car'), ('points_encoded', 'true'),
                    ('point', f'{start_lat:.6f},{start_lng:.6f}'),
                    ('point', f'{end_lat:.6f},{end_lng:.6f}'),
                ])
                vietmap_url = 'https://maps.vietmap.vn/api/route/v4?' + vietmap_query
                ctx = ssl._create_unverified_context()
                vietmap_req = urllib.request.Request(vietmap_url, headers={"User-Agent": "MochiHUD/1.0"})
                with urllib.request.urlopen(vietmap_req, context=ctx, timeout=12) as resp:
                    route_data = normalize_vietmap_route(json.load(resp))
                payload = json.dumps(route_data, ensure_ascii=False).encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.send_header('Access-Control-Allow-Origin', '*')
                self.send_header('Content-Length', str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            except Exception as e:
                logging.error("VIETMAP Route proxy error: %s", e)
                self.send_response(500)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": str(e)}).encode('utf-8'))
            return

        elif path == '/api/mochi/emotion':
            # Remote mascot control.  Keep the accepted vocabulary small so a
            # public browser cannot inject arbitrary display strings.
            requested = query.get('emotion', ['neutral'])[0].strip().lower()
            allowed = {
                'neutral', 'happy', 'laughing', 'thinking', 'curious',
                'sleepy', 'relaxed', 'wink', 'loving', 'cool', 'surprised',
                'shy', 'sad', 'angry',
            }
            if requested not in allowed:
                self.send_error(400, 'unsupported emotion')
                return
            send_mochi_udp({'cmd': 'emotion', 'emotion': requested})
            payload = json.dumps({'status': 'ok', 'emotion': requested}, ensure_ascii=False).encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'application/json; charset=utf-8')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Content-Length', str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return

        elif path == '/api/nav':
            instruction = query.get('instruction', ['Đi thẳng'])[0]
            road = query.get('road', ['Đ. Nguyễn Trãi'])[0]
            distance = query.get('distance', ['200 m'])[0]
            raw_spd = query.get('speed', ['45'])[0]
            raw_lim = query.get('speed_limit', [query.get('limit', ['50'])[0]])[0]
            eta = query.get('eta', ['11:45'])[0]
            style = query.get('style', ['vietmap'])[0]
            vehicle = query.get('vehicle', ['car'])[0]
            traffic_dist = query.get('traffic_dist', ['-- M'])[0]
            traffic_light = query.get('traffic_light', ['none'])[0]
            arrow = query.get('arrow', ['straight'])[0]
            try:
                lane = int(query.get('lane', ['1'])[0])
            except Exception:
                lane = 1

            try:
                speed = int(re.sub(r'[^\d]', '', raw_spd)) if raw_spd else 45
            except:
                speed = 45
            try:
                speed_limit = int(re.sub(r'[^\d]', '', raw_lim)) if raw_lim else 50
            except:
                speed_limit = 50

            payload = {
                "cmd": "nav",
                "instruction": instruction,
                "road": road,
                "distance": distance,
                "speed": speed,
                "speed_limit": speed_limit,
                "eta": eta,
                "style": style,
                "vehicle": vehicle,
                "traffic_dist": traffic_dist,
                "traffic_light": traffic_light,
                "arrow": arrow,
                "lane": lane
            }
            send_mochi_udp(payload)
            self.send_response(200)
            self.send_header('Content-Type', 'application/json; charset=utf-8')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            self.wfile.write(json.dumps({"status": "ok", "nav": payload}, ensure_ascii=False).encode('utf-8'))
            return

        elif path == '/api/bank_notify' or path == '/api/payment_notify':
            text = query.get('text', [''])[0]
            title = query.get('title', [''])[0]
            raw_amt = query.get('amount', [''])[0]
            if raw_amt:
                clean = re.sub(r'[^\d]', '', raw_amt)
                amount = int(clean) if clean else 0
                sender = query.get('sender', ['Khách hàng'])[0]
                content = query.get('content', ['Chuyển khoản TPBank'])[0]
            else:
                amount, sender, content = parse_vietnamese_bank_notification(text, title)
            if amount > 0:
                spoken_amt = format_vietnamese_amount(amount)
                speech_text = f"Tài khoản TPBank vừa nhận được {spoken_amt} đồng từ {sender}"
                audio_url = f"http://{get_lan_ip()}:{PORT}/tts?text=" + urllib.parse.quote(speech_text)
                formatted_amt = f"{amount:,.0f}".replace(",", ".")
                payload = {
                    "cmd": "payment",
                    "amount": f"+{formatted_amt} đ",
                    "sender": sender,
                    "content": content,
                    "audio_url": audio_url
                }
                send_mochi_udp(payload)
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.end_headers()
                self.wfile.write(json.dumps({"status": "ok", "amount": amount, "sender": sender, "spoken": speech_text}, ensure_ascii=False).encode('utf-8'))
            else:
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.end_headers()
                self.wfile.write(json.dumps({"status": "ignored", "reason": "No incoming amount found"}, ensure_ascii=False).encode('utf-8'))
            return

        elif path == '/tts':
            text = query.get('text', [''])[0]
            if not text:
                self.send_error(400, 'Missing text')
                return
            try:
                logging.info(f"Generating Vietnamese TTS: {text}")
                tts_url = 'https://translate.google.com/translate_tts?ie=UTF-8&client=tw-ob&tl=vi&q=' + urllib.parse.quote(text)
                req = urllib.request.Request(tts_url, headers={'User-Agent': 'Mozilla/5.0'})
                with urllib.request.urlopen(req, timeout=8) as resp:
                    audio_bytes = resp.read()

                self.send_response(200)
                self.send_header('Content-Type', 'audio/mpeg')
                self.send_header('Content-Length', str(len(audio_bytes)))
                self.send_header('Cache-Control', 'no-cache')
                self.end_headers()
                self.wfile.write(audio_bytes)
            except Exception as e:
                logging.error(f"TTS error: {e}")
                self.send_error(500, str(e))
            return

        elif path == '/search' or path == '/play':
            q = query.get('q', [''])[0]
            if not q:
                self.send_error(400, 'Missing search query q')
                return
            try:
                logging.info(f"Searching YouTube for: {q}")
                selected_entry = select_best_video(q, ydl)
                if not selected_entry:
                    self.send_error(404, 'No video found')
                    return

                video_id = selected_entry['id']
                title = selected_entry.get('title', q)
                duration = selected_entry.get('duration', 0)
                logging.info(f"Selected cleanest audio: '{title}' (ID: {video_id})")
                
                host = self.headers.get('Host', f'{LAN_IP}:{PORT}')
                proto = self.headers.get('X-Forwarded-Proto', 'http')
                stream_url = f"{proto}://{host}/stream?v={video_id}"
                
                response_data = {
                    'status': 'success',
                    'id': video_id,
                    'title': title,
                    'duration': duration,
                    'stream_url': stream_url
                }
                
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.send_header('Access-Control-Allow-Origin', '*')
                self.end_headers()
                self.wfile.write(json.dumps(response_data, ensure_ascii=False).encode('utf-8'))
            except Exception as e:
                logging.error(f"Search error: {e}")
                self.send_error(500, str(e))
            return

        elif path == '/stream':
            video_id = query.get('v', [''])[0]
            q = query.get('q', [''])[0]
            
            target_url = None
            title = "YouTube Audio"
            
            try:
                user_agent = None
                with yt_dlp.YoutubeDL(ydl_search_opts) as ydl_req:
                    if video_id:
                        info = ydl_req.extract_info(f"https://www.youtube.com/watch?v={video_id}", download=False)
                        target_url = info.get('url')
                        title = info.get('title', video_id)
                        user_agent = (info.get('http_headers') or {}).get('User-Agent')
                    elif q:
                        best = select_best_video(q, ydl_req)
                        if best:
                            video_id = best.get('id')
                            info = ydl_req.extract_info(f"https://www.youtube.com/watch?v={video_id}", download=False)
                            target_url = info.get('url')
                            title = info.get('title', q)
                            user_agent = (info.get('http_headers') or {}).get('User-Agent')

                if not target_url:
                    self.send_error(404, 'Could not resolve audio stream')
                    return

                logging.info(f"Streaming MP3: {title}")
                self.send_response(200)
                self.send_header('Content-Type', 'audio/mpeg')
                self.send_header('Cache-Control', 'no-cache')
                self.send_header('Connection', 'close')
                self.end_headers()

                ffmpeg_cmd = [
                    FFMPEG_PATH,
                    '-nostdin',
                    '-hide_banner',
                    '-loglevel', 'error',
                    '-reconnect', '1',
                    '-reconnect_streamed', '1',
                    '-reconnect_delay_max', '5',
                ]
                if user_agent:
                    ffmpeg_cmd.extend(['-user_agent', user_agent])
                ffmpeg_cmd.extend([
                    '-i', target_url,
                    '-vn',
                    '-acodec', 'libmp3lame',
                    '-b:a', '128k',
                    '-ar', '24000',
                    '-ac', '1',
                    '-f', 'mp3',
                    'pipe:1'
                ])

                proc = subprocess.Popen(
                    ffmpeg_cmd,
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    bufsize=65536
                )

                total_sent = 0
                try:
                    while True:
                        chunk = proc.stdout.read(4096)
                        if not chunk:
                            break
                        self.wfile.write(chunk)
                        self.wfile.flush()
                        total_sent += len(chunk)
                except (BrokenPipeError, ConnectionResetError):
                    logging.info(f"Client disconnected while streaming ({total_sent}B): {title}")
                finally:
                    proc.terminate()
                    try:
                        proc.wait(timeout=1)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                    err_out = ""
                    try:
                        err_out = proc.stderr.read().decode('utf-8', 'ignore').strip()
                    except Exception:
                        pass
                    if total_sent == 0:
                        logging.error(f"Stream sent 0 bytes (rc={proc.returncode}, ffmpeg={FFMPEG_PATH}): {err_out}")
                    else:
                        logging.info(f"Finished MP3 stream ({total_sent} bytes): {title}")
            except Exception as e:
                logging.error(f"Stream error: {e}")
            return

        self.send_error(404, 'Not found')

    def do_POST(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        try:
            content_length = int(self.headers.get('Content-Length', 0))
        except ValueError:
            self.send_error(400, 'Invalid Content-Length')
            return
        if content_length < 0 or content_length > MAX_REQUEST_BODY:
            self.send_error(413, 'Request body too large')
            return
        body = self.rfile.read(content_length).decode('utf-8') if content_length > 0 else ""

        req_json = {}
        if body:
            try:
                req_json = json.loads(body)
            except Exception:
                pass

        host = self.headers.get('Host', f'192.168.1.77:{PORT}')

        if path == '/api/nav':
            instruction = req_json.get('instruction', 'Đi thẳng')
            road = req_json.get('road', 'Đ. Nguyễn Trãi')
            distance = req_json.get('distance', '200 m')
            speed = int(req_json.get('speed', 45))
            speed_limit = int(req_json.get('speed_limit', 50))
            eta = req_json.get('eta', '11:45')
            style = req_json.get('style', 'vietmap')
            vehicle = req_json.get('vehicle', 'car')
            traffic_dist = req_json.get('traffic_dist', '-- M')
            traffic_light = req_json.get('traffic_light', 'none')
            arrow = req_json.get('arrow', 'straight')
            try:
                lane = int(req_json.get('lane', 1))
            except Exception:
                lane = 1
            payload = {
                "cmd": "nav",
                "instruction": instruction,
                "road": road,
                "distance": distance,
                "speed": speed,
                "speed_limit": speed_limit,
                "eta": eta,
                "style": style,
                "vehicle": vehicle,
                "traffic_dist": traffic_dist,
                "traffic_light": traffic_light,
                "arrow": arrow,
                "lane": lane
            }
            send_mochi_udp(payload)
            self.send_response(200)
            self.send_header('Content-Type', 'application/json; charset=utf-8')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            self.wfile.write(json.dumps({"status": "ok", "nav": payload}, ensure_ascii=False).encode('utf-8'))
            return

        if path == '/api/payment_notify':
            try:
                raw_amt = req_json.get('amount', 50000)
                if isinstance(raw_amt, str):
                    clean = re.sub(r'[^\d]', '', raw_amt)
                    amount = int(clean) if clean else 50000
                else:
                    amount = int(raw_amt)
                sender = req_json.get('sender', 'Khách hàng')
                content = req_json.get('content', 'Thanh toan')

                spoken_amt = format_vietnamese_amount(amount)
                speech_text = f"Tài khoản TPBank vừa nhận được {spoken_amt} đồng từ {sender}"
                audio_url = f"http://{get_lan_ip()}:{PORT}/tts?text=" + urllib.parse.quote(speech_text)

                formatted_amt = f"{amount:,.0f}".replace(",", ".")

                payload = {
                    "cmd": "payment",
                    "amount": f"+{formatted_amt} đ",
                    "sender": sender,
                    "content": content,
                    "audio_url": audio_url
                }
                send_mochi_udp(payload)

                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.end_headers()
                self.wfile.write(json.dumps({"status": "ok", "spoken": speech_text}, ensure_ascii=False).encode('utf-8'))
            except Exception as e:
                logging.error(f"Notify error: {e}")
                self.send_response(500)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.end_headers()
                self.wfile.write(json.dumps({"error": str(e)}, ensure_ascii=False).encode('utf-8'))
            return

        elif path == '/api/bank_notify' or path == '/api/payment_notify':
            try:
                text = req_json.get('text', '') or body
                title = req_json.get('title', '')
                amount, sender, content = parse_vietnamese_bank_notification(text, title)
                if amount > 0:
                    spoken_amt = format_vietnamese_amount(amount)
                    speech_text = f"Tài khoản TPBank vừa nhận được {spoken_amt} đồng từ {sender}"
                    audio_url = f"http://{get_lan_ip()}:{PORT}/tts?text=" + urllib.parse.quote(speech_text)
                    formatted_amt = f"{amount:,.0f}".replace(",", ".")
                    payload = {
                        "cmd": "payment",
                        "amount": f"+{formatted_amt} đ",
                        "sender": sender,
                        "content": content,
                        "audio_url": audio_url
                    }
                    send_mochi_udp(payload)
                    self.send_response(200)
                    self.send_header('Content-Type', 'application/json; charset=utf-8')
                    self.end_headers()
                    self.wfile.write(json.dumps({"status": "ok", "amount": amount, "sender": sender, "spoken": speech_text}, ensure_ascii=False).encode('utf-8'))
                else:
                    self.send_response(200)
                    self.send_header('Content-Type', 'application/json; charset=utf-8')
                    self.end_headers()
                    self.wfile.write(json.dumps({"status": "ignored", "reason": "No incoming amount found"}, ensure_ascii=False).encode('utf-8'))
            except Exception as e:
                logging.error(f"Bank notify error: {e}")
                self.send_response(500)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.end_headers()
                self.wfile.write(json.dumps({"error": str(e)}, ensure_ascii=False).encode('utf-8'))
            return

        elif path == '/api/qr_change':
            try:
                amount = int(req_json.get('amount', 0))
                payload = {
                    "cmd": "qr",
                    "amount": amount
                }
                send_mochi_udp(payload)
                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.end_headers()
                self.wfile.write(json.dumps({"status": "ok"}, ensure_ascii=False).encode('utf-8'))
            except Exception as e:
                logging.error(f"QR change error: {e}")
                self.send_error(500, str(e))
            return

        elif path == '/webhook/sepay' or path == '/webhook/casso':
            try:
                logging.info(f"Incoming Webhook from {path}: {body}")
                # SePay webhook payload:
                # { "gateway": "TPBank", "amountIn": 50000, "transactionContent": "...", "referenceNumber": "..." }
                amount = int(req_json.get('amountIn') or req_json.get('amount') or 0)
                content = req_json.get('transactionContent') or req_json.get('description') or 'Thanh toán đơn hàng'
                sender = req_json.get('sender') or 'Khách hàng'

                if amount > 0:
                    spoken_amt = format_vietnamese_amount(amount)
                    speech_text = f"Tài khoản TPBank vừa nhận được {spoken_amt} đồng"
                    audio_url = f"http://{get_lan_ip()}:{PORT}/tts?text=" + urllib.parse.quote(speech_text)
                    formatted_amt = f"{amount:,.0f}".replace(",", ".")

                    payload = {
                        "cmd": "payment",
                        "amount": f"+{formatted_amt} đ",
                        "sender": sender,
                        "content": content,
                        "audio_url": audio_url
                    }
                    send_mochi_udp(payload)

                self.send_response(200)
                self.send_header('Content-Type', 'application/json; charset=utf-8')
                self.end_headers()
                self.wfile.write(json.dumps({"success": True}).encode('utf-8'))
            except Exception as e:
                logging.error(f"Webhook error: {e}")
                self.send_error(500, str(e))
            return

        self.send_error(404, 'Not found')

class ThreadingHTTPServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True

def run_https(https_server):
    try:
        https_server.serve_forever()
    except Exception as e:
        logging.error(f"HTTPS server error: {e}")

def main():
    logging.info(f"Starting Mochi Audio Bridge & Payment Soundbox on HTTP port {PORT}...")
    server = ThreadingHTTPServer(('0.0.0.0', PORT), YouTubeHandler)
    logging.info(f"Ready!")
    logging.info(f"-> Test Loa Thanh Toán: http://127.0.0.1:{PORT}/payment_test")
    logging.info(f"-> Webhook SePay:      http://127.0.0.1:{PORT}/webhook/sepay")
    logging.info(f"-> Waze HUD (HTTP):    http://{LAN_IP}:{PORT}/waze")

    if os.path.exists(CERT_FILE) and os.path.exists(KEY_FILE):
        try:
            ssl_context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ssl_context.load_cert_chain(certfile=CERT_FILE, keyfile=KEY_FILE)
            https_server = ThreadingHTTPServer(('0.0.0.0', HTTPS_PORT), YouTubeHandler)
            https_server.socket = ssl_context.wrap_socket(https_server.socket, server_side=True)
            t = threading.Thread(target=run_https, args=(https_server,), daemon=True)
            t.start()
            logging.info(f"-> Waze HUD GPS (HTTPS): https://{LAN_IP}:{HTTPS_PORT}/waze")
        except Exception as e:
            logging.error(f"Failed to start HTTPS server: {e}")

    while True:
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            logging.info("Shutting down...")
            server.server_close()
            break
        except Exception as e:
            logging.error(f"Server loop exception: {e}")
            time.sleep(1)

if __name__ == '__main__':
    main()
