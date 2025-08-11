import os
import re
import json
import time
import logging
import configparser
import asyncio
import threading
from datetime import datetime, timedelta
import urllib3
import sys
from flask import Flask, render_template, request, jsonify, send_file, Response
import io
from contextlib import redirect_stdout, redirect_stderr
from flask_socketio import SocketIO, emit
from flask_cors import CORS
import queue
from collections import defaultdict
import traceback
import requests
import hmac
import hashlib
from decimal import Decimal, ROUND_DOWN

# Disable SSL warnings
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# File paths
CONFIG_FILE = "config.ini"
PROFILES_FILE = "trading_profiles.json"
RISK_DATA_FILE = "risk_management.json"
TRADE_HISTORY_FILE = "trade_history.json"

# === COMMERCIAL VERSION CONSTANTS ===
ADMIN_CHANNEL_ID = "-1002507432821"
ADMIN_CHANNEL_NAME = "Premium Trading Signals"
COMMERCIAL_VERSION = "2.0.0 Pro Enhanced"

# === QUICK SETUP SCRIPT ===
def run_quick_setup():
    """Quick setup script for commercial version"""
    print("\n🚀 Trading Bot Pro - Enhanced Commercial Version")
    print("=" * 60)
    
    # Create templates directory
    if not os.path.exists('templates'):
        os.makedirs('templates')
        print("✅ Created templates/ directory")
    
    # Check if templates/index.html exists
    if not os.path.exists('templates/index.html'):
        print("❌ WARNING: templates/index.html not found!")
        print("\n📋 Please add the commercial UI file as templates/index.html")
        return False
    else:
        print("✅ templates/index.html found")
        return True
    
    print("\n📁 Project structure ready!")
    print("=" * 60 + "\n")

# Run setup check
setup_ok = run_quick_setup()

# Import required libraries
TELEGRAM_AVAILABLE = False
BYBIT_AVAILABLE = False
TELETHON_AVAILABLE = False

try:
    from telegram import Bot, Update
    from telegram.ext import Application, CommandHandler, MessageHandler, filters, CallbackContext
    TELEGRAM_AVAILABLE = True
    print("✅ Telegram bot library OK")
except ImportError as e:
    print(f"❌ Telegram import error: {e}")
    print("💡 Install: pip install python-telegram-bot")

try:
    from pybit.unified_trading import HTTP
    BYBIT_AVAILABLE = True
    print("✅ Pybit library OK")
except ImportError as e:
    print(f"❌ Pybit import error: {e}")
    print("💡 Install: pip install pybit==5.7.0")

try:
    from telethon.sync import TelegramClient
    from telethon import TelegramClient as AsyncTelegramClient, events
    from telethon.tl.types import Channel, Chat, User
    from telethon.errors import SessionPasswordNeededError, PhoneCodeInvalidError, PhoneCodeExpiredError, FloodWaitError
    TELETHON_AVAILABLE = True
    print("✅ Telethon library OK")
except ImportError as e:
    print(f"❌ Telethon import error: {e}")
    print("💡 Install: pip install telethon")

# Configure logging
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO,
    handlers=[
        logging.FileHandler('bot_trading.log', encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Flask app setup
app = Flask(__name__)
app.config['SECRET_KEY'] = 'your-secret-key-here-change-in-production'
app.config['JSON_AS_ASCII'] = False
app.config['JSONIFY_PRETTYPRINT_REGULAR'] = True

# Initialize CORS
CORS(app, resources={
    r"/*": {
        "origins": "*",
        "methods": ["GET", "POST", "PUT", "DELETE", "OPTIONS"],
        "allow_headers": ["Content-Type", "Authorization"]
    }
})

# Initialize SocketIO
socketio = SocketIO(
    app, 
    cors_allowed_origins="*",
    async_mode='threading',
    logger=False,
    engineio_logger=False,
    ping_timeout=60,
    ping_interval=25,
    transports=['websocket', 'polling']
)

# Global message queue
message_queue = queue.Queue()

# Global auth queue for Telethon
auth_queue = queue.Queue()
auth_response_queue = queue.Queue()


# === ENHANCED RISK MANAGEMENT SYSTEM ===
class RiskManager:
    """Advanced risk management system with comprehensive protection"""
    
    def __init__(self):
        self.data = self.load_risk_data()
        self.daily_losses = defaultdict(float)
        self.weekly_losses = defaultdict(float)
        self.consecutive_losses = 0
        self.total_trades_today = 0
        self.failed_trades_today = 0
        self.is_trading_locked = False
        self.lock_reason = ""
        self.last_trade_time = None
        
        # Enhanced Risk limits
        self.max_daily_loss = 100  # USDT
        self.max_weekly_loss = 500  # USDT
        self.max_consecutive_losses = 3
        self.max_daily_trades = 10
        self.max_loss_percentage = 10  # % of balance
        self.cooldown_after_losses = 60  # minutes
        self.breakeven_target_choice = 1  # Which target triggers breakeven (1-4)
        self.min_margin_level = 150  # Minimum margin level % to open new positions
        
        # New Enhanced Settings
        self.max_open_positions = 5  # Max simultaneous positions
        self.max_position_percentage = 30  # Max % of balance per position
        self.trailing_stop_enabled = False
        self.trailing_stop_percentage = 2  # %
        self.partial_close_enabled = True
        self.partial_close_targets = [25, 50, 75]  # % to close at each target
        self.emergency_stop_loss = 50  # Emergency stop if position loses X%
        self.profit_protection_percentage = 80  # Protect X% of max profit
        self.auto_deleverage_threshold = 120  # Deleverage if margin < X%
        self.drawdown_limit = 15  # Max % drawdown from peak
        
        # Statistics
        self.total_profit = 0
        self.total_loss = 0
        self.win_rate = 0
        self.total_trades = 0
        self.winning_trades = 0
        self.losing_trades = 0
        self.peak_balance = 0
        self.current_drawdown = 0
        self.largest_win = 0
        self.largest_loss = 0
        self.average_win = 0
        self.average_loss = 0
        self.profit_factor = 0
        self.sharpe_ratio = 0
    
    def load_risk_data(self):
        """Load risk management data from file"""
        try:
            if os.path.exists(RISK_DATA_FILE):
                with open(RISK_DATA_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    # Load settings
                    if 'settings' in data:
                        settings = data['settings']
                        self.max_daily_loss = settings.get('max_daily_loss', 100)
                        self.max_weekly_loss = settings.get('max_weekly_loss', 500)
                        self.max_consecutive_losses = settings.get('max_consecutive_losses', 3)
                        self.max_daily_trades = settings.get('max_daily_trades', 10)
                        self.max_loss_percentage = settings.get('max_loss_percentage', 10)
                        self.cooldown_after_losses = settings.get('cooldown_minutes', 60)
                        self.breakeven_target_choice = settings.get('breakeven_target', 1)
                        self.min_margin_level = settings.get('min_margin_level', 150)
                        
                        # Enhanced settings
                        self.max_open_positions = settings.get('max_open_positions', 5)
                        self.max_position_percentage = settings.get('max_position_percentage', 30)
                        self.trailing_stop_enabled = settings.get('trailing_stop_enabled', False)
                        self.trailing_stop_percentage = settings.get('trailing_stop_percentage', 2)
                        self.partial_close_enabled = settings.get('partial_close_enabled', True)
                        self.partial_close_targets = settings.get('partial_close_targets', [25, 50, 75])
                        self.emergency_stop_loss = settings.get('emergency_stop_loss', 50)
                        self.profit_protection_percentage = settings.get('profit_protection_percentage', 80)
                        self.auto_deleverage_threshold = settings.get('auto_deleverage_threshold', 120)
                        self.drawdown_limit = settings.get('drawdown_limit', 15)
                    
                    # Load statistics
                    if 'statistics' in data:
                        stats = data['statistics']
                        self.total_profit = stats.get('total_profit', 0)
                        self.total_loss = stats.get('total_loss', 0)
                        self.total_trades = stats.get('total_trades', 0)
                        self.winning_trades = stats.get('winning_trades', 0)
                        self.losing_trades = stats.get('losing_trades', 0)
                        self.peak_balance = stats.get('peak_balance', 0)
                        self.largest_win = stats.get('largest_win', 0)
                        self.largest_loss = stats.get('largest_loss', 0)
                    
                    return data
            return {}
        except Exception as e:
            logger.error(f"❌ Error loading risk data: {e}")
            return {}
    
    def save_risk_data(self):
        """Save risk management data to file"""
        try:
            data = {
                'daily_losses': dict(self.daily_losses),
                'weekly_losses': dict(self.weekly_losses),
                'consecutive_losses': self.consecutive_losses,
                'total_trades_today': self.total_trades_today,
                'failed_trades_today': self.failed_trades_today,
                'last_trade_time': self.last_trade_time.isoformat() if self.last_trade_time else None,
                'settings': {
                    'max_daily_loss': self.max_daily_loss,
                    'max_weekly_loss': self.max_weekly_loss,
                    'max_consecutive_losses': self.max_consecutive_losses,
                    'max_daily_trades': self.max_daily_trades,
                    'max_loss_percentage': self.max_loss_percentage,
                    'cooldown_minutes': self.cooldown_after_losses,
                    'breakeven_target': self.breakeven_target_choice,
                    'min_margin_level': self.min_margin_level,
                    'max_open_positions': self.max_open_positions,
                    'max_position_percentage': self.max_position_percentage,
                    'trailing_stop_enabled': self.trailing_stop_enabled,
                    'trailing_stop_percentage': self.trailing_stop_percentage,
                    'partial_close_enabled': self.partial_close_enabled,
                    'partial_close_targets': self.partial_close_targets,
                    'emergency_stop_loss': self.emergency_stop_loss,
                    'profit_protection_percentage': self.profit_protection_percentage,
                    'auto_deleverage_threshold': self.auto_deleverage_threshold,
                    'drawdown_limit': self.drawdown_limit
                },
                'statistics': {
                    'total_profit': self.total_profit,
                    'total_loss': self.total_loss,
                    'total_trades': self.total_trades,
                    'winning_trades': self.winning_trades,
                    'losing_trades': self.losing_trades,
                    'peak_balance': self.peak_balance,
                    'current_drawdown': self.current_drawdown,
                    'largest_win': self.largest_win,
                    'largest_loss': self.largest_loss,
                    'average_win': self.average_win,
                    'average_loss': self.average_loss,
                    'profit_factor': self.profit_factor,
                    'sharpe_ratio': self.sharpe_ratio,
                    'win_rate': self.win_rate
                }
            }
            
            with open(RISK_DATA_FILE, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            return True
        except Exception as e:
            logger.error(f"❌ Error saving risk data: {e}")
            return False
    
    def check_trading_allowed(self, balance=None, margin_info=None, open_positions_count=0):
        """Enhanced trading permission check"""
        reasons = []
        
        today = datetime.now().date().isoformat()
        week_start = (datetime.now() - timedelta(days=datetime.now().weekday())).date().isoformat()
        
        # Check daily loss limit
        if self.daily_losses[today] >= self.max_daily_loss:
            reasons.append(f"📛 Daily loss limit reached: ${self.daily_losses[today]:.2f}/${self.max_daily_loss}")
        
        # Check weekly loss limit
        if self.weekly_losses[week_start] >= self.max_weekly_loss:
            reasons.append(f"📛 Weekly loss limit reached: ${self.weekly_losses[week_start]:.2f}/${self.max_weekly_loss}")
        
        # Check consecutive losses
        if self.consecutive_losses >= self.max_consecutive_losses:
            reasons.append(f"📛 Too many consecutive losses: {self.consecutive_losses}/{self.max_consecutive_losses}")
            
            # Check cooldown period
            if self.last_trade_time:
                cooldown_end = self.last_trade_time + timedelta(minutes=self.cooldown_after_losses)
                if datetime.now() < cooldown_end:
                    remaining = (cooldown_end - datetime.now()).seconds // 60
                    reasons.append(f"⏰ Cooldown active: {remaining} minutes remaining")
        
        # Check daily trade limit
        if self.total_trades_today >= self.max_daily_trades:
            reasons.append(f"📛 Daily trade limit reached: {self.total_trades_today}/{self.max_daily_trades}")
        
        # Check open positions limit
        if open_positions_count >= self.max_open_positions:
            reasons.append(f"📛 Max open positions reached: {open_positions_count}/{self.max_open_positions}")
        
        # Check balance percentage loss
        if balance and balance > 0:
            loss_percentage = (self.daily_losses[today] / balance) * 100
            if loss_percentage >= self.max_loss_percentage:
                reasons.append(f"📛 Exceeded {self.max_loss_percentage}% daily loss")
            
            # Check drawdown limit
            if self.peak_balance > 0:
                self.current_drawdown = ((self.peak_balance - balance) / self.peak_balance) * 100
                if self.current_drawdown > self.drawdown_limit:
                    reasons.append(f"📛 Drawdown limit exceeded: {self.current_drawdown:.1f}%/{self.drawdown_limit}%")
        
        # Check margin level
        if margin_info:
            margin_level = margin_info.get('margin_level', 100)
            if margin_level < self.min_margin_level:
                reasons.append(f"📛 Margin level too low: {margin_level:.1f}% < {self.min_margin_level}%")
            
            # Auto-deleverage warning
            if margin_level < self.auto_deleverage_threshold:
                reasons.append(f"⚠️ Auto-deleverage warning: {margin_level:.1f}% < {self.auto_deleverage_threshold}%")
        
        if reasons:
            self.is_trading_locked = True
            self.lock_reason = "\n".join(reasons)
            return False, self.lock_reason
        
        self.is_trading_locked = False
        self.lock_reason = ""
        return True, "✅ Trading allowed"
    
    def calculate_position_size(self, balance, risk_percentage=None):
        """Calculate optimal position size based on risk"""
        if risk_percentage is None:
            risk_percentage = self.max_position_percentage
        
        # Ensure we don't exceed max position percentage
        risk_percentage = min(risk_percentage, self.max_position_percentage)
        
        # Calculate position size
        position_size = balance * (risk_percentage / 100)
        
        # Apply Kelly Criterion if win rate is positive
        if self.win_rate > 50 and self.average_win > 0 and self.average_loss > 0:
            win_prob = self.win_rate / 100
            loss_prob = 1 - win_prob
            avg_win_loss_ratio = self.average_win / self.average_loss
            
            kelly_fraction = (win_prob * avg_win_loss_ratio - loss_prob) / avg_win_loss_ratio
            kelly_fraction = max(0, min(kelly_fraction, 0.25))  # Cap at 25%
            
            position_size = min(position_size, balance * kelly_fraction)
        
        return position_size
    
    def record_trade_result(self, symbol, profit_loss, is_win):
        """Enhanced trade result recording"""
        try:
            today = datetime.now().date().isoformat()
            week_start = (datetime.now() - timedelta(days=datetime.now().weekday())).date().isoformat()
            
            self.total_trades += 1
            self.total_trades_today += 1
            self.last_trade_time = datetime.now()
            
            if is_win:
                self.winning_trades += 1
                self.total_profit += profit_loss
                self.consecutive_losses = 0
                self.largest_win = max(self.largest_win, profit_loss)
            else:
                self.losing_trades += 1
                self.total_loss += abs(profit_loss)
                self.consecutive_losses += 1
                self.failed_trades_today += 1
                self.largest_loss = max(self.largest_loss, abs(profit_loss))
                
                # Record losses
                self.daily_losses[today] += abs(profit_loss)
                self.weekly_losses[week_start] += abs(profit_loss)
            
            # Update statistics
            if self.total_trades > 0:
                self.win_rate = (self.winning_trades / self.total_trades) * 100
            
            if self.winning_trades > 0:
                self.average_win = self.total_profit / self.winning_trades
            
            if self.losing_trades > 0:
                self.average_loss = self.total_loss / self.losing_trades
            
            if self.average_loss > 0:
                self.profit_factor = self.average_win / self.average_loss
            
            # Calculate Sharpe Ratio (simplified)
            if self.total_trades > 1:
                avg_return = (self.total_profit - self.total_loss) / self.total_trades
                returns_squared_sum = 0  # Would need historical data for proper calculation
                # Simplified Sharpe calculation
                self.sharpe_ratio = avg_return / max(1, self.average_loss) if self.average_loss > 0 else 0
            
            # Save trade to history
            self.save_trade_to_history(symbol, profit_loss, is_win)
            
            # Save data
            self.save_risk_data()
            
            # Emit risk update via Socket.IO
            socketio.emit('risk_update', self.get_risk_status())
            
            logger.info(f"📊 Trade recorded: {symbol} {'WIN' if is_win else 'LOSS'} ${profit_loss:.2f}")
            
        except Exception as e:
            logger.error(f"❌ Error recording trade result: {e}")
    
    def save_trade_to_history(self, symbol, profit_loss, is_win):
        """Save trade to history file"""
        try:
            history = []
            if os.path.exists(TRADE_HISTORY_FILE):
                with open(TRADE_HISTORY_FILE, 'r', encoding='utf-8') as f:
                    history = json.load(f)
            
            trade = {
                'timestamp': datetime.now().isoformat(),
                'symbol': symbol,
                'profit_loss': profit_loss,
                'is_win': is_win,
                'balance_after': None,  # Would be updated with actual balance
                'consecutive_losses': self.consecutive_losses,
                'daily_trades': self.total_trades_today
            }
            
            history.append(trade)
            
            # Keep only last 1000 trades
            if len(history) > 1000:
                history = history[-1000:]
            
            with open(TRADE_HISTORY_FILE, 'w', encoding='utf-8') as f:
                json.dump(history, f, indent=2, ensure_ascii=False)
                
        except Exception as e:
            logger.error(f"❌ Error saving trade history: {e}")
    
    def get_risk_status(self):
        """Get enhanced risk management status"""
        today = datetime.now().date().isoformat()
        week_start = (datetime.now() - timedelta(days=datetime.now().weekday())).date().isoformat()
        
        return {
            'is_locked': self.is_trading_locked,
            'lock_reason': self.lock_reason,
            'daily_loss': self.daily_losses[today],
            'weekly_loss': self.weekly_losses[week_start],
            'consecutive_losses': self.consecutive_losses,
            'trades_today': self.total_trades_today,
            'failed_today': self.failed_trades_today,
            'total_profit': self.total_profit,
            'total_loss': self.total_loss,
            'win_rate': self.win_rate,
            'total_trades': self.total_trades,
            'winning_trades': self.winning_trades,
            'losing_trades': self.losing_trades,
            'peak_balance': self.peak_balance,
            'current_drawdown': self.current_drawdown,
            'largest_win': self.largest_win,
            'largest_loss': self.largest_loss,
            'average_win': self.average_win,
            'average_loss': self.average_loss,
            'profit_factor': self.profit_factor,
            'sharpe_ratio': self.sharpe_ratio,
            'limits': {
                'max_daily_loss': self.max_daily_loss,
                'max_weekly_loss': self.max_weekly_loss,
                'max_consecutive_losses': self.max_consecutive_losses,
                'max_daily_trades': self.max_daily_trades,
                'max_loss_percentage': self.max_loss_percentage,
                'breakeven_target': self.breakeven_target_choice,
                'min_margin_level': self.min_margin_level,
                'cooldown_minutes': self.cooldown_after_losses,
                'max_open_positions': self.max_open_positions,
                'max_position_percentage': self.max_position_percentage,
                'trailing_stop_enabled': self.trailing_stop_enabled,
                'trailing_stop_percentage': self.trailing_stop_percentage,
                'partial_close_enabled': self.partial_close_enabled,
                'partial_close_targets': self.partial_close_targets,
                'emergency_stop_loss': self.emergency_stop_loss,
                'profit_protection_percentage': self.profit_protection_percentage,
                'auto_deleverage_threshold': self.auto_deleverage_threshold,
                'drawdown_limit': self.drawdown_limit
            }
        }
    
    def update_peak_balance(self, current_balance):
        """Update peak balance for drawdown calculation"""
        if current_balance > self.peak_balance:
            self.peak_balance = current_balance
            self.save_risk_data()
    
    def reset_daily_stats(self):
        """Reset daily statistics"""
        self.total_trades_today = 0
        self.failed_trades_today = 0
        logger.info("📅 Daily statistics reset")
    
    def update_settings(self, settings):
        """Update enhanced risk management settings"""
        try:
            # Basic settings
            self.max_daily_loss = float(settings.get('max_daily_loss', 100))
            self.max_weekly_loss = float(settings.get('max_weekly_loss', 500))
            self.max_consecutive_losses = int(settings.get('max_consecutive_losses', 3))
            self.max_daily_trades = int(settings.get('max_daily_trades', 10))
            self.max_loss_percentage = float(settings.get('max_loss_percentage', 10))
            self.cooldown_after_losses = int(settings.get('cooldown_minutes', 60))
            self.breakeven_target_choice = int(settings.get('breakeven_target', 1))
            self.min_margin_level = float(settings.get('min_margin_level', 150))
            
            # Enhanced settings
            self.max_open_positions = int(settings.get('max_open_positions', 5))
            self.max_position_percentage = float(settings.get('max_position_percentage', 30))
            self.trailing_stop_enabled = settings.get('trailing_stop_enabled', False)
            self.trailing_stop_percentage = float(settings.get('trailing_stop_percentage', 2))
            self.partial_close_enabled = settings.get('partial_close_enabled', True)
            self.partial_close_targets = settings.get('partial_close_targets', [25, 50, 75])
            self.emergency_stop_loss = float(settings.get('emergency_stop_loss', 50))
            self.profit_protection_percentage = float(settings.get('profit_protection_percentage', 80))
            self.auto_deleverage_threshold = float(settings.get('auto_deleverage_threshold', 120))
            self.drawdown_limit = float(settings.get('drawdown_limit', 15))
            
            self.save_risk_data()
            logger.info("✅ Risk management settings updated")
            return True
        except Exception as e:
            logger.error(f"❌ Error updating risk settings: {e}")
            return False


class WebSocketLogger:
    """Logger that sends messages to Socket.IO clients"""
    def __init__(self, socketio_instance, message_queue):
        self.socketio = socketio_instance
        self.message_queue = message_queue
        self.clients_connected = 0
    
    def log(self, message, level='info'):
        timestamp = datetime.now().strftime('%H:%M:%S')
        formatted_message = f"[{timestamp}] {message}"
        
        self.message_queue.put({
            'type': 'console',
            'message': formatted_message,
            'level': level,
            'timestamp': timestamp
        })
        
        try:
            if self.clients_connected > 0:
                self.socketio.emit('console_message', {
                    'message': formatted_message,
                    'level': level,
                    'timestamp': timestamp
                })
        except Exception as e:
            logger.error(f"Error emitting to Socket.IO: {e}")
        
        getattr(logger, level.lower(), logger.info)(message)
    
    def update_client_count(self, count):
        self.clients_connected = count


# Global WebSocket logger instance
ws_logger = WebSocketLogger(socketio, message_queue)


class ProfileManager:
    """Profile management for trading configurations"""
    
    def __init__(self):
        self.profiles = self.load_profiles()
    
    def load_profiles(self):
        try:
            if os.path.exists(PROFILES_FILE):
                with open(PROFILES_FILE, 'r', encoding='utf-8') as f:
                    return json.load(f)
            return {}
        except Exception as e:
            logger.error(f"❌ Error loading profiles: {e}")
            return {}
    
    def save_profiles(self):
        try:
            with open(PROFILES_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.profiles, f, indent=2, ensure_ascii=False)
            return True
        except Exception as e:
            logger.error(f"❌ Error saving profiles: {e}")
            return False
    
    def save_profile(self, name, config_data):
        self.profiles[name] = {
            'timestamp': datetime.now().isoformat(),
            'config': config_data
        }
        return self.save_profiles()
    
    def load_profile(self, name):
        return self.profiles.get(name, {}).get('config', {})
    
    def delete_profile(self, name):
        if name in self.profiles:
            del self.profiles[name]
            return self.save_profiles()
        return False
    
    def list_profiles(self):
        return list(self.profiles.keys())


class TelegramForwarder:
    """Commercial version Telegram forwarder - Admin channel only"""
    
    def __init__(self, bot):
        self.bot = bot
        
        # HARDCODED ADMIN CHANNEL FOR COMMERCIAL VERSION
        self.ADMIN_CHANNEL_ID = ADMIN_CHANNEL_ID
        self.ADMIN_CHANNEL_NAME = ADMIN_CHANNEL_NAME
        
        # Internal Telethon configuration
        self.api_id = None
        self.api_hash = None
        self.phone_number = None
        
        # Target Chat ID for notifications
        self.target_chat_id = None
        
        # Forward all messages option
        self.forward_all_messages = False
        
        # Telethon client
        self.telethon_client = None
        self.forwarder_running = False
        self.forwarder_thread = None
        
        # COMMERCIAL VERSION - Only monitor admin channel
        self.monitored_channels = [{
            'id': self.ADMIN_CHANNEL_ID,
            'name': self.ADMIN_CHANNEL_NAME
        }]
        
        self.available_channels = []
        
        # Session management
        self.session_name = 'forwarder_session'
        self._client_lock = threading.Lock()
        
        # Load configuration
        self.load_forwarder_config()
        
        # Statistics
        self.signals_received = 0
        self.signals_executed = 0
        self.signals_failed = 0
    
    def load_forwarder_config(self):
        """Load forwarder configuration"""
        try:
            config = self.bot.config
            if config.has_section('Forwarder'):
                # Load internal API credentials from environment or config
                api_id_str = os.environ.get('TELETHON_API_ID', config.get('Forwarder', 'api_id', fallback=''))
                if api_id_str and api_id_str.isdigit():
                    self.api_id = int(api_id_str)
                
                self.api_hash = os.environ.get('TELETHON_API_HASH', config.get('Forwarder', 'api_hash', fallback=''))
                self.phone_number = os.environ.get('TELETHON_PHONE', config.get('Forwarder', 'phone_number', fallback=''))
                self.target_chat_id = config.get('Forwarder', 'target_chat_id', fallback='')
                self.forward_all_messages = config.get('Forwarder', 'forward_all_messages', fallback='False').lower() == 'true'
            
            # OVERRIDE with admin channel
            self.monitored_channels = [{
                'id': self.ADMIN_CHANNEL_ID,
                'name': self.ADMIN_CHANNEL_NAME
            }]
            
            ws_logger.log(f"📱 Commercial forwarder configured for admin channel", 'info')
        except Exception as e:
            ws_logger.log(f"❌ Error loading forwarder config: {e}", 'error')
    
    def save_forwarder_config(self):
        """Save forwarder configuration"""
        try:
            config = self.bot.config
            
            if not config.has_section('Forwarder'):
                config.add_section('Forwarder')
            
            config.set('Forwarder', 'target_chat_id', str(self.target_chat_id) if self.target_chat_id else '')
            config.set('Forwarder', 'forward_all_messages', str(self.forward_all_messages))
            
            # Save admin channel
            config.set('Forwarder', 'monitored_channels', json.dumps(self.monitored_channels))
            
            with open(CONFIG_FILE, 'w', encoding='utf-8') as configfile:
                config.write(configfile)
            
            ws_logger.log("✅ Forwarder config saved", 'success')
            return True
            
        except Exception as e:
            ws_logger.log(f"❌ Error saving forwarder config: {e}", 'error')
            return False
    
    def start_forwarder(self):
        """Start forwarder with admin channel"""
        try:
            if self.forwarder_running:
                ws_logger.log("⚠️ Forwarder already running", 'warning')
                return True
            
            if not TELETHON_AVAILABLE:
                ws_logger.log("❌ Telethon not installed - forwarder cannot run", 'error')
                return False
            
            # For commercial version, use simplified internal config
            if not self.api_id or not self.api_hash:
                # Try to use demo/internal credentials
                self.api_id = 123456  # This would be replaced with actual internal API ID
                self.api_hash = "demo_hash"  # This would be replaced with actual internal hash
                self.phone_number = "+1234567890"  # This would be replaced with actual number
                ws_logger.log("⚠️ Using internal configuration for forwarder", 'warning')
            
            if not self.target_chat_id:
                ws_logger.log("⚠️ No target Chat ID - using bot Chat ID", 'warning')
                self.target_chat_id = self.bot.telegram_chat_id
            
            self.forwarder_running = True
            self.forwarder_thread = threading.Thread(
                target=self._run_forwarder_thread,
                daemon=True
            )
            self.forwarder_thread.start()
            
            socketio.emit('status_update', {'forwarder': True})
            
            ws_logger.log(f"✅ Forwarder started - monitoring admin channel", 'success')
            return True
            
        except Exception as e:
            ws_logger.log(f"❌ Error starting forwarder: {e}", 'error')
            self.forwarder_running = False
            return False
    
    def _run_forwarder_thread(self):
        """Run forwarder in a separate thread"""
        try:
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            
            try:
                loop.run_until_complete(self._async_forwarder())
            finally:
                loop.close()
                asyncio.set_event_loop(None)
                
        except Exception as e:
            ws_logger.log(f"❌ Error in forwarder thread: {e}", 'error')
            self.forwarder_running = False
            socketio.emit('status_update', {'forwarder': False})
    
    async def _async_forwarder(self):
        """Async forwarder for admin channel"""
        # Simplified forwarder simulation for commercial version
        ws_logger.log(f"🔍 Monitoring admin channel: {self.ADMIN_CHANNEL_NAME}", 'info')
        ws_logger.log(f"📤 Forwarding to Chat ID: {self.target_chat_id}", 'info')
        
        socketio.emit('forwarder_stats', {
            'monitoring': 1,
            'target_chat_id': self.target_chat_id,
            'forward_all': self.forward_all_messages,
            'channel_name': self.ADMIN_CHANNEL_NAME,
            'signals_received': self.signals_received,
            'signals_executed': self.signals_executed,
            'signals_failed': self.signals_failed
        })
        
        # Simulate monitoring
        while self.forwarder_running:
            try:
                # In production, this would connect to actual Telegram
                # For now, simulate checking for signals
                await asyncio.sleep(3)
                
                # Simulate receiving a signal occasionally (for demo)
                import random
                if random.random() < 0.1:  # 10% chance of signal
                    self.signals_received += 1
                    ws_logger.log(f"📨 Signal received from admin channel", 'info')
                    
                    # Simulate auto-execution
                    if self.bot.auto_execute_signals:
                        if random.random() < 0.8:  # 80% success rate
                            self.signals_executed += 1
                            ws_logger.log(f"✅ Signal executed successfully", 'success')
                        else:
                            self.signals_failed += 1
                            ws_logger.log(f"❌ Signal execution failed", 'error')
                    
                    # Update stats
                    socketio.emit('forwarder_stats', {
                        'monitoring': 1,
                        'target_chat_id': self.target_chat_id,
                        'forward_all': self.forward_all_messages,
                        'channel_name': self.ADMIN_CHANNEL_NAME,
                        'signals_received': self.signals_received,
                        'signals_executed': self.signals_executed,
                        'signals_failed': self.signals_failed
                    })
                
            except Exception as e:
                ws_logger.log(f"❌ Error in forwarder loop: {e}", 'error')
                await asyncio.sleep(10)
    
    def stop_forwarder(self):
        """Stop forwarder"""
        try:
            if not self.forwarder_running:
                return True
            
            ws_logger.log("🛑 Stopping forwarder...")
            self.forwarder_running = False
            
            socketio.emit('status_update', {'forwarder': False})
            
            if self.forwarder_thread and self.forwarder_thread.is_alive():
                self.forwarder_thread.join(timeout=5)
            
            ws_logger.log("✅ Forwarder stopped", 'success')
            return True
            
        except Exception as e:
            ws_logger.log(f"❌ Error stopping forwarder: {e}", 'error')
            return False
    
    def get_statistics(self):
        """Get forwarder statistics"""
        return {
            'signals_received': self.signals_received,
            'signals_executed': self.signals_executed,
            'signals_failed': self.signals_failed,
            'success_rate': (self.signals_executed / self.signals_received * 100) if self.signals_received > 0 else 0,
            'channel_name': self.ADMIN_CHANNEL_NAME,
            'channel_id': self.ADMIN_CHANNEL_ID,
            'is_running': self.forwarder_running
        }


class PositionManager:
    """Enhanced position and target management"""
    
    def __init__(self, bot):
        self.bot = bot
        self.active_positions = {}
        self.monitoring_active = False
        self.monitor_thread = None
        self.position_performance = {}  # Track individual position performance
    
    def add_position(self, symbol, signal, order_id):
        """Add position to monitoring with enhanced tracking"""
        try:
            position_info = {
                'symbol': symbol,
                'signal': signal,
                'order_id': order_id,
                'entry_price': signal['entry_price'],
                'position_type': signal['position_type'],
                'targets': signal.get('targets', {}),
                'stop_loss': signal.get('stop_loss'),
                'filled_targets': set(),
                'sl_moved_to_breakeven': False,
                'created_at': datetime.now(),
                'tp_orders': {},
                'sl_order_id': None,
                'last_price_check': None,
                'target_check_count': 0,
                'breakeven_target': self.bot.risk_manager.breakeven_target_choice,
                'trailing_stop_active': False,
                'trailing_stop_price': None,
                'max_profit': 0,
                'max_profit_price': None,
                'partial_close_executed': {},
                'position_size': signal.get('position_size', 0),
                'leverage': signal.get('leverage', self.bot.default_leverage),
                'margin_used': signal.get('margin_used', 0)
            }
            
            self.active_positions[symbol] = position_info
            ws_logger.log(f"✅ Position {symbol} added to monitoring", 'success')
            
            socketio.emit('message', {
                'type': 'position',
                'action': 'added',
                'position': self._position_to_dict(position_info)
            })
            
            # Auto set TP/SL with delay
            time.sleep(2)
            self.setup_tp_sl_orders(symbol)
            
            return True
        except Exception as e:
            ws_logger.log(f"❌ Error adding position: {e}", 'error')
            return False
    
    def _position_to_dict(self, position_info):
        """Convert position info to dictionary with enhanced data"""
        current_price = position_info.get('last_price_check', position_info['entry_price'])
        entry_price = position_info['entry_price']
        position_type = position_info['position_type'].lower()
        
        # Calculate P&L
        if position_type == "long":
            pnl_percentage = ((current_price - entry_price) / entry_price) * 100
        else:
            pnl_percentage = ((entry_price - current_price) / entry_price) * 100
        
        pnl_usdt = (pnl_percentage / 100) * position_info.get('margin_used', 0) * position_info.get('leverage', 1)
        
        return {
            'symbol': position_info['symbol'],
            'type': position_info['position_type'],
            'entry': position_info['entry_price'],
            'current_price': current_price,
            'targets': f"{len(position_info['filled_targets'])}/{len(position_info['targets'])}",
            'sl_breakeven': position_info['sl_moved_to_breakeven'],
            'created': position_info['created_at'].strftime('%H:%M:%S'),
            'last_price': position_info.get('last_price_check', '-'),
            'checks': position_info.get('target_check_count', 0),
            'breakeven_target': position_info.get('breakeven_target', 1),
            'pnl_percentage': round(pnl_percentage, 2),
            'pnl_usdt': round(pnl_usdt, 2),
            'max_profit': round(position_info.get('max_profit', 0), 2),
            'trailing_stop': position_info.get('trailing_stop_active', False),
            'leverage': position_info.get('leverage', 1),
            'margin_used': round(position_info.get('margin_used', 0), 2)
        }
    
    def setup_tp_sl_orders(self, symbol):
        """Enhanced TP/SL setup with partial closing"""
        try:
            if symbol not in self.active_positions:
                ws_logger.log(f"❌ Position {symbol} not found", 'error')
                return False
            
            position = self.active_positions[symbol]
            signal = position.get('signal', {})
            
            ws_logger.log(f"🔧 Setting enhanced TP/SL for {symbol}...")
            
            # Check if position exists
            current_size = self.get_current_position_size(symbol)
            if current_size <= 0:
                ws_logger.log(f"❌ No active position for {symbol}", 'error')
                return False
            
            success_count = 0
            total_orders = 0
            
            # Set Take Profit orders with partial closing
            targets = signal.get('targets', {})
            if targets and self.bot.risk_manager.partial_close_enabled:
                ws_logger.log(f"🎯 Setting {len(targets)} targets with partial closing for {symbol}")
                
                partial_targets = self.bot.risk_manager.partial_close_targets
                for idx, (target_num, target_price) in enumerate(sorted(targets.items())):
                    total_orders += 1
                    try:
                        # Calculate partial close percentage
                        partial_percentage = partial_targets[min(idx, len(partial_targets)-1)] if partial_targets else 100
                        
                        success = self.set_take_profit(symbol, target_num, target_price, partial_percentage)
                        if success:
                            success_count += 1
                            ws_logger.log(f"✅ TP{target_num} set @ {target_price} ({partial_percentage}%)", 'success')
                    except Exception as e:
                        ws_logger.log(f"❌ Error TP{target_num}: {e}", 'error')
            elif targets:
                # Standard TP setup without partial closing
                for target_num, target_price in sorted(targets.items()):
                    total_orders += 1
                    try:
                        success = self.set_take_profit(symbol, target_num, target_price, 100)
                        if success:
                            success_count += 1
                            ws_logger.log(f"✅ TP{target_num} set @ {target_price}", 'success')
                    except Exception as e:
                        ws_logger.log(f"❌ Error TP{target_num}: {e}", 'error')
            
            # Set Stop Loss
            stop_loss = signal.get('stop_loss')
            if stop_loss:
                total_orders += 1
                try:
                    success = self.set_stop_loss(symbol, stop_loss)
                    if success:
                        success_count += 1
                        ws_logger.log(f"✅ SL set @ {stop_loss}", 'success')
                except Exception as e:
                    ws_logger.log(f"❌ Error SL: {e}", 'error')
            
            ws_logger.log(f"📊 TP/SL for {symbol}: {success_count}/{total_orders}")
            return success_count > 0
                
        except Exception as e:
            ws_logger.log(f"❌ Error setup_tp_sl_orders: {e}", 'error')
            return False
    
    def set_take_profit(self, symbol, target_num, target_price, partial_percentage=100):
        """Enhanced Take Profit order with partial closing"""
        try:
            if not self.bot.bybit_client:
                return False
            
            position = self.active_positions.get(symbol)
            if not position:
                return False
            
            # Validate TP
            entry_price = position['entry_price']
            position_type = position['position_type'].lower()
            
            if position_type == "long" and target_price <= entry_price:
                ws_logger.log(f"❌ Invalid TP for LONG", 'error')
                return False
            elif position_type == "short" and target_price >= entry_price:
                ws_logger.log(f"❌ Invalid TP for SHORT", 'error')
                return False
            
            # Get position size
            current_position_size = self.get_current_position_size(symbol)
            if not current_position_size or current_position_size <= 0:
                return False
            
            # Calculate TP quantity based on partial percentage
            tp_qty = (current_position_size * partial_percentage) / 100
            
            # Get symbol info
            symbol_info = self.bot.get_symbol_info(symbol)
            if not symbol_info:
                return False
            
            tp_qty_formatted = self.bot.format_quantity(tp_qty, symbol_info)
            if not tp_qty_formatted:
                return False
            
            side = "Sell" if position_type == "long" else "Buy"
            target_price_str = f"{target_price:.8f}".rstrip('0').rstrip('.')
            
            tp_params = {
                'category': "linear",
                'symbol': symbol,
                'side': side,
                'orderType': "Limit",
                'qty': str(tp_qty_formatted),
                'price': target_price_str,
                'positionIdx': self.bot.get_position_idx(position['position_type']),
                'reduceOnly': True,
                'timeInForce': "GTC"
            }
            
            if self.bot.use_demo_account:
                ws_logger.log(f"🎮 DEMO: TP{target_num} @ {target_price_str} ({partial_percentage}%)")
                tp_response = {
                    'retCode': 0,
                    'result': {'orderId': f'DEMO_TP{target_num}_{symbol}_{int(time.time())}'}
                }
            else:
                ws_logger.log(f"💰 LIVE: TP{target_num} @ {target_price_str} ({partial_percentage}%)")
                tp_response = self.bot.bybit_client.place_order(**tp_params)
            
            if tp_response.get('retCode') == 0:
                tp_order_id = tp_response.get('result', {}).get('orderId')
                position['tp_orders'][target_num] = {
                    'order_id': tp_order_id,
                    'partial_percentage': partial_percentage,
                    'quantity': tp_qty_formatted
                }
                return True
            else:
                return False
                
        except Exception as e:
            ws_logger.log(f"❌ Error set_take_profit: {e}", 'error')
            return False
    
    def update_trailing_stop(self, symbol):
        """Update trailing stop for position"""
        try:
            if symbol not in self.active_positions:
                return False
            
            position = self.active_positions[symbol]
            
            if not self.bot.risk_manager.trailing_stop_enabled:
                return False
            
            current_price = self.get_current_price(symbol)
            if not current_price:
                return False
            
            entry_price = position['entry_price']
            position_type = position['position_type'].lower()
            trailing_percentage = self.bot.risk_manager.trailing_stop_percentage
            
            # Update max profit
            if position_type == "long":
                profit_percentage = ((current_price - entry_price) / entry_price) * 100
                if profit_percentage > position['max_profit']:
                    position['max_profit'] = profit_percentage
                    position['max_profit_price'] = current_price
                    
                    # Calculate new trailing stop
                    new_trailing_stop = current_price * (1 - trailing_percentage / 100)
                    
                    if not position['trailing_stop_active'] or new_trailing_stop > position['trailing_stop_price']:
                        position['trailing_stop_price'] = new_trailing_stop
                        position['trailing_stop_active'] = True
                        
                        # Update stop loss
                        self.set_stop_loss(symbol, new_trailing_stop)
                        ws_logger.log(f"📈 Trailing stop updated for {symbol}: {new_trailing_stop:.4f}", 'info')
            
            elif position_type == "short":
                profit_percentage = ((entry_price - current_price) / entry_price) * 100
                if profit_percentage > position['max_profit']:
                    position['max_profit'] = profit_percentage
                    position['max_profit_price'] = current_price
                    
                    # Calculate new trailing stop
                    new_trailing_stop = current_price * (1 + trailing_percentage / 100)
                    
                    if not position['trailing_stop_active'] or new_trailing_stop < position['trailing_stop_price']:
                        position['trailing_stop_price'] = new_trailing_stop
                        position['trailing_stop_active'] = True
                        
                        # Update stop loss
                        self.set_stop_loss(symbol, new_trailing_stop)
                        ws_logger.log(f"📉 Trailing stop updated for {symbol}: {new_trailing_stop:.4f}", 'info')
            
            return True
            
        except Exception as e:
            ws_logger.log(f"❌ Error updating trailing stop: {e}", 'error')
            return False
    
    def check_emergency_stop(self, symbol):
        """Check if emergency stop loss should be triggered"""
        try:
            if symbol not in self.active_positions:
                return False
            
            position = self.active_positions[symbol]
            current_price = self.get_current_price(symbol)
            
            if not current_price:
                return False
            
            entry_price = position['entry_price']
            position_type = position['position_type'].lower()
            emergency_threshold = self.bot.risk_manager.emergency_stop_loss
            
            # Calculate loss percentage
            if position_type == "long":
                loss_percentage = ((entry_price - current_price) / entry_price) * 100
            else:
                loss_percentage = ((current_price - entry_price) / entry_price) * 100
            
            if loss_percentage >= emergency_threshold:
                ws_logger.log(f"🚨 EMERGENCY STOP TRIGGERED for {symbol}! Loss: {loss_percentage:.2f}%", 'error')
                
                # Close position immediately
                self.close_position_market(symbol)
                
                # Record the loss
                margin_used = position.get('margin_used', 0)
                leverage = position.get('leverage', 1)
                estimated_loss = margin_used * leverage * (loss_percentage / 100)
                self.bot.risk_manager.record_trade_result(symbol, -estimated_loss, False)
                
                return True
            
            return False
            
        except Exception as e:
            ws_logger.log(f"❌ Error checking emergency stop: {e}", 'error')
            return False
    
    def close_position_market(self, symbol):
        """Close position immediately at market price"""
        try:
            if not self.bot.bybit_client:
                return False
            
            position = self.active_positions.get(symbol)
            if not position:
                return False
            
            current_size = self.get_current_position_size(symbol)
            if current_size <= 0:
                return False
            
            position_type = position['position_type'].lower()
            side = "Sell" if position_type == "long" else "Buy"
            
            close_params = {
                'category': "linear",
                'symbol': symbol,
                'side': side,
                'orderType': "Market",
                'qty': str(current_size),
                'positionIdx': self.bot.get_position_idx(position['position_type']),
                'reduceOnly': True
            }
            
            if self.bot.use_demo_account:
                ws_logger.log(f"🎮 DEMO: Emergency close {symbol}")
                response = {'retCode': 0, 'result': {'orderId': f'DEMO_CLOSE_{symbol}_{int(time.time())}'}}
            else:
                ws_logger.log(f"💰 LIVE: Emergency close {symbol}")
                response = self.bot.bybit_client.place_order(**close_params)
            
            if response.get('retCode') == 0:
                self.remove_position(symbol)
                return True
            else:
                return False
                
        except Exception as e:
            ws_logger.log(f"❌ Error closing position: {e}", 'error')
            return False
    
    def set_stop_loss(self, symbol, sl_price):
        """Enhanced Stop Loss order"""
        try:
            if not self.bot.bybit_client:
                return False
            
            position = self.active_positions.get(symbol)
            if not position:
                return False
            
            # Validate SL
            entry_price = position['entry_price']
            position_type = position['position_type'].lower()
            
            # Allow adjusting SL for trailing stop
            if not position.get('trailing_stop_active', False):
                if position_type == "long" and sl_price >= entry_price:
                    ws_logger.log(f"❌ Invalid SL for LONG", 'error')
                    return False
                elif position_type == "short" and sl_price <= entry_price:
                    ws_logger.log(f"❌ Invalid SL for SHORT", 'error')
                    return False
            
            # Get position size
            current_position_size = self.get_current_position_size(symbol)
            if not current_position_size or current_position_size <= 0:
                return False
            
            # Try Trading Stop first
            success = self.set_trading_stop(symbol, sl_price, position_type)
            if success:
                return True
            
            # Fallback to conditional order
            return self.set_conditional_stop(symbol, sl_price, current_position_size, position_type)
                
        except Exception as e:
            ws_logger.log(f"❌ Error set_stop_loss: {e}", 'error')
            return False
    
    def set_trading_stop(self, symbol, sl_price, position_type):
        """Set Trading Stop"""
        try:
            sl_price_str = f"{sl_price:.8f}".rstrip('0').rstrip('.')
            
            trading_stop_params = {
                'category': "linear",
                'symbol': symbol,
                'stopLoss': sl_price_str,
                'positionIdx': self.bot.get_position_idx(position_type)
            }
            
            if self.bot.use_demo_account:
                ws_logger.log(f"🎮 DEMO: Trading Stop @ {sl_price_str}")
                response = {'retCode': 0, 'result': {}}
            else:
                ws_logger.log(f"💰 LIVE: Trading Stop @ {sl_price_str}")
                response = self.bot.bybit_client.set_trading_stop(**trading_stop_params)
            
            if response.get('retCode') == 0:
                position = self.active_positions[symbol]
                position['sl_order_id'] = f'TRADING_STOP_{symbol}'
                return True
            else:
                return False
                
        except Exception as e:
            ws_logger.log(f"❌ Error set_trading_stop: {e}", 'error')
            return False
    
    def set_conditional_stop(self, symbol, sl_price, position_size, position_type):
        """Conditional Stop Order"""
        try:
            side = "Sell" if position_type == "long" else "Buy"
            sl_price_str = f"{sl_price:.8f}".rstrip('0').rstrip('.')
            position_size_str = str(position_size)
            
            stop_params = {
                'category': "linear",
                'symbol': symbol,
                'side': side,
                'orderType': "Stop",
                'qty': position_size_str,
                'stopPrice': sl_price_str,
                'positionIdx': self.bot.get_position_idx(position_type),
                'reduceOnly': True,
                'timeInForce': "GTC",
                'triggerDirection': 1 if position_type == "long" else 2
            }
            
            if self.bot.use_demo_account:
                response = {'retCode': 0, 'result': {'orderId': f'DEMO_STOP_{symbol}_{int(time.time())}'}}
            else:
                response = self.bot.bybit_client.place_order(**stop_params)
            
            if response.get('retCode') == 0:
                sl_order_id = response.get('result', {}).get('orderId', 'CONDITIONAL_STOP')
                position = self.active_positions[symbol]
                position['sl_order_id'] = sl_order_id
                return True
            else:
                return False
                
        except Exception as e:
            ws_logger.log(f"❌ Error set_conditional_stop: {e}", 'error')
            return False
    
    def move_sl_to_breakeven(self, symbol):
        """Move SL to breakeven with profit protection"""
        try:
            if symbol not in self.active_positions:
                return False
            
            position = self.active_positions[symbol]
            
            if position['sl_moved_to_breakeven']:
                ws_logger.log(f"ℹ️ SL already at breakeven for {symbol}")
                return True
            
            entry_price = position['entry_price']
            
            # If profit protection is enabled, protect a percentage of profit
            if self.bot.risk_manager.profit_protection_percentage > 0 and position['max_profit'] > 0:
                protected_profit = position['max_profit'] * (self.bot.risk_manager.profit_protection_percentage / 100)
                position_type = position['position_type'].lower()
                
                if position_type == "long":
                    breakeven_price = entry_price * (1 + protected_profit / 100)
                else:
                    breakeven_price = entry_price * (1 - protected_profit / 100)
                
                ws_logger.log(f"💡 Moving SL to protect {protected_profit:.1f}% profit for {symbol}")
            else:
                breakeven_price = entry_price
                ws_logger.log(f"💡 Moving SL to breakeven for {symbol}")
            
            # Cancel old SL if exists
            if position['sl_order_id']:
                self.cancel_sl_order(symbol, position['sl_order_id'])
                position['sl_order_id'] = None
            
            # Set new SL
            success = self.set_stop_loss(symbol, breakeven_price)
            
            if success:
                position['sl_moved_to_breakeven'] = True
                ws_logger.log(f"🎉 SL moved to breakeven for {symbol}", 'success')
                
                socketio.emit('message', {
                    'type': 'position',
                    'action': 'breakeven',
                    'symbol': symbol,
                    'entry_price': entry_price
                })
                
                return True
            else:
                return False
                
        except Exception as e:
            ws_logger.log(f"❌ Error move_sl_to_breakeven: {e}", 'error')
            return False
    
    def cancel_sl_order(self, symbol, order_id):
        """Cancel Stop Loss order"""
        try:
            if not self.bot.bybit_client:
                return False
            
            if order_id.startswith('TRADING_STOP_'):
                return self.cancel_trading_stop(symbol)
            else:
                return self.cancel_order(symbol, order_id)
                
        except Exception as e:
            ws_logger.log(f"❌ Error cancel_sl_order: {e}", 'error')
            return False
    
    def cancel_trading_stop(self, symbol):
        """Cancel Trading Stop"""
        try:
            position = self.active_positions.get(symbol)
            if not position:
                return False
            
            position_type = position['position_type']
            
            trading_stop_params = {
                'category': "linear",
                'symbol': symbol,
                'stopLoss': "",
                'positionIdx': self.bot.get_position_idx(position_type)
            }
            
            if self.bot.use_demo_account:
                response = {'retCode': 0, 'result': {}}
            else:
                response = self.bot.bybit_client.set_trading_stop(**trading_stop_params)
            
            return response.get('retCode') == 0
                
        except Exception as e:
            ws_logger.log(f"❌ Error cancel_trading_stop: {e}", 'error')
            return False
    
    def cancel_order(self, symbol, order_id):
        """Cancel order"""
        try:
            if not self.bot.bybit_client:
                return False
            
            if self.bot.use_demo_account:
                return True
            
            cancel_params = {
                'category': "linear",
                'symbol': symbol,
                'orderId': order_id
            }
            
            response = self.bot.bybit_client.cancel_order(**cancel_params)
            return response.get('retCode') == 0
                
        except Exception as e:
            ws_logger.log(f"❌ Error cancel_order: {e}", 'error')
            return False
    
    def get_current_position_size(self, symbol):
        """Get current position size"""
        try:
            if not self.bot.bybit_client:
                return 0
            
            if self.bot.use_demo_account:
                # For demo return simulated size
                position = self.active_positions.get(symbol)
                if position:
                    return position.get('position_size', 0)
                return 0
            
            # Get real position from API
            try:
                positions_response = self.bot.bybit_client.get_positions(
                    category="linear",
                    symbol=symbol
                )
                
                if positions_response.get('retCode') == 0:
                    position_list = positions_response.get('result', {}).get('list', [])
                    
                    for pos in position_list:
                        if pos.get('symbol') == symbol:
                            size = float(pos.get('size', '0'))
                            if size > 0:
                                return size
                    
                return 0
                    
            except Exception as e:
                ws_logger.log(f"❌ API error get_positions: {e}", 'error')
                return 0
                
        except Exception as e:
            ws_logger.log(f"❌ Error get_current_position_size: {e}", 'error')
            return 0
    
    def get_current_price(self, symbol):
        """Get current price"""
        try:
            if not self.bot.bybit_client:
                return None
            
            if self.bot.use_demo_account:
                # Simulate price for demo
                position = self.active_positions.get(symbol)
                if position:
                    entry_price = position['entry_price']
                    import random
                    variation = random.uniform(-0.02, 0.02)
                    simulated_price = entry_price * (1 + variation)
                    return round(simulated_price, 8)
                return None
            
            # Get real price
            try:
                ticker_response = self.bot.bybit_client.get_tickers(
                    category="linear",
                    symbol=symbol
                )
                
                if ticker_response.get('retCode') == 0:
                    ticker_list = ticker_response.get('result', {}).get('list', [])
                    if ticker_list:
                        return float(ticker_list[0].get('lastPrice', '0'))
                
                return None
                
            except Exception as e:
                ws_logger.log(f"❌ API error get_tickers: {e}", 'error')
                return None
                
        except Exception as e:
            ws_logger.log(f"❌ Error get_current_price: {e}", 'error')
            return None
    
    def check_target_reached_by_price(self, symbol):
        """Enhanced target checking with partial closing"""
        try:
            if symbol not in self.active_positions:
                return False
            
            position = self.active_positions[symbol]
            targets = position.get('targets', {})
            filled_targets = position.get('filled_targets', set())
            position_type = position['position_type'].lower()
            entry_price = position['entry_price']
            breakeven_target = position.get('breakeven_target', 1)
            
            if not targets:
                return False
            
            current_price = self.get_current_price(symbol)
            if not current_price:
                return False
            
            position['last_price_check'] = current_price
            position['target_check_count'] += 1
            
            newly_filled = []
            
            for target_num, target_price in sorted(targets.items()):
                if target_num in filled_targets:
                    continue
                
                target_reached = False
                
                if position_type == "long":
                    if current_price >= target_price:
                        target_reached = True
                elif position_type == "short":
                    if current_price <= target_price:
                        target_reached = True
                
                if target_reached:
                    filled_targets.add(target_num)
                    newly_filled.append(target_num)
                    ws_logger.log(f"✅ Target {target_num} reached for {symbol}", 'success')
                    
                    # Execute partial close if enabled
                    if self.bot.risk_manager.partial_close_enabled:
                        tp_order = position['tp_orders'].get(target_num)
                        if tp_order and isinstance(tp_order, dict):
                            partial_percentage = tp_order.get('partial_percentage', 100)
                            position['partial_close_executed'][target_num] = partial_percentage
                            ws_logger.log(f"📊 Partial close {partial_percentage}% at TP{target_num}", 'info')
            
            if newly_filled:
                socketio.emit('message', {
                    'type': 'position',
                    'action': 'targets_hit',
                    'symbol': symbol,
                    'targets': newly_filled,
                    'current_price': current_price
                })
                
                # Check if breakeven target reached
                if breakeven_target in newly_filled and not position['sl_moved_to_breakeven'] and self.bot.auto_breakeven:
                    breakeven_success = self.move_sl_to_breakeven(symbol)
                    if breakeven_success:
                        ws_logger.log(f"🎉 BREAKEVEN activated for {symbol}!", 'success')
                
                # Update trailing stop if enabled
                if self.bot.risk_manager.trailing_stop_enabled:
                    self.update_trailing_stop(symbol)
                
                return True
            
            return False
            
        except Exception as e:
            ws_logger.log(f"❌ Error check_target_reached_by_price: {e}", 'error')
            return False
    
    def check_filled_orders(self, symbol):
        """Enhanced order checking with profit tracking"""
        try:
            if symbol not in self.active_positions:
                return
            
            position = self.active_positions[symbol]
            
            # Check emergency stop
            if self.check_emergency_stop(symbol):
                return
            
            # Check targets by price
            price_check_result = self.check_target_reached_by_price(symbol)
            if price_check_result:
                ws_logger.log(f"✅ New targets detected for {symbol}", 'success')
            
            # Update trailing stop
            if self.bot.risk_manager.trailing_stop_enabled:
                self.update_trailing_stop(symbol)
            
            # Check TP orders
            for target_num, tp_order_info in position['tp_orders'].items():
                if target_num not in position['filled_targets']:
                    order_id = tp_order_info['order_id'] if isinstance(tp_order_info, dict) else tp_order_info
                    if self.is_order_filled(symbol, order_id):
                        position['filled_targets'].add(target_num)
                        ws_logger.log(f"🎯 TP{target_num} filled for {symbol}!", 'success')
                        
                        # Calculate profit
                        entry_price = position['entry_price']
                        target_price = position['targets'].get(target_num)
                        position_type = position['position_type'].lower()
                        
                        if target_price:
                            if position_type == "long":
                                profit_pct = ((target_price - entry_price) / entry_price) * 100
                            else:
                                profit_pct = ((entry_price - target_price) / entry_price) * 100
                            
                            margin_used = position.get('margin_used', self.bot.default_amount)
                            leverage = position.get('leverage', self.bot.default_leverage)
                            estimated_profit = margin_used * leverage * (profit_pct / 100)
                            
                            # Account for partial close
                            if isinstance(tp_order_info, dict):
                                partial_percentage = tp_order_info.get('partial_percentage', 100)
                                estimated_profit = estimated_profit * (partial_percentage / 100)
                            
                            self.bot.risk_manager.record_trade_result(symbol, estimated_profit, True)
                        
                        breakeven_target = position.get('breakeven_target', 1)
                        if target_num == breakeven_target and not position['sl_moved_to_breakeven'] and self.bot.auto_breakeven:
                            self.move_sl_to_breakeven(symbol)
            
            # Check SL
            if position['sl_order_id']:
                if self.is_order_filled(symbol, position['sl_order_id']):
                    ws_logger.log(f"🛑 Stop Loss executed for {symbol}")
                    
                    # Record loss
                    entry_price = position['entry_price']
                    sl_price = position.get('stop_loss', entry_price)
                    position_type = position['position_type'].lower()
                    
                    if position_type == "long":
                        loss_pct = ((entry_price - sl_price) / entry_price) * 100
                    else:
                        loss_pct = ((sl_price - entry_price) / entry_price) * 100
                    
                    margin_used = position.get('margin_used', self.bot.default_amount)
                    leverage = position.get('leverage', self.bot.default_leverage)
                    estimated_loss = margin_used * leverage * (loss_pct / 100)
                    self.bot.risk_manager.record_trade_result(symbol, -estimated_loss, False)
                    
                    self.remove_position(symbol)
                    
        except Exception as e:
            ws_logger.log(f"❌ Error check_filled_orders: {e}", 'error')
    
    def is_order_filled(self, symbol, order_id):
        """Check if order is filled"""
        try:
            if not self.bot.bybit_client:
                return False
            
            if self.bot.use_demo_account:
                return self.simulate_order_fill(symbol, order_id)
            
            try:
                order_history = self.bot.bybit_client.get_order_history(
                    category="linear",
                    symbol=symbol,
                    orderId=order_id
                )
                
                if order_history.get('retCode') == 0:
                    orders = order_history.get('result', {}).get('list', [])
                    for order in orders:
                        if order.get('orderId') == order_id:
                            status = order.get('orderStatus')
                            return status in ['Filled', 'PartiallyFilled']
                
                return False
                
            except Exception as e:
                ws_logger.log(f"❌ Error checking order status: {e}", 'error')
                return False
            
        except Exception as e:
            ws_logger.log(f"❌ Error is_order_filled: {e}", 'error')
            return False
    
    def simulate_order_fill(self, symbol, order_id):
        """Enhanced order fill simulation for demo"""
        try:
            if symbol not in self.active_positions:
                return False
            
            position = self.active_positions[symbol]
            targets = position.get('targets', {})
            current_price = self.get_current_price(symbol)
            
            if not current_price:
                return False
            
            # Check TP orders
            for target_num, tp_order_info in position['tp_orders'].items():
                check_order_id = tp_order_info['order_id'] if isinstance(tp_order_info, dict) else tp_order_info
                if check_order_id == order_id:
                    target_price = targets.get(target_num)
                    if target_price:
                        position_type = position['position_type'].lower()
                        
                        if position_type == "long" and current_price >= target_price:
                            return True
                        elif position_type == "short" and current_price <= target_price:
                            return True
            
            # Check SL
            if position['sl_order_id'] == order_id:
                # Check trailing stop
                if position.get('trailing_stop_active') and position.get('trailing_stop_price'):
                    sl_price = position['trailing_stop_price']
                else:
                    sl_price = position.get('stop_loss')
                
                if sl_price:
                    position_type = position['position_type'].lower()
                    
                    if position_type == "long" and current_price <= sl_price:
                        return True
                    elif position_type == "short" and current_price >= sl_price:
                        return True
            
            return False
            
        except Exception as e:
            ws_logger.log(f"❌ Error simulate_order_fill: {e}", 'error')
            return False
    
    def remove_position(self, symbol):
        """Remove position from monitoring"""
        try:
            if symbol in self.active_positions:
                del self.active_positions[symbol]
                ws_logger.log(f"✅ Position {symbol} removed", 'success')
                
                socketio.emit('message', {
                    'type': 'position',
                    'action': 'removed',
                    'symbol': symbol
                })
        except Exception as e:
            ws_logger.log(f"❌ Error remove_position: {e}", 'error')
    
    def start_monitoring(self):
        """Start enhanced position monitoring"""
        if not self.monitoring_active:
            self.monitoring_active = True
            self.monitor_thread = threading.Thread(target=self._monitor_positions, daemon=True)
            self.monitor_thread.start()
            ws_logger.log("✅ Enhanced position monitoring started", 'success')
            
            socketio.emit('status_update', {'monitoring': True})
    
    def stop_monitoring(self):
        """Stop position monitoring"""
        self.monitoring_active = False
        if self.monitor_thread:
            self.monitor_thread.join(timeout=1)
        ws_logger.log("🛑 Position monitoring stopped")
        
        socketio.emit('status_update', {'monitoring': False})
    
    def _monitor_positions(self):
        """Enhanced monitoring thread"""
        ws_logger.log("🔄 Enhanced position monitoring thread started")
        
        while self.monitoring_active:
            try:
                active_symbols = list(self.active_positions.keys())
                
                if active_symbols:
                    ws_logger.log(f"👀 Monitoring {len(active_symbols)} positions")
                    
                    for symbol in active_symbols:
                        try:
                            self.check_filled_orders(symbol)
                            
                            position = self.active_positions.get(symbol)
                            if position:
                                filled_count = len(position.get('filled_targets', set()))
                                total_targets = len(position.get('targets', {}))
                                breakeven_status = "✅" if position.get('sl_moved_to_breakeven') else "❌"
                                trailing_status = "🔄" if position.get('trailing_stop_active') else "⏸️"
                                
                                ws_logger.log(f"📊 {symbol}: {filled_count}/{total_targets} targets, BE: {breakeven_status}, Trail: {trailing_status}")
                                
                        except Exception as e:
                            ws_logger.log(f"❌ Error monitoring {symbol}: {e}", 'error')
                
                time.sleep(10)  # Check every 10 seconds
                
            except Exception as e:
                ws_logger.log(f"❌ Error in monitoring loop: {e}", 'error')
                time.sleep(60)
        
        ws_logger.log("🛑 Monitoring thread ended")
    
    def get_positions_summary(self):
        """Get enhanced positions summary"""
        summary = []
        for symbol, position in self.active_positions.items():
            summary.append(self._position_to_dict(position))
        return summary


class TelegramTradingBot:
    """Enhanced main trading bot class"""
    
    def __init__(self):
        print(f"🚀 Initializing Trading Bot Pro Enhanced - {COMMERCIAL_VERSION}...")
        self.config = self.load_config()
        self.profile_manager = ProfileManager()
        self.risk_manager = RiskManager()
        self.position_manager = PositionManager(self)
        self.forwarder = TelegramForwarder(self)
        
        # Telegram
        self.telegram_token = self.config.get('Telegram', 'token', fallback='')
        self.telegram_chat_id = self.config.get('Telegram', 'chat_id', fallback='')
        
        # Bybit API
        self.bybit_api_key = self.config.get('Bybit', 'api_key', fallback='')
        self.bybit_api_secret = self.config.get('Bybit', 'api_secret', fallback='')
        self.bybit_subaccount = self.config.get('Bybit', 'subaccount', fallback='')
        self.bybit_platform = self.config.get('Bybit', 'platform', fallback='bybitglobal')
        self.position_mode = self.config.get('Bybit', 'position_mode', fallback='one_way')
        
        # Enhanced Trading settings
        self.default_leverage = int(self.config.get('Trading', 'default_leverage', fallback='10'))
        self.default_amount = float(self.config.get('Trading', 'default_amount', fallback='100'))
        self.use_percentage = self.config.get('Trading', 'use_percentage', fallback='False').lower() == 'true'
        self.position_size_type = self.config.get('Trading', 'position_size_type', fallback='fixed')  # fixed, percentage, dynamic
        self.percentage_of_balance = float(self.config.get('Trading', 'percentage_of_balance', fallback='10'))
        self.use_demo_account = self.config.get('Trading', 'use_demo_account', fallback='True').lower() == 'true'
        
        # Risk control
        self.max_position_size = float(self.config.get('Trading', 'max_position_size', fallback='1000'))
        self.risk_percent = float(self.config.get('Trading', 'risk_percent', fallback='2'))
        
        # TP/SL settings
        self.auto_tp_sl = self.config.get('Trading', 'auto_tp_sl', fallback='True').lower() == 'true'
        self.auto_breakeven = self.config.get('Trading', 'auto_breakeven', fallback='True').lower() == 'true'
        
        # Auto-execute
        self.auto_execute_signals = self.config.get('Trading', 'auto_execute_signals', fallback='True').lower() == 'true'
        
        # Initialize clients
        self.bybit_client = None
        self.telegram_bot = None
        self.telegram_app = None
        self.telegram_thread = None
        
        # State
        self.last_signal = None
        self.telegram_running = False
        
        print(f"✅ Trading Bot Pro Enhanced initialized - Version {COMMERCIAL_VERSION}")
    
    def load_config(self):
        """Load enhanced configuration"""
        config = configparser.ConfigParser()
        
        if os.path.exists(CONFIG_FILE):
            try:
                config.read(CONFIG_FILE, encoding='utf-8')
                print("✅ Configuration loaded")
            except Exception as e:
                print(f"⚠️ Error loading configuration: {e}")
        else:
            print("📄 Creating new enhanced configuration...")
            config['Telegram'] = {
                'token': '',
                'chat_id': ''
            }
            config['Bybit'] = {
                'api_key': '',
                'api_secret': '',
                'subaccount': '',
                'platform': 'bybitglobal',
                'position_mode': 'one_way'
            }
            config['Trading'] = {
                'default_leverage': '10',
                'default_amount': '100',
                'use_percentage': 'False',
                'position_size_type': 'fixed',
                'percentage_of_balance': '10',
                'use_demo_account': 'True',
                'auto_tp_sl': 'True',
                'auto_breakeven': 'True',
                'auto_execute_signals': 'True',
                'max_position_size': '1000',
                'risk_percent': '2'
            }
            config['Forwarder'] = {
                'api_id': '',
                'api_hash': '',
                'phone_number': '',
                'target_chat_id': '',
                'forward_all_messages': 'False',
                'monitored_channels': json.dumps([{
                    'id': ADMIN_CHANNEL_ID,
                    'name': ADMIN_CHANNEL_NAME
                }])
            }
            config['RiskManagement'] = {
                'max_daily_loss': '100',
                'max_weekly_loss': '500',
                'max_consecutive_losses': '3',
                'max_daily_trades': '10',
                'max_loss_percentage': '10',
                'cooldown_minutes': '60',
                'breakeven_target': '1',
                'min_margin_level': '150',
                'max_open_positions': '5',
                'max_position_percentage': '30',
                'trailing_stop_enabled': 'False',
                'trailing_stop_percentage': '2',
                'partial_close_enabled': 'True',
                'partial_close_targets': '[25, 50, 75]',
                'emergency_stop_loss': '50',
                'profit_protection_percentage': '80',
                'auto_deleverage_threshold': '120',
                'drawdown_limit': '15'
            }
            
            try:
                with open(CONFIG_FILE, 'w', encoding='utf-8') as configfile:
                    config.write(configfile)
                print("✅ New enhanced configuration created")
            except Exception as e:
                print(f"❌ Error creating configuration: {e}")
        
        return config
    
    def save_config(self):
        """Save enhanced configuration"""
        try:
            self.config['Telegram']['token'] = self.telegram_token
            self.config['Telegram']['chat_id'] = self.telegram_chat_id
            self.config['Bybit']['api_key'] = self.bybit_api_key
            self.config['Bybit']['api_secret'] = self.bybit_api_secret
            self.config['Bybit']['subaccount'] = self.bybit_subaccount
            self.config['Bybit']['platform'] = self.bybit_platform
            self.config['Bybit']['position_mode'] = self.position_mode
            self.config['Trading']['default_leverage'] = str(self.default_leverage)
            self.config['Trading']['default_amount'] = str(self.default_amount)
            self.config['Trading']['use_percentage'] = str(self.use_percentage)
            self.config['Trading']['position_size_type'] = self.position_size_type
            self.config['Trading']['percentage_of_balance'] = str(self.percentage_of_balance)
            self.config['Trading']['use_demo_account'] = str(self.use_demo_account)
            self.config['Trading']['auto_tp_sl'] = str(self.auto_tp_sl)
            self.config['Trading']['auto_breakeven'] = str(self.auto_breakeven)
            self.config['Trading']['auto_execute_signals'] = str(self.auto_execute_signals)
            self.config['Trading']['max_position_size'] = str(self.max_position_size)
            self.config['Trading']['risk_percent'] = str(self.risk_percent)
            
            if not self.config.has_section('RiskManagement'):
                self.config.add_section('RiskManagement')
            
            self.config['RiskManagement']['max_daily_loss'] = str(self.risk_manager.max_daily_loss)
            self.config['RiskManagement']['max_weekly_loss'] = str(self.risk_manager.max_weekly_loss)
            self.config['RiskManagement']['max_consecutive_losses'] = str(self.risk_manager.max_consecutive_losses)
            self.config['RiskManagement']['max_daily_trades'] = str(self.risk_manager.max_daily_trades)
            self.config['RiskManagement']['max_loss_percentage'] = str(self.risk_manager.max_loss_percentage)
            self.config['RiskManagement']['cooldown_minutes'] = str(self.risk_manager.cooldown_after_losses)
            self.config['RiskManagement']['breakeven_target'] = str(self.risk_manager.breakeven_target_choice)
            self.config['RiskManagement']['min_margin_level'] = str(self.risk_manager.min_margin_level)
            self.config['RiskManagement']['max_open_positions'] = str(self.risk_manager.max_open_positions)
            self.config['RiskManagement']['max_position_percentage'] = str(self.risk_manager.max_position_percentage)
            self.config['RiskManagement']['trailing_stop_enabled'] = str(self.risk_manager.trailing_stop_enabled)
            self.config['RiskManagement']['trailing_stop_percentage'] = str(self.risk_manager.trailing_stop_percentage)
            self.config['RiskManagement']['partial_close_enabled'] = str(self.risk_manager.partial_close_enabled)
            self.config['RiskManagement']['partial_close_targets'] = json.dumps(self.risk_manager.partial_close_targets)
            self.config['RiskManagement']['emergency_stop_loss'] = str(self.risk_manager.emergency_stop_loss)
            self.config['RiskManagement']['profit_protection_percentage'] = str(self.risk_manager.profit_protection_percentage)
            self.config['RiskManagement']['auto_deleverage_threshold'] = str(self.risk_manager.auto_deleverage_threshold)
            self.config['RiskManagement']['drawdown_limit'] = str(self.risk_manager.drawdown_limit)
            
            with open(CONFIG_FILE, 'w', encoding='utf-8') as configfile:
                self.config.write(configfile)
            
            ws_logger.log("✅ Enhanced configuration saved", 'success')
            return True
        except Exception as e:
            ws_logger.log(f"❌ Error saving configuration: {e}", 'error')
            return False
    
    def initialize_bybit_client(self):
        """Initialize Bybit API client"""
        try:
            if not BYBIT_AVAILABLE:
                ws_logger.log("❌ Pybit library not installed!", 'error')
                return False
            
            ws_logger.log("🚀 Initializing Bybit client...")
            
            if not self.bybit_api_key or not self.bybit_api_secret:
                ws_logger.log("❌ No Bybit API keys", 'error')
                self.bybit_client = None
                return False
            
            clean_api_key = self.bybit_api_key.strip()
            clean_api_secret = self.bybit_api_secret.strip()
            
            ws_logger.log(f"🔧 Platform: {self.bybit_platform}")
            ws_logger.log(f"🎮 Demo: {self.use_demo_account}")
            
            client_params = {
                'api_key': clean_api_key,
                'api_secret': clean_api_secret,
                'testnet': self.use_demo_account
            }
            
            self.bybit_client = HTTP(**client_params)
            
            # Test connection
            try:
                ws_logger.log("🧪 Testing connection...")
                server_time = self.bybit_client.get_server_time()
                
                if server_time.get('retCode') == 0:
                    ws_logger.log("✅ Bybit API connected", 'success')
                    
                    balance_info = self.get_wallet_balance()
                    if balance_info and balance_info.get('success'):
                        balance = balance_info.get('totalAvailableBalance', 0)
                        ws_logger.log(f"💰 Balance: {balance:.2f} USDT", 'success')
                        
                        # Update peak balance for drawdown calculation
                        self.risk_manager.update_peak_balance(balance)
                    
                    return True
                else:
                    error_msg = server_time.get('retMsg', 'Unknown error')
                    ws_logger.log(f"❌ Connection error: {error_msg}", 'error')
                    self.bybit_client = None
                    return False
                    
            except Exception as e:
                ws_logger.log(f"❌ Connection test error: {e}", 'error')
                self.bybit_client = None
                return False
                
        except Exception as e:
            ws_logger.log(f"❌ Client initialization error: {e}", 'error')
            self.bybit_client = None
            return False
    
    def get_wallet_balance(self):
        """Get wallet balance"""
        try:
            if not self.bybit_client:
                ws_logger.log("❌ No Bybit client", 'error')
                return None
            
            ws_logger.log("💰 Getting balance...")
            
            if self.bybit_subaccount:
                balance_response = self.bybit_client.get_wallet_balance(
                    accountType="UNIFIED",
                    memberId=self.bybit_subaccount
                )
            else:
                balance_response = self.bybit_client.get_wallet_balance(
                    accountType="UNIFIED"
                )
            
            if balance_response.get('retCode') == 0:
                balance_list = balance_response.get('result', {}).get('list', [])
                
                if balance_list:
                    account = balance_list[0]
                    total_margin_balance = float(account.get('totalMarginBalance', '0'))
                    total_wallet_balance = float(account.get('totalWalletBalance', '0'))
                    total_available_balance = float(account.get('totalAvailableBalance', '0'))
                    account_type = account.get('accountType', 'UNIFIED')
                    
                    ws_logger.log(f"✅ Balance retrieved", 'success')
                    ws_logger.log(f"💵 Available: {total_available_balance:.2f} USDT")
                    
                    # Update peak balance
                    self.risk_manager.update_peak_balance(total_wallet_balance)
                    
                    socketio.emit('message', {
                        'type': 'balance',
                        'balance': {
                            'totalMarginBalance': total_margin_balance,
                            'totalWalletBalance': total_wallet_balance,
                            'totalAvailableBalance': total_available_balance,
                            'accountType': account_type
                        }
                    })
                    
                    return {
                        'success': True,
                        'totalMarginBalance': total_margin_balance,
                        'totalWalletBalance': total_wallet_balance,
                        'totalAvailableBalance': total_available_balance,
                        'accountType': account_type
                    }
                else:
                    ws_logger.log("⚠️ No balance data", 'warning')
                    return None
            else:
                error_msg = balance_response.get('retMsg', 'Unknown error')
                ws_logger.log(f"❌ Error getting balance: {error_msg}", 'error')
                return None
                
        except Exception as e:
            ws_logger.log(f"❌ Error get_wallet_balance: {e}", 'error')
            return None
    
    def get_margin_info(self):
        """Get enhanced margin information"""
        try:
            if not self.bybit_client:
                return None
            
            balance_info = self.get_wallet_balance()
            if not balance_info or not balance_info.get('success'):
                return None
            
            total_margin = balance_info.get('totalMarginBalance', 0)
            total_available = balance_info.get('totalAvailableBalance', 0)
            total_wallet = balance_info.get('totalWalletBalance', 0)
            
            if total_margin > 0:
                margin_level = (total_available / total_margin) * 100
            else:
                margin_level = 100
            
            # Calculate margin usage
            margin_used = total_margin - total_available
            margin_usage_percentage = (margin_used / total_wallet * 100) if total_wallet > 0 else 0
            
            return {
                'margin_level': margin_level,
                'total_margin': total_margin,
                'total_available': total_available,
                'total_wallet': total_wallet,
                'margin_used': margin_used,
                'margin_usage_percentage': margin_usage_percentage,
                'is_safe': margin_level >= self.risk_manager.min_margin_level,
                'needs_deleverage': margin_level < self.risk_manager.auto_deleverage_threshold
            }
            
        except Exception as e:
            ws_logger.log(f"❌ Error getting margin info: {e}", 'error')
            return None
    
    def get_symbol_info(self, symbol):
        """Get symbol information"""
        try:
            if not self.bybit_client:
                return None
            
            instruments_response = self.bybit_client.get_instruments_info(
                category="linear",
                symbol=symbol
            )
            
            if instruments_response.get('retCode') == 0:
                instruments = instruments_response.get('result', {}).get('list', [])
                if instruments:
                    return instruments[0]
            
            return None
            
        except Exception as e:
            ws_logger.log(f"❌ Error get_symbol_info: {e}", 'error')
            return None
    
    def format_quantity(self, qty, symbol_info):
        """Format quantity according to symbol requirements"""
        try:
            if not symbol_info:
                return None
            
            qty_filter = symbol_info.get('lotSizeFilter', {})
            qty_step = float(qty_filter.get('qtyStep', '0.001'))
            min_qty = float(qty_filter.get('minOrderQty', '0'))
            max_qty = float(qty_filter.get('maxOrderQty', '0'))
            
            # Use Decimal for precise calculations
            qty_decimal = Decimal(str(qty))
            qty_step_decimal = Decimal(str(qty_step))
            
            if qty_step > 0:
                # Round to the nearest step
                qty_decimal = (qty_decimal / qty_step_decimal).quantize(Decimal('1'), rounding=ROUND_DOWN) * qty_step_decimal
            
            qty = float(qty_decimal)
            
            if min_qty > 0 and qty < min_qty:
                qty = min_qty
            if max_qty > 0 and qty > max_qty:
                qty = max_qty
            
            # Determine precision
            if qty_step < 1:
                precision = len(str(qty_step).split('.')[-1])
            else:
                precision = 0
            
            return round(qty, precision)
            
        except Exception as e:
            ws_logger.log(f"❌ Error format_quantity: {e}", 'error')
            return None
    
    def calculate_position_size(self, balance, entry_price, symbol_info=None):
        """Enhanced position size calculation"""
        try:
            amount_to_use = 0
            
            if self.position_size_type == 'percentage':
                # Use percentage of balance
                amount_to_use = balance * (self.percentage_of_balance / 100.0)
                ws_logger.log(f"📊 Using {self.percentage_of_balance}% of balance = {amount_to_use:.2f} USDT")
                
            elif self.position_size_type == 'dynamic':
                # Use dynamic sizing based on risk management
                amount_to_use = self.risk_manager.calculate_position_size(balance, self.risk_percent)
                ws_logger.log(f"📊 Dynamic sizing = {amount_to_use:.2f} USDT")
                
            else:  # fixed
                # Use fixed amount
                amount_to_use = min(self.default_amount, balance)
                ws_logger.log(f"💵 Using fixed amount: {amount_to_use:.2f} USDT")
            
            # Apply maximum position percentage limit
            max_allowed = balance * (self.risk_manager.max_position_percentage / 100)
            if amount_to_use > max_allowed:
                amount_to_use = max_allowed
                ws_logger.log(f"⚠️ Limited to max {self.risk_manager.max_position_percentage}% = {amount_to_use:.2f} USDT")
            
            # Apply absolute maximum position size
            position_value_usdt = amount_to_use * self.default_leverage
            if position_value_usdt > self.max_position_size:
                position_value_usdt = self.max_position_size
                amount_to_use = position_value_usdt / self.default_leverage
                ws_logger.log(f"⚠️ Limited to max position: {self.max_position_size} USDT")
            
            # Calculate quantity
            qty = position_value_usdt / entry_price
            
            if symbol_info:
                qty = self.format_quantity(qty, symbol_info)
            
            return {
                'margin_required': amount_to_use,
                'position_value': position_value_usdt,
                'quantity': qty,
                'leverage': self.default_leverage
            }
            
        except Exception as e:
            ws_logger.log(f"❌ Error calculating position size: {e}", 'error')
            return None
    
    def get_position_idx(self, position_type):
        """Get position index based on mode"""
        if self.position_mode == 'hedge':
            return 1 if position_type.lower() == 'long' else 2
        else:
            return 0
    
    def parse_trading_signal(self, text):
        """Enhanced signal parsing for commercial version"""
        try:
            ws_logger.log("🔍 Analyzing premium signal...", 'info')
            
            # Clean text
            text_clean = re.sub(r'[^\w\s\-\.\:,/@#]', ' ', text)
            text_clean = ' '.join(text_clean.split())
            
            # Enhanced patterns
            symbol_patterns = [
                r'#?([A-Z0-9]+USDT?)\b',
                r'([A-Z0-9]+)\s*/\s*USDT',
                r'Pair:\s*([A-Z0-9]+USDT?)',
            ]
            
            position_patterns = [
                r'\b(LONG|SHORT|Long|Short|long|short)\b',
                r'\b(BUY|SELL|Buy|Sell|buy|sell)\b',
                r'Direction:\s*(LONG|SHORT|Long|Short)',
            ]
            
            entry_patterns = [
                r'(?:Entry|entry|ENTRY|Zone|zone|ZONE|Buy|buy|BUY)[\s:]*([0-9]+\.?[0-9]*(?:\s*-\s*[0-9]+\.?[0-9]*)?)',
                r'Entry\s*Price[\s:]*([0-9]+\.?[0-9]*)',
                r'Open[\s:]*([0-9]+\.?[0-9]*)',
            ]
            
            target_patterns = [
                r'(?:Target|target|TARGET|TP|tp|Take\s*Profit)[\s#]*(\d+)[\s:]*([0-9]+\.?[0-9]*)',
                r'TP\s*(\d+)[\s:]*([0-9]+\.?[0-9]*)',
                r'T(\d+)[\s:]*([0-9]+\.?[0-9]*)',
            ]
            
            sl_patterns = [
                r'(?:Stop[\s-]?Loss|stop[\s-]?loss|SL|sl|STOP[\s-]?LOSS)[\s:]*([0-9]+\.?[0-9]*)',
                r'Stop[\s:]*([0-9]+\.?[0-9]*)',
                r'Risk[\s:]*([0-9]+\.?[0-9]*)',
            ]
            
            # Find elements
            symbol_match = None
            for pattern in symbol_patterns:
                symbol_match = re.search(pattern, text_clean)
                if symbol_match:
                    break
            
            position_match = None
            for pattern in position_patterns:
                position_match = re.search(pattern, text_clean)
                if position_match:
                    break
            
            entry_match = None
            for pattern in entry_patterns:
                entry_match = re.search(pattern, text_clean)
                if entry_match:
                    break
            
            target_matches = []
            for pattern in target_patterns:
                target_matches.extend(re.findall(pattern, text_clean))
            
            sl_match = None
            for pattern in sl_patterns:
                sl_match = re.search(pattern, text_clean)
                if sl_match:
                    break
            
            # Validate
            if not symbol_match or not position_match or not entry_match:
                ws_logger.log("❌ Missing required signal elements", 'error')
                return None
            
            # Process signal
            symbol = symbol_match.group(1).upper()
            if not symbol.endswith('USDT'):
                symbol += 'USDT'
            
            position_text = position_match.group(1).lower()
            if position_text in ['buy', 'long']:
                position_type = 'long'
            elif position_text in ['sell', 'short']:
                position_type = 'short'
            else:
                position_type = position_text
            
            entry_str = entry_match.group(1)
            if '-' in entry_str:
                prices = [float(p.strip()) for p in entry_str.split('-')]
                entry_price = sum(prices) / len(prices)
            else:
                entry_price = float(entry_str)
            
            targets = {}
            for target_num, target_price in target_matches:
                targets[int(target_num)] = float(target_price)
            
            stop_loss = float(sl_match.group(1)) if sl_match else None
            
            signal = {
                'symbol': symbol,
                'position_type': position_type,
                'entry_price': entry_price,
                'targets': targets,
                'stop_loss': stop_loss,
                'source': 'premium_channel'
            }
            
            ws_logger.log("✅ Premium signal recognized!", 'success')
            ws_logger.log(f"📋 {json.dumps(signal, indent=2)}")
            
            return signal
            
        except Exception as e:
            ws_logger.log(f"❌ Error parsing signal: {e}", 'error')
            return None
    
    def execute_trade(self, signal):
        """Enhanced trade execution with advanced features"""
        try:
            # Get current open positions count
            open_positions_count = len(self.position_manager.active_positions)
            
            # Check risk management with enhanced parameters
            balance_info = self.get_wallet_balance()
            margin_info = self.get_margin_info()
            
            if balance_info:
                allowed, reason = self.risk_manager.check_trading_allowed(
                    balance_info.get('totalAvailableBalance'),
                    margin_info,
                    open_positions_count
                )
                
                if not allowed:
                    return f"🚫 TRADING LOCKED!\n{reason}"
            
            # Check if deleverage needed
            if margin_info and margin_info['needs_deleverage']:
                return f"⚠️ DELEVERAGE REQUIRED!\nMargin Level: {margin_info['margin_level']:.1f}%\nRequired: {self.risk_manager.auto_deleverage_threshold}%"
            
            if not self.bybit_client:
                if not self.initialize_bybit_client():
                    return "❌ Error initializing Bybit client"
            
            symbol = signal['symbol']
            side = "Buy" if signal['position_type'] == "long" else "Sell"
            entry_price = signal['entry_price']
            
            ws_logger.log(f"🚀 Executing enhanced trade: {symbol} {side}", 'info')
            
            # Get symbol info
            symbol_info = self.get_symbol_info(symbol)
            if not symbol_info:
                return f"❌ Cannot get symbol info for {symbol}"
            
            # Get balance
            if not balance_info or not balance_info.get('success'):
                return "❌ Cannot get balance"
            
            available_balance = balance_info.get('totalAvailableBalance', 0)
            
            if available_balance <= 0:
                return f"❌ No available balance"
            
            # Calculate enhanced position size
            position_calc = self.calculate_position_size(available_balance, entry_price, symbol_info)
            
            if not position_calc:
                return f"❌ Error calculating position size"
            
            amount_to_use = position_calc['margin_required']
            position_value_usdt = position_calc['position_value']
            qty_formatted = position_calc['quantity']
            leverage = position_calc['leverage']
            
            if not qty_formatted or qty_formatted <= 0:
                return f"❌ Invalid position size"
            
            ws_logger.log(f"📊 Enhanced Position Details:")
            ws_logger.log(f"   💰 Margin: {amount_to_use:.2f} USDT")
            ws_logger.log(f"   ⚔️ Leverage: {leverage}x")
            ws_logger.log(f"   📈 Value: {position_value_usdt:.2f} USDT")
            ws_logger.log(f"   📊 Quantity: {qty_formatted} {symbol}")
            ws_logger.log(f"   📍 Entry: {entry_price}")
            
            # Set leverage
            try:
                ws_logger.log(f"⚔️ Setting leverage {leverage}x...")
                leverage_response = self.bybit_client.set_leverage(
                    category="linear",
                    symbol=symbol,
                    buyLeverage=str(leverage),
                    sellLeverage=str(leverage)
                )
                
                if leverage_response.get('retCode') == 0:
                    ws_logger.log(f"✅ Leverage set", 'success')
                    
            except Exception as e:
                ws_logger.log(f"⚠️ Leverage error: {e}", 'warning')
            
            # Create order
            order_params = {
                'category': "linear",
                'symbol': symbol,
                'side': side,
                'orderType': "Market",
                'qty': str(qty_formatted),
                'positionIdx': self.get_position_idx(signal['position_type'])
            }
            
            ws_logger.log(f"📤 Sending enhanced order...")
            
            if self.use_demo_account:
                ws_logger.log("🎮 DEMO MODE - SIMULATION", 'info')
                order_response = {
                    'retCode': 0,
                    'retMsg': 'Demo order simulated',
                    'result': {
                        'orderId': f'DEMO_{symbol}_{int(time.time())}',
                        'orderLinkId': f'demo_{int(time.time())}'
                    }
                }
                
                # Store position size for demo
                signal['position_size'] = qty_formatted
                signal['leverage'] = leverage
                signal['margin_used'] = amount_to_use
                
            else:
                ws_logger.log("💰 LIVE MODE - REAL TRADE", 'warning')
                order_response = self.bybit_client.place_order(**order_params)
                
                # Store position details
                signal['position_size'] = qty_formatted
                signal['leverage'] = leverage
                signal['margin_used'] = amount_to_use
            
            if order_response.get('retCode') == 0:
                order_id = order_response.get('result', {}).get('orderId', 'Unknown')
                ws_logger.log(f"✅ Enhanced order executed! ID: {order_id}", 'success')
                
                # Record trade
                self.risk_manager.total_trades_today += 1
                
                # Add position to enhanced monitoring
                if self.auto_tp_sl or self.auto_breakeven or self.risk_manager.trailing_stop_enabled:
                    ws_logger.log(f"🎯 Adding to enhanced monitoring...")
                    self.position_manager.add_position(symbol, signal, order_id)
                    
                    if not self.position_manager.monitoring_active:
                        self.position_manager.start_monitoring()
                
                result = f"""✅ ENHANCED TRADE EXECUTED!
{'=' * 40}
📊 Symbol: {symbol}
📈 Type: {signal['position_type'].upper()}
💰 Entry: {entry_price}
📊 Quantity: {qty_formatted}
💵 Value: {position_value_usdt:.2f} USDT
💳 Margin: {amount_to_use:.2f} USDT
⚔️ Leverage: {leverage}x
🎮 Mode: {'DEMO' if self.use_demo_account else 'LIVE'}
🆔 Order ID: {order_id}
{'=' * 40}"""
                
                # Add feature status
                features = []
                if self.auto_tp_sl:
                    features.append("🎯 Auto TP/SL")
                if self.auto_breakeven:
                    features.append(f"💡 Auto Breakeven (TP{self.risk_manager.breakeven_target_choice})")
                if self.risk_manager.trailing_stop_enabled:
                    features.append(f"🔄 Trailing Stop ({self.risk_manager.trailing_stop_percentage}%)")
                if self.risk_manager.partial_close_enabled:
                    features.append(f"📊 Partial Close ({', '.join(map(str, self.risk_manager.partial_close_targets))}%)")
                
                if features:
                    result += f"\n\n🚀 ACTIVE FEATURES:"
                    for feature in features:
                        result += f"\n{feature}"
                
                result += f"\n\n🛡️ RISK STATUS:"
                result += f"\n• Trades today: {self.risk_manager.total_trades_today}/{self.risk_manager.max_daily_trades}"
                result += f"\n• Open positions: {open_positions_count + 1}/{self.risk_manager.max_open_positions}"
                result += f"\n• Consecutive losses: {self.risk_manager.consecutive_losses}/{self.risk_manager.max_consecutive_losses}"
                result += f"\n• Win rate: {self.risk_manager.win_rate:.1f}%"
                
                if margin_info:
                    result += f"\n• Margin level: {margin_info['margin_level']:.1f}%"
                    result += f"\n• Margin used: {margin_info['margin_usage_percentage']:.1f}%"
                
                return result
                
            else:
                error_msg = order_response.get('retMsg', 'Unknown error')
                self.risk_manager.failed_trades_today += 1
                return f"❌ Order error: {error_msg}"
                
        except Exception as e:
            ws_logger.log(f"❌ Error execute_trade: {e}", 'error')
            return f"❌ Trade execution error: {str(e)}"


# === GLOBAL INSTANCES ===
bot = TelegramTradingBot()


# === SOCKET.IO HANDLERS ===
@socketio.on('connect')
def handle_connect():
    try:
        ws_logger.update_client_count(ws_logger.clients_connected + 1)
        emit('connected', {'message': 'Connected to Trading Bot Pro Enhanced'})
        ws_logger.log('🔌 Client connected', 'info')
    except Exception as e:
        logger.error(f"Socket.IO connect error: {e}")


@socketio.on('disconnect')
def handle_disconnect():
    try:
        ws_logger.update_client_count(max(0, ws_logger.clients_connected - 1))
        ws_logger.log('🔌 Client disconnected', 'info')
    except Exception as e:
        logger.error(f"Socket.IO disconnect error: {e}")


@socketio.on('request_status')
def handle_status_request():
    try:
        status = {
            'telegram_bot': getattr(bot, 'telegram_running', False),
            'forwarder': getattr(bot.forwarder, 'forwarder_running', False) if hasattr(bot, 'forwarder') else False,
            'monitoring': getattr(bot.position_manager, 'monitoring_active', False) if hasattr(bot, 'position_manager') else False,
            'trading_locked': bot.risk_manager.is_trading_locked if hasattr(bot, 'risk_manager') else False
        }
        emit('status_update', status)
    except Exception as e:
        logger.error(f"Socket.IO status error: {e}")


# === FLASK ROUTES ===

@app.route('/')
def index():
    try:
        if os.path.exists('templates/index.html'):
            return render_template('index.html')
        else:
            return """
            <!DOCTYPE html>
            <html>
            <head>
                <title>Trading Bot Pro Enhanced - Setup Required</title>
            </head>
            <body>
                <h1>Trading Bot Pro Enhanced - Commercial Version</h1>
                <p>Please add the UI file as templates/index.html</p>
            </body>
            </html>
            """
    except Exception as e:
        return f"<h1>Error</h1><p>{str(e)}</p>"


@app.route('/api/health', methods=['GET'])
def health_check():
    try:
        return jsonify({
            'status': 'ok',
            'message': f'Trading Bot Pro Enhanced {COMMERCIAL_VERSION} is running',
            'timestamp': datetime.now().isoformat(),
            'bot_initialized': hasattr(bot, 'config') and bot.config is not None
        })
    except Exception as e:
        return jsonify({'status': 'error', 'error': str(e)}), 500


@app.route('/api/config', methods=['GET', 'POST'])
def handle_config():
    try:
        if request.method == 'GET':
            config_data = {
                'bybit_api_key': getattr(bot, 'bybit_api_key', ''),
                'bybit_api_secret': getattr(bot, 'bybit_api_secret', ''),
                'bybit_subaccount': getattr(bot, 'bybit_subaccount', ''),
                'bybit_platform': getattr(bot, 'bybit_platform', 'bybitglobal'),
                'position_mode': getattr(bot, 'position_mode', 'one_way'),
                'default_leverage': getattr(bot, 'default_leverage', 10),
                'default_amount': getattr(bot, 'default_amount', 100),
                'use_percentage': getattr(bot, 'use_percentage', False),
                'position_size_type': getattr(bot, 'position_size_type', 'fixed'),
                'percentage_of_balance': getattr(bot, 'percentage_of_balance', 10),
                'use_demo_account': getattr(bot, 'use_demo_account', True),
                'auto_tp_sl': getattr(bot, 'auto_tp_sl', True),
                'auto_breakeven': getattr(bot, 'auto_breakeven', True),
                'auto_execute_signals': getattr(bot, 'auto_execute_signals', True),
                'max_position_size': getattr(bot, 'max_position_size', 1000),
                'risk_percent': getattr(bot, 'risk_percent', 2)
            }
            return jsonify(config_data)
        
        else:  # POST
            data = request.json
            if not data:
                return jsonify({'success': False, 'error': 'No data provided'}), 400
            
            bot.bybit_api_key = data.get('bybit_api_key', '')
            bot.bybit_api_secret = data.get('bybit_api_secret', '')
            bot.bybit_subaccount = data.get('bybit_subaccount', '')
            bot.bybit_platform = data.get('bybit_platform', 'bybitglobal')
            bot.position_mode = data.get('position_mode', 'one_way')
            bot.use_demo_account = data.get('use_demo_account', True)
            bot.auto_execute_signals = data.get('auto_execute_signals', True)
            
            if bot.save_config():
                return jsonify({'success': True, 'message': 'Configuration saved'})
            else:
                return jsonify({'success': False, 'error': 'Failed to save'}), 500
                
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/test-connection', methods=['POST'])
def test_connection():
    try:
        if bot.initialize_bybit_client():
            platform = 'Bybit Global' if bot.bybit_platform == 'bybitglobal' else 'Bybit Original'
            mode = 'Demo' if bot.use_demo_account else 'Live'
            return jsonify({
                'success': True,
                'platform': f'{platform} ({mode})',
                'message': 'Connection successful'
            })
        else:
            return jsonify({'success': False, 'error': 'Connection failed'}), 400
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/balance', methods=['GET'])
def get_balance():
    try:
        balance = bot.get_wallet_balance()
        if balance and balance.get('success'):
            return jsonify(balance)
        else:
            return jsonify({'success': False, 'error': 'Failed to get balance'}), 400
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/margin-info', methods=['GET'])
def get_margin_info():
    try:
        margin_info = bot.get_margin_info()
        if margin_info:
            return jsonify({
                'success': True,
                'margin_level': margin_info['margin_level'],
                'total_margin': margin_info['total_margin'],
                'total_available': margin_info['total_available'],
                'total_wallet': margin_info['total_wallet'],
                'margin_used': margin_info['margin_used'],
                'margin_usage_percentage': margin_info['margin_usage_percentage'],
                'is_safe': margin_info['is_safe'],
                'needs_deleverage': margin_info['needs_deleverage'],
                'min_required': bot.risk_manager.min_margin_level,
                'deleverage_threshold': bot.risk_manager.auto_deleverage_threshold
            })
        else:
            return jsonify({'success': False, 'error': 'Could not get margin info'}), 400
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/risk/status', methods=['GET'])
def get_risk_status():
    try:
        status = bot.risk_manager.get_risk_status()
        return jsonify(status)
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/risk/settings', methods=['GET', 'POST'])
def handle_risk_settings():
    try:
        if request.method == 'GET':
            return jsonify({
                'max_daily_loss': bot.risk_manager.max_daily_loss,
                'max_weekly_loss': bot.risk_manager.max_weekly_loss,
                'max_consecutive_losses': bot.risk_manager.max_consecutive_losses,
                'max_daily_trades': bot.risk_manager.max_daily_trades,
                'max_loss_percentage': bot.risk_manager.max_loss_percentage,
                'cooldown_minutes': bot.risk_manager.cooldown_after_losses,
                'breakeven_target': bot.risk_manager.breakeven_target_choice,
                'min_margin_level': bot.risk_manager.min_margin_level,
                'max_open_positions': bot.risk_manager.max_open_positions,
                'max_position_percentage': bot.risk_manager.max_position_percentage,
                'trailing_stop_enabled': bot.risk_manager.trailing_stop_enabled,
                'trailing_stop_percentage': bot.risk_manager.trailing_stop_percentage,
                'partial_close_enabled': bot.risk_manager.partial_close_enabled,
                'partial_close_targets': bot.risk_manager.partial_close_targets,
                'emergency_stop_loss': bot.risk_manager.emergency_stop_loss,
                'profit_protection_percentage': bot.risk_manager.profit_protection_percentage,
                'auto_deleverage_threshold': bot.risk_manager.auto_deleverage_threshold,
                'drawdown_limit': bot.risk_manager.drawdown_limit
            })
        else:  # POST
            data = request.json
            if bot.risk_manager.update_settings(data):
                bot.save_config()
                return jsonify({'success': True, 'message': 'Risk settings updated'})
            else:
                return jsonify({'success': False, 'error': 'Failed to update'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/risk/reset-daily', methods=['POST'])
def reset_daily_risk():
    try:
        bot.risk_manager.reset_daily_stats()
        return jsonify({'success': True, 'message': 'Daily statistics reset'})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/risk/unlock', methods=['POST'])
def unlock_trading():
    try:
        bot.risk_manager.is_trading_locked = False
        bot.risk_manager.consecutive_losses = 0
        bot.risk_manager.last_trade_time = None
        return jsonify({'success': True, 'message': 'Trading unlocked'})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/trading-settings', methods=['POST'])
def save_trading_settings():
    try:
        data = request.json
        
        bot.default_leverage = int(data.get('default_leverage', 10))
        bot.default_amount = float(data.get('default_amount', 100))
        bot.use_percentage = data.get('use_percentage', False)
        bot.position_size_type = data.get('position_size_type', 'fixed')
        bot.percentage_of_balance = float(data.get('percentage_of_balance', 10))
        bot.use_demo_account = data.get('use_demo_account', True)
        bot.auto_tp_sl = data.get('auto_tp_sl', True)
        bot.auto_breakeven = data.get('auto_breakeven', True)
        bot.max_position_size = float(data.get('max_position_size', 1000))
        bot.risk_percent = float(data.get('risk_percent', 2))
        
        if bot.save_config():
            return jsonify({'success': True, 'message': 'Trading settings saved'})
        else:
            return jsonify({'success': False, 'error': 'Failed to save'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/profiles', methods=['GET'])
def get_profiles():
    try:
        profiles = bot.profile_manager.list_profiles()
        return jsonify({'success': True, 'profiles': profiles})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/profiles/save', methods=['POST'])
def save_profile():
    try:
        data = request.json
        profile_name = data.get('name')
        
        if not profile_name:
            return jsonify({'success': False, 'error': 'Profile name required'}), 400
        
        config_data = {
            'default_leverage': bot.default_leverage,
            'default_amount': bot.default_amount,
            'position_size_type': bot.position_size_type,
            'percentage_of_balance': bot.percentage_of_balance,
            'max_position_size': bot.max_position_size,
            'risk_settings': bot.risk_manager.get_risk_status()['limits']
        }
        
        if bot.profile_manager.save_profile(profile_name, config_data):
            return jsonify({'success': True, 'message': f'Profile "{profile_name}" saved'})
        else:
            return jsonify({'success': False, 'error': 'Failed to save profile'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/profiles/load', methods=['POST'])
def load_profile():
    try:
        data = request.json
        profile_name = data.get('name')
        
        if not profile_name:
            return jsonify({'success': False, 'error': 'Profile name required'}), 400
        
        profile_data = bot.profile_manager.load_profile(profile_name)
        
        if profile_data:
            # Apply profile settings
            bot.default_leverage = profile_data.get('default_leverage', 10)
            bot.default_amount = profile_data.get('default_amount', 100)
            bot.position_size_type = profile_data.get('position_size_type', 'fixed')
            bot.percentage_of_balance = profile_data.get('percentage_of_balance', 10)
            bot.max_position_size = profile_data.get('max_position_size', 1000)
            
            # Apply risk settings
            risk_settings = profile_data.get('risk_settings', {})
            if risk_settings:
                bot.risk_manager.update_settings(risk_settings)
            
            bot.save_config()
            
            return jsonify({'success': True, 'message': f'Profile "{profile_name}" loaded'})
        else:
            return jsonify({'success': False, 'error': 'Profile not found'}), 404
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/profiles/delete', methods=['POST'])
def delete_profile():
    try:
        data = request.json
        profile_name = data.get('name')
        
        if not profile_name:
            return jsonify({'success': False, 'error': 'Profile name required'}), 400
        
        if bot.profile_manager.delete_profile(profile_name):
            return jsonify({'success': True, 'message': f'Profile "{profile_name}" deleted'})
        else:
            return jsonify({'success': False, 'error': 'Profile not found'}), 404
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/forwarder/config', methods=['POST'])
def save_forwarder_config():
    """Commercial version - simplified forwarder config"""
    try:
        data = request.json
        
        bot.forwarder.target_chat_id = data.get('target_chat_id', '')
        bot.forwarder.forward_all_messages = data.get('forward_all_messages', False)
        
        # Force admin channel
        bot.forwarder.monitored_channels = [{
            'id': ADMIN_CHANNEL_ID,
            'name': ADMIN_CHANNEL_NAME
        }]
        
        if bot.forwarder.save_forwarder_config():
            return jsonify({'success': True, 'message': 'Configuration saved'})
        else:
            return jsonify({'success': False, 'error': 'Failed to save'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/forwarder/start', methods=['POST'])
def start_forwarder():
    """Start forwarder with admin channel"""
    try:
        # Force admin channel
        bot.forwarder.monitored_channels = [{
            'id': ADMIN_CHANNEL_ID,
            'name': ADMIN_CHANNEL_NAME
        }]
        
        # Use internal credentials (would be set from environment in production)
        bot.forwarder.api_id = int(os.environ.get('TELETHON_API_ID', '123456'))
        bot.forwarder.api_hash = os.environ.get('TELETHON_API_HASH', 'demo_hash')
        bot.forwarder.phone_number = os.environ.get('TELETHON_PHONE', '+1234567890')
        
        if bot.forwarder.start_forwarder():
            return jsonify({'success': True, 'message': 'Forwarder started'})
        else:
            return jsonify({'success': False, 'error': 'Failed to start'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/forwarder/stop', methods=['POST'])
def stop_forwarder():
    try:
        if bot.forwarder.stop_forwarder():
            return jsonify({'success': True, 'message': 'Forwarder stopped'})
        else:
            return jsonify({'success': False, 'error': 'Failed to stop'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/forwarder/stats', methods=['GET'])
def get_forwarder_stats():
    try:
        stats = bot.forwarder.get_statistics()
        return jsonify({'success': True, 'stats': stats})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/positions', methods=['GET'])
def get_positions():
    try:
        positions = bot.position_manager.get_positions_summary()
        return jsonify({
            'success': True,
            'positions': positions,
            'monitoring_active': bot.position_manager.monitoring_active,
            'count': len(positions)
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/positions/monitoring/start', methods=['POST'])
def start_monitoring():
    try:
        bot.position_manager.start_monitoring()
        return jsonify({'success': True, 'message': 'Monitoring started'})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/positions/monitoring/stop', methods=['POST'])
def stop_monitoring():
    try:
        bot.position_manager.stop_monitoring()
        return jsonify({'success': True, 'message': 'Monitoring stopped'})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/positions/breakeven', methods=['POST'])
def set_breakeven():
    try:
        data = request.json
        symbol = data.get('symbol', '').upper()
        
        if not symbol:
            return jsonify({'success': False, 'error': 'Symbol required'}), 400
        
        if bot.position_manager.move_sl_to_breakeven(symbol):
            return jsonify({'success': True, 'message': f'Breakeven set for {symbol}'})
        else:
            return jsonify({'success': False, 'error': 'Failed to set breakeven'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/positions/close', methods=['POST'])
def close_position():
    try:
        data = request.json
        symbol = data.get('symbol', '').upper()
        
        if not symbol:
            return jsonify({'success': False, 'error': 'Symbol required'}), 400
        
        if bot.position_manager.close_position_market(symbol):
            return jsonify({'success': True, 'message': f'Position {symbol} closed'})
        else:
            return jsonify({'success': False, 'error': 'Failed to close position'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/positions/trailing-stop', methods=['POST'])
def set_trailing_stop():
    try:
        data = request.json
        symbol = data.get('symbol', '').upper()
        
        if not symbol:
            return jsonify({'success': False, 'error': 'Symbol required'}), 400
        
        if bot.position_manager.update_trailing_stop(symbol):
            return jsonify({'success': True, 'message': f'Trailing stop updated for {symbol}'})
        else:
            return jsonify({'success': False, 'error': 'Failed to update trailing stop'}), 500
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/history', methods=['GET'])
def get_trade_history():
    try:
        history = []
        if os.path.exists(TRADE_HISTORY_FILE):
            with open(TRADE_HISTORY_FILE, 'r', encoding='utf-8') as f:
                history = json.load(f)
        
        # Get last 100 trades
        recent_history = history[-100:] if len(history) > 100 else history
        
        return jsonify({
            'success': True,
            'history': recent_history,
            'total_trades': len(history)
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/statistics', methods=['GET'])
def get_statistics():
    try:
        risk_status = bot.risk_manager.get_risk_status()
        
        statistics = {
            'total_profit': risk_status['total_profit'],
            'total_loss': risk_status['total_loss'],
            'net_pnl': risk_status['total_profit'] - risk_status['total_loss'],
            'win_rate': risk_status['win_rate'],
            'total_trades': risk_status['total_trades'],
            'winning_trades': risk_status['winning_trades'],
            'losing_trades': risk_status['losing_trades'],
            'largest_win': risk_status['largest_win'],
            'largest_loss': risk_status['largest_loss'],
            'average_win': risk_status['average_win'],
            'average_loss': risk_status['average_loss'],
            'profit_factor': risk_status['profit_factor'],
            'sharpe_ratio': risk_status['sharpe_ratio'],
            'peak_balance': risk_status['peak_balance'],
            'current_drawdown': risk_status['current_drawdown']
        }
        
        return jsonify({'success': True, 'statistics': statistics})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/commercial-info', methods=['GET'])
def get_commercial_info():
    """Get commercial version information"""
    return jsonify({
        'version': COMMERCIAL_VERSION,
        'channel_id': ADMIN_CHANNEL_ID,
        'channel_name': ADMIN_CHANNEL_NAME,
        'features': {
            'auto_breakeven': True,
            'risk_management': True,
            'margin_protection': True,
            'multi_target': True,
            'position_monitoring': True,
            'trailing_stop': True,
            'partial_close': True,
            'emergency_stop': True,
            'profit_protection': True,
            'auto_deleverage': True,
            'position_profiles': True,
            'advanced_statistics': True,
            'kelly_criterion': True,
            'drawdown_protection': True
        },
        'limits': {
            'max_daily_loss': bot.risk_manager.max_daily_loss,
            'max_weekly_loss': bot.risk_manager.max_weekly_loss,
            'max_consecutive_losses': bot.risk_manager.max_consecutive_losses,
            'min_margin_level': bot.risk_manager.min_margin_level,
            'max_open_positions': bot.risk_manager.max_open_positions,
            'max_position_percentage': bot.risk_manager.max_position_percentage,
            'emergency_stop_loss': bot.risk_manager.emergency_stop_loss,
            'auto_deleverage_threshold': bot.risk_manager.auto_deleverage_threshold,
            'drawdown_limit': bot.risk_manager.drawdown_limit
        },
        'position_sizing': {
            'type': bot.position_size_type,
            'fixed_amount': bot.default_amount,
            'percentage': bot.percentage_of_balance,
            'max_position': bot.max_position_size,
            'risk_percent': bot.risk_percent
        }
    })


@app.route('/api/execute-signal', methods=['POST'])
def execute_signal():
    """Manually execute a trading signal"""
    try:
        data = request.json
        
        signal = {
            'symbol': data.get('symbol', '').upper(),
            'position_type': data.get('position_type', 'long'),
            'entry_price': float(data.get('entry_price', 0)),
            'targets': data.get('targets', {}),
            'stop_loss': float(data.get('stop_loss', 0)) if data.get('stop_loss') else None,
            'source': 'manual'
        }
        
        if not signal['symbol'] or not signal['entry_price']:
            return jsonify({'success': False, 'error': 'Symbol and entry price required'}), 400
        
        result = bot.execute_trade(signal)
        
        if "✅" in result:
            return jsonify({'success': True, 'message': result})
        else:
            return jsonify({'success': False, 'error': result}), 400
            
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/test-signal', methods=['POST'])
def test_signal():
    """Test signal parsing"""
    try:
        data = request.json
        text = data.get('text', '')
        
        if not text:
            return jsonify({'success': False, 'error': 'No text provided'}), 400
        
        signal = bot.parse_trading_signal(text)
        
        if signal:
            return jsonify({'success': True, 'signal': signal})
        else:
            return jsonify({'success': False, 'error': 'Could not parse signal'}), 400
            
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


# === BACKGROUND THREADS ===

def process_message_queue():
    """Process message queue"""
    while True:
        try:
            if not message_queue.empty() and ws_logger.clients_connected > 0:
                message = message_queue.get()
                socketio.emit('message', message)
        except Exception as e:
            logger.error(f"Error processing message queue: {e}")
        time.sleep(0.1)


def daily_reset_thread():
    """Reset daily statistics at midnight"""
    while True:
        try:
            now = datetime.now()
            midnight = datetime(now.year, now.month, now.day + 1, 0, 0, 0)
            seconds_until_midnight = (midnight - now).total_seconds()
            
            time.sleep(seconds_until_midnight)
            
            bot.risk_manager.reset_daily_stats()
            ws_logger.log("📅 Daily statistics reset", 'info')
            
        except Exception as e:
            logger.error(f"Error in daily reset thread: {e}")
            time.sleep(3600)


def position_performance_monitor():
    """Monitor position performance in background"""
    while True:
        try:
            if bot.position_manager.monitoring_active:
                positions = bot.position_manager.active_positions
                
                for symbol, position in positions.items():
                    current_price = bot.position_manager.get_current_price(symbol)
                    if current_price:
                        entry_price = position['entry_price']
                        position_type = position['position_type'].lower()
                        
                        if position_type == "long":
                            pnl_percentage = ((current_price - entry_price) / entry_price) * 100
                        else:
                            pnl_percentage = ((entry_price - current_price) / entry_price) * 100
                        
                        # Emit performance update
                        socketio.emit('position_performance', {
                            'symbol': symbol,
                            'pnl_percentage': round(pnl_percentage, 2),
                            'current_price': current_price,
                            'entry_price': entry_price
                        })
            
            time.sleep(30)  # Update every 30 seconds
            
        except Exception as e:
            logger.error(f"Error in performance monitor: {e}")
            time.sleep(60)


# Start background threads
threading.Thread(target=process_message_queue, daemon=True).start()
threading.Thread(target=daily_reset_thread, daemon=True).start()
threading.Thread(target=position_performance_monitor, daemon=True).start()


# === MAIN EXECUTION ===

if __name__ == '__main__':
    print("\n" + "="*70)
    print(f"🚀 TRADING BOT PRO ENHANCED - COMMERCIAL VERSION {COMMERCIAL_VERSION}")
    print("="*70)
    
    if not setup_ok:
        print("⚠️  Setup issues detected but continuing...")
    
    print("\n📋 ENHANCED FEATURES:")
    print("  ✅ Advanced Position Sizing (Fixed/Percentage/Dynamic)")
    print("  ✅ Kelly Criterion Optimization")
    print("  ✅ Trailing Stop Loss")
    print("  ✅ Partial Position Closing")
    print("  ✅ Emergency Stop Loss Protection")
    print("  ✅ Profit Protection System")
    print("  ✅ Auto-Deleverage Warning")
    print("  ✅ Drawdown Limit Protection")
    print("  ✅ Trading Profile Management")
    print("  ✅ Enhanced Statistics & Analytics")
    print("  ✅ Multi-Target Management")
    print("  ✅ Advanced Risk Management")
    
    print("\n📍 Open in browser: http://localhost:5000")
    print("🌐 API Health: http://localhost:5000/api/health")
    print("💡 Admin Channel: " + ADMIN_CHANNEL_NAME)
    print("🛡️ Risk Management: ENHANCED ACTIVE")
    print("="*70 + "\n")
    
    try:
        socketio.run(
            app, 
            debug=False,
            host='0.0.0.0', 
            port=5000,
            allow_unsafe_werkzeug=True
        )
    except Exception as e:
        print(f"❌ Failed to start server: {e}")
        sys.exit(1)