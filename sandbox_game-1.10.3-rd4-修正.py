import pygame
import random
import sys
import os
import json
import time
import math
import threading
import traceback
try:
    import numpy as np
except ImportError:
    np = None
from datetime import datetime
from collections import OrderedDict

# ---------------------- 全局配置与初始化 ----------------------
SCREEN_WIDTH = 800
SCREEN_HEIGHT = 600
BLOCK_SIZE = 32
FPS = 60
CHUNK_SIZE = 16
RENDER_DISTANCE = 3
Y_MAX = 128
WORLD_SEED = random.randint(0, 2**32 - 1)

# 性能优化配置
MAX_UPDATES_PER_FRAME = 50
USE_DOUBLE_BUFFER = True
FRAME_SKIP = 2

# 移动设备配置
IS_MOBILE = False
VIRTUAL_JOYSTICK_ENABLED = True
VIRTUAL_BUTTONS_ENABLED = True
JOYSTICK_RADIUS = 60
JOYSTICK_BASE_COLOR = (100, 100, 100, 150)
JOYSTICK_HANDLE_COLOR = (200, 200, 200, 200)
BUTTON_SIZE = 60
BUTTON_COLOR = (100, 100, 100, 150)
BUTTON_HIGHLIGHT_COLOR = (150, 150, 150, 200)

exe_dir = os.path.dirname(os.path.abspath(sys.executable))
SAVE_DIR = os.path.join(exe_dir, "save")
SCREENSHOT_DIR = os.path.join(exe_dir, "pic")
OGG_DIR = os.path.join(exe_dir, "ogg")
LOG_DIR = os.path.join(exe_dir, "log")
TOOL_DIR = os.path.join(exe_dir, "tools")
BG_PHOTO_PATH = "game_bg.PNG"

# 颜色定义
BLACK = (0, 0, 0)
WHITE = (255, 255, 255)
GREEN = (0, 255, 0)
BROWN = (139, 69, 19)
BLUE = (0, 0, 255)
GRAY = (128, 128, 128)
PROGRESS_BG = (50, 50, 50)
PROGRESS_FG = (255, 165, 0)
YELLOW = (255, 255, 0)
RED = (255, 0, 0)
ORANGE = (255, 140, 0)
DARK_GREEN = (0, 100, 0)
WOOD_BROWN = (160, 82, 45)
COAL_BLACK = (30, 30, 30)
MEAT_COLOR = (205, 133, 63)
SAND_COLOR = (238, 203, 173)
STONE_GRAY = (100, 100, 100)
DEEP_STONE = (70, 70, 70)
IRON_COLOR = (200, 200, 220)
GOLD_COLOR = (255, 215, 0)

# 方块类型配置
BLOCK_TYPES = {
    0: {"name": "空气", "color": BLACK, "breakable": False, "hardness": 0, "drop": 0, "tool_need": 0},
    1: {"name": "草块", "color": GREEN, "breakable": True, "hardness": 2, "drop": 2, "tool_need": 0},
    2: {"name": "泥土", "color": BROWN, "breakable": True, "hardness": 2, "drop": 2, "tool_need": 0},
    3: {"name": "石头", "color": STONE_GRAY, "breakable": True, "hardness": 5, "drop": 3, "tool_need": 1},
    4: {"name": "水", "color": BLUE, "breakable": False, "hardness": 0, "drop": 0, "tool_need": 0},
    5: {"name": "木头", "color": WOOD_BROWN, "breakable": True, "hardness": 3, "drop": 5, "tool_need": 0},
    6: {"name": "树叶", "color": DARK_GREEN, "breakable": True, "hardness": 1, "drop": 0, "tool_need": 0},
    7: {"name": "煤炭", "color": COAL_BLACK, "breakable": True, "hardness": 4, "drop": 7, "tool_need": 1},
    8: {"name": "工作台", "color": WOOD_BROWN, "breakable": True, "hardness": 3, "drop": 8, "tool_need": 0},
    9: {"name": "肉", "color": MEAT_COLOR, "breakable": False, "hardness": 0, "drop": 9, "tool_need": 0},
    10: {"name": "沙块", "color": SAND_COLOR, "breakable": True, "hardness": 2, "drop": 10, "tool_need": 0},
    11: {"name": "深层石", "color": DEEP_STONE, "breakable": True, "hardness": 6, "drop": 3, "tool_need": 1},
    12: {"name": "铁矿", "color": IRON_COLOR, "breakable": True, "hardness": 6, "drop": 12, "tool_need": 2},
    13: {"name": "金矿", "color": GOLD_COLOR, "breakable": True, "hardness": 7, "drop": 13, "tool_need": 2},
}

TOOL_TYPES = {
    0: {"name": "徒手", "durability": 0, "efficiency": 1.0, "breakable_blocks": [1, 2, 5, 6, 10]},
    1: {"name": "木镐", "durability": 60, "efficiency": 2.0, "breakable_blocks": [1, 2, 3, 5, 6, 7, 10]},
    2: {"name": "石镐", "durability": 132, "efficiency": 4.0, "breakable_blocks": [1, 2, 3, 5, 6, 7, 8, 10, 11]},
    3: {"name": "铁镐", "durability": 250, "efficiency": 6.0, "breakable_blocks": [1, 2, 3, 5, 6, 7, 8, 10, 11, 12]},
}

CRAFT_RECIPES = {
    8: {"name": "工作台", "need": {5: 3}, "output": 1},
    1: {"name": "木镐", "need": {5: 3, 2: 2}, "output": 1},
    2: {"name": "石镐", "need": {3: 3, 2: 2}, "output": 1},
    3: {"name": "铁镐", "need": {12: 3, 2: 2}, "output": 1},
}

# 全局变量
LOADED_CHUNKS = OrderedDict()
DROPS = []
MONSTERS = []
menu_bg = None
main_font = None
small_font = None
is_day = True
SOUNDS = {"dig": None, "place": None, "hurt": None}

# 性能监控
frame_count = 0
last_fps_time = time.time()
current_fps = 0
frame_skip_counter = 0
show_fps = True

# 虚拟摇杆状态
joystick_active = False
joystick_pos = (JOYSTICK_RADIUS + 20, SCREEN_HEIGHT - JOYSTICK_RADIUS - 20)
joystick_handle_pos = joystick_pos
joystick_vector = (0, 0)

# 虚拟按钮状态
button_jump_rect = pygame.Rect(SCREEN_WIDTH - BUTTON_SIZE - 20, SCREEN_HEIGHT - BUTTON_SIZE - 20, BUTTON_SIZE, BUTTON_SIZE)
button_inventory_rect = pygame.Rect(SCREEN_WIDTH - BUTTON_SIZE*2 - 40, SCREEN_HEIGHT - BUTTON_SIZE - 20, BUTTON_SIZE, BUTTON_SIZE)
button_action_rect = pygame.Rect(SCREEN_WIDTH - BUTTON_SIZE - 20, SCREEN_HEIGHT - BUTTON_SIZE*2 - 40, BUTTON_SIZE, BUTTON_SIZE)

# 设置选项
SETTINGS = {
    "virtual_joystick": True,
    "virtual_buttons": True,
    "sound_volume": 0.7,
    "music_volume": 0.5,
    "render_distance": 3,
    "fps_limit": 60,
    "log_enabled": True,  # 新增：日志开关
}

# ---------------------- 日志系统 ----------------------
class GameLogger:
    """游戏日志系统"""
    
    def __init__(self, log_dir, enabled=True):
        self.log_dir = log_dir
        self.enabled = enabled
        self.log_file = None
        self.console_output = True
        self.log_levels = {
            "INFO": "[INFO]",
            "WARNING": "[WARNING]",
            "ERROR": "[ERROR]",
            "FATAL": "[FATAL]",
            "EXIT": "[EXIT]"
        }
        
        # 确保日志目录存在
        if not os.path.exists(log_dir):
            os.makedirs(log_dir, exist_ok=True)
            
        # 创建日志文件
        if self.enabled:
            self._create_log_file()
    
    def _create_log_file(self):
        """创建日志文件"""
        try:
            timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
            log_filename = f"{timestamp}-sandboxlog.log"
            self.log_file_path = os.path.join(self.log_dir, log_filename)
            self.log_file = open(self.log_file_path, 'a', encoding='utf-8')
            
            # 写入文件头
            self._write_to_file(f"=== 沙盒游戏日志文件 ===\n")
            self._write_to_file(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            self._write_to_file(f"游戏版本: 1.10.3-rd3\n")
            self._write_to_file(f"操作系统: {sys.platform}\n")
            self._write_to_file("=" * 40 + "\n")
            
            return True
        except Exception as e:
            print(f"[ERROR] 创建日志文件失败: {e}")
            return False
    
    def _get_timestamp(self):
        """获取时间戳"""
        return datetime.now().strftime("[%H:%M:%S]")
    
    def _write_to_file(self, message):
        """写入日志文件"""
        if self.log_file and not self.log_file.closed:
            try:
                self.log_file.write(message)
                self.log_file.flush()
            except:
                pass
    
    def _format_message(self, level, message):
        """格式化日志消息"""
        timestamp = self._get_timestamp()
        level_str = self.log_levels.get(level, "[UNKNOWN]")
        return f"{timestamp} {level_str} {message}\n"
    
    def log(self, level, message):
        """记录日志"""
        if not self.enabled:
            return
            
        formatted = self._format_message(level, message)
        
        # 输出到控制台
        if self.console_output:
            print(formatted.rstrip())
        
        # 写入文件
        self._write_to_file(formatted)
    
    def info(self, message):
        """记录信息"""
        self.log("INFO", message)
    
    def warning(self, message):
        """记录警告"""
        self.log("WARNING", message)
    
    def error(self, message):
        """记录错误"""
        self.log("ERROR", message)
    
    def fatal(self, message):
        """记录致命错误"""
        self.log("FATAL", message)
    
    def exit(self, message, exit_code=0):
        """记录退出信息"""
        self.log("EXIT", f"{message}, Exit Code: {exit_code}")
    
    def exception(self, message, exception_obj=None):
        """记录异常"""
        if exception_obj:
            exc_info = traceback.format_exception(type(exception_obj), exception_obj, exception_obj.__traceback__)
            exc_str = "".join(exc_info)
            self.error(f"{message}\n异常详情:\n{exc_str}")
        else:
            self.error(message)
    
    def set_enabled(self, enabled):
        """启用/禁用日志"""
        self.enabled = enabled
        
        if enabled and not self.log_file:
            self._create_log_file()
        elif not enabled and self.log_file:
            self.close()
    
    def close(self):
        """关闭日志文件"""
        if self.log_file:
            try:
                self.log_file.close()
                self.log_file = None
            except:
                pass

# 全局日志实例
game_logger = None

# ---------------------- 柏林噪声核心函数 ----------------------
class PerlinNoise:
    """优化的柏林噪声生成器"""
    def __init__(self, seed=WORLD_SEED):
        self.seed = seed
        random.seed(seed)
        self.permutation = list(range(256))
        random.shuffle(self.permutation)
        self.p = self.permutation * 2
    
    def fade(self, t):
        """6t^5 - 15t^4 + 10t^3"""
        return t * t * t * (t * (t * 6 - 15) + 10)
    
    def lerp(self, t, a, b):
        """线性插值"""
        return a + t * (b - a)
    
    def grad(self, hash_val, x, y, z=0):
        """梯度函数"""
        h = hash_val & 15
        u = x if h < 8 else y
        v = y if h < 4 else (x if h in (12, 14) else z)
        return (u if (h & 1) == 0 else -u) + (v if (h & 2) == 0 else -v)
    
    def noise2d(self, x, y, frequency=1.0):
        """2D柏林噪声"""
        x *= frequency
        y *= frequency
        
        xi = int(x) & 255
        yi = int(y) & 255
        xf = x - int(x)
        yf = y - int(y)
        
        u = self.fade(xf)
        v = self.fade(yf)
        
        a = self.p[xi] + yi
        aa = self.p[a]
        ab = self.p[a + 1]
        b = self.p[xi + 1] + yi
        ba = self.p[b]
        bb = self.p[b + 1]
        
        x1 = self.lerp(u, self.grad(aa, xf, yf), self.grad(ba, xf - 1, yf))
        x2 = self.lerp(u, self.grad(ab, xf, yf - 1), self.grad(bb, xf - 1, yf - 1))
        
        return self.lerp(v, x1, x2)
    
    def octave_noise2d(self, x, y, octaves=4, persistence=0.5, frequency=1.0):
        """多层柏林噪声"""
        value = 0
        amplitude = 1.0
        max_value = 0
        
        for i in range(octaves):
            value += self.noise2d(x, y, frequency * (2 ** i)) * amplitude
            max_value += amplitude
            amplitude *= persistence
        
        return value / max_value

# ---------------------- 泰拉瑞亚地形生成器 ----------------------
class TerrainGenerator:
    """泰拉瑞亚风格地形生成器 - 多噪声混合"""
    
    def __init__(self, seed=WORLD_SEED):
        self.seed = seed
        self.perlin = PerlinNoise(seed)
        
        # 地形参数
        self.terrain_noise1 = PerlinNoise(seed * 2 + 1)
        self.terrain_noise2 = PerlinNoise(seed * 3 + 2)
        self.biome_noise = PerlinNoise(seed * 5 + 3)
        self.cave_noise1 = PerlinNoise(seed * 7 + 4)
        self.cave_noise2 = PerlinNoise(seed * 11 + 5)
        self.ore_noise = PerlinNoise(seed * 13 + 6)
        
        # 地表参数
        self.base_height = Y_MAX // 2
        self.amplitude = 20
        self.frequency = 0.01
        
        # 生物群系参数
        self.biome_size = 200
        self.biome_blend = 0.3
        
        # 洞穴参数
        self.cave_threshold = 0.4
        self.cave_frequency = 0.05
        self.deep_cave_threshold = 0.3
        
        # 矿石参数
        self.ore_frequency = 0.1
    
    def get_height(self, x):
        """获取地表高度 - 使用双噪声混合"""
        # 基础地形噪声
        base_noise = self.terrain_noise1.octave_noise2d(x, 0, octaves=6, persistence=0.5, frequency=self.frequency)
        
        # 细节地形噪声
        detail_noise = self.terrain_noise2.octave_noise2d(x, 100, octaves=8, persistence=0.7, frequency=self.frequency * 2)
        
        # 混合噪声
        height_noise = base_noise * 0.7 + detail_noise * 0.3
        
        # 计算高度
        height = self.base_height + height_noise * self.amplitude
        
        # 添加地形特征
        mountain_noise = abs(self.perlin.noise2d(x * 0.005, 0, 0.5))
        if mountain_noise > 0.8:
            height += mountain_noise * 30
        
        # 确保高度在合理范围内
        return max(20, min(height, Y_MAX - 30))
    
    def get_biome(self, x):
        """获取生物群系"""
        biome_value = self.biome_noise.noise2d(x / self.biome_size, 0, 1.0)
        
        if biome_value < -0.5:
            return "desert"  # 沙漠
        elif biome_value < 0:
            return "forest"  # 森林
        elif biome_value < 0.5:
            return "plains"  # 平原
        else:
            return "hills"   # 丘陵
    
    def is_cave(self, x, y):
        """判断是否是洞穴 - 多层洞穴噪声"""
        if y < 20:
            return False
        
        # 基础洞穴噪声
        cave1 = self.cave_noise1.octave_noise2d(x, y, octaves=4, persistence=0.5, frequency=self.cave_frequency)
        
        # 细节洞穴噪声
        cave2 = self.cave_noise2.octave_noise2d(x * 1.5, y * 1.5, octaves=2, persistence=0.3, frequency=self.cave_frequency * 2)
        
        # 组合洞穴噪声
        cave_value = (cave1 + cave2 * 0.3) * (1.0 + y / Y_MAX * 2)
        
        # 深层洞穴
        deep_factor = max(0, (y - Y_MAX * 0.7) / (Y_MAX * 0.3))
        if deep_factor > 0:
            deep_cave = self.perlin.noise2d(x * 0.02, y * 0.02, 0.3)
            cave_value = max(cave_value, deep_cave * deep_factor)
        
        return cave_value > self.cave_threshold
    
    def get_ore_at(self, x, y):
        """获取矿石类型"""
        if y < 30:
            return None
        
        ore_value = self.ore_noise.octave_noise2d(x, y, octaves=3, persistence=0.6, frequency=self.ore_frequency)
        
        # 按深度分布矿石
        if y < 50:
            if ore_value > 0.85:
                return 7
        elif y < 80:
            if ore_value > 0.9:
                return 12
        else:
            if ore_value > 0.95:
                return 13
            elif ore_value > 0.85:
                return 12
            elif ore_value > 0.7:
                return 7
        
        return None
    
    def get_surface_block(self, x, y, height, biome):
        """获取地表方块"""
        if y > height:
            return 0
        elif y == height:
            if biome == "desert":
                return 10
            else:
                return 1
        elif y >= height - 4:
            if biome == "desert":
                return 10
            else:
                return 2
        elif y >= height - 10:
            return 3
        elif y >= 40:
            return 11
        else:
            return 11
    
    def generate_chunk(self, chunk_x, chunk_y):
        """生成区块地形"""
        chunk_data = []
        
        for local_y in range(CHUNK_SIZE):
            world_y = chunk_y * CHUNK_SIZE + local_y
            row = []
            
            for local_x in range(CHUNK_SIZE):
                world_x = chunk_x * CHUNK_SIZE + local_x
                
                # 获取地表高度和生物群系
                surface_height = self.get_height(world_x)
                biome = self.get_biome(world_x)
                
                # 判断是否是洞穴
                if self.is_cave(world_x, world_y):
                    block_type = 0
                else:
                    # 获取基础方块
                    block_type = self.get_surface_block(world_x, world_y, surface_height, biome)
                    
                    # 检查矿石
                    if block_type in [3, 11]:
                        ore = self.get_ore_at(world_x, world_y)
                        if ore:
                            block_type = ore
                
                row.append(block_type)
            
            chunk_data.append(row)
        
        return chunk_data

# ---------------------- 性能优化函数 ----------------------
def get_current_fps():
    """获取当前FPS"""
    global frame_count, last_fps_time, current_fps
    frame_count += 1
    current_time = time.time()
    if current_time - last_fps_time >= 1.0:
        current_fps = frame_count
        frame_count = 0
        last_fps_time = current_time
    return current_fps

def limit_updates_per_frame(entities, max_updates=MAX_UPDATES_PER_FRAME):
    """限制每帧更新的实体数量"""
    if len(entities) <= max_updates:
        return entities
    return entities[:max_updates]

def should_update_this_frame():
    """帧跳过优化"""
    global frame_skip_counter
    frame_skip_counter += 1
    return frame_skip_counter % FRAME_SKIP == 0

# ---------------------- 虚拟控制函数 ----------------------
def draw_virtual_controls(screen):
    """绘制虚拟控制界面"""
    if not VIRTUAL_JOYSTICK_ENABLED and not VIRTUAL_BUTTONS_ENABLED:
        return
        
    if VIRTUAL_JOYSTICK_ENABLED:
        pygame.draw.circle(screen, JOYSTICK_BASE_COLOR, joystick_pos, JOYSTICK_RADIUS)
        pygame.draw.circle(screen, JOYSTICK_HANDLE_COLOR, joystick_handle_pos, JOYSTICK_RADIUS//2)
    
    if VIRTUAL_BUTTONS_ENABLED:
        pygame.draw.circle(screen, BUTTON_COLOR, button_jump_rect.center, BUTTON_SIZE//2)
        jump_text = small_font.render("跳", True, WHITE)
        screen.blit(jump_text, (button_jump_rect.centerx - jump_text.get_width()//2, 
                               button_jump_rect.centery - jump_text.get_height()//2))
        
        pygame.draw.circle(screen, BUTTON_COLOR, button_inventory_rect.center, BUTTON_SIZE//2)
        inv_text = small_font.render("包", True, WHITE)
        screen.blit(inv_text, (button_inventory_rect.centerx - inv_text.get_width()//2, 
                              button_inventory_rect.centery - inv_text.get_height()//2))
        
        pygame.draw.circle(screen, BUTTON_COLOR, button_action_rect.center, BUTTON_SIZE//2)
        action_text = small_font.render("动", True, WHITE)
        screen.blit(action_text, (button_action_rect.centerx - action_text.get_width()//2, 
                                 button_action_rect.centery - action_text.get_height()//2))

def handle_virtual_controls(event, player):
    """处理虚拟控制输入"""
    global joystick_active, joystick_handle_pos, joystick_vector
    
    if not VIRTUAL_JOYSTICK_ENABLED and not VIRTUAL_BUTTONS_ENABLED:
        return False
        
    if event.type == pygame.MOUSEBUTTONDOWN:
        pos = event.pos
        
        if VIRTUAL_JOYSTICK_ENABLED:
            distance = math.hypot(pos[0] - joystick_pos[0], pos[1] - joystick_pos[1])
            if distance <= JOYSTICK_RADIUS:
                joystick_active = True
                joystick_handle_pos = pos
                return True
        
        if VIRTUAL_BUTTONS_ENABLED:
            if button_jump_rect.collidepoint(pos):
                if player.on_ground:
                    player.velocity_y = -player.jump_power
                    player.on_ground = False
                return True
            elif button_inventory_rect.collidepoint(pos):
                player.bag_open = not player.bag_open
                return True
            elif button_action_rect.collidepoint(pos):
                return True
    
    elif event.type == pygame.MOUSEMOTION:
        if joystick_active and VIRTUAL_JOYSTICK_ENABLED:
            pos = event.pos
            dx = pos[0] - joystick_pos[0]
            dy = pos[1] - joystick_pos[1]
            distance = math.hypot(dx, dy)
            
            if distance <= JOYSTICK_RADIUS:
                joystick_handle_pos = pos
            else:
                angle = math.atan2(dy, dx)
                joystick_handle_pos = (
                    joystick_pos[0] + math.cos(angle) * JOYSTICK_RADIUS,
                    joystick_pos[1] + math.sin(angle) * JOYSTICK_RADIUS
                )
            
            joystick_vector = (
                (joystick_handle_pos[0] - joystick_pos[0]) / JOYSTICK_RADIUS,
                (joystick_handle_pos[1] - joystick_pos[1]) / JOYSTICK_RADIUS
            )
            return True
    
    elif event.type == pygame.MOUSEBUTTONUP:
        if joystick_active:
            joystick_active = False
            joystick_handle_pos = joystick_pos
            joystick_vector = (0, 0)
            return True
    
    return False

def update_player_movement_from_joystick(player, delta_time):
    """根据虚拟摇杆更新玩家移动"""
    if not joystick_active or not VIRTUAL_JOYSTICK_ENABLED:
        return
        
    move_speed = player.speed * delta_time * 60
    player.world_x += joystick_vector[0] * move_speed / BLOCK_SIZE
    player.world_z += joystick_vector[1] * move_speed / BLOCK_SIZE

# ---------------------- 工具模块 ----------------------
def init_sounds():
    global SOUNDS
    try:
        if not os.path.exists(TOOL_DIR):
            os.makedirs(TOOL_DIR, exist_ok=True)
        SOUNDS["dig"] = pygame.mixer.Sound(buffer=create_sine_wave(440, 0.1, 44100))
        SOUNDS["place"] = pygame.mixer.Sound(buffer=create_sine_wave(220, 0.1, 44100))
        SOUNDS["hurt"] = pygame.mixer.Sound(buffer=create_sine_wave(880, 0.1, 44100))
        
        for sound in SOUNDS.values():
            if sound:
                sound.set_volume(SETTINGS["sound_volume"])
                
        pygame.mixer.music.set_volume(SETTINGS["music_volume"])
    except Exception as e:
        if game_logger:
            game_logger.error(f"音效初始化失败：{str(e)}")

def create_sine_wave(freq, duration, sample_rate):
    samples = int(duration * sample_rate)
    if np is not None:
        t = np.linspace(0, duration, samples, endpoint=False)
        wave = 0.5 * np.sin(2 * np.pi * freq * t)
        wave = wave * 32767
        wave = wave.astype(np.int16)
        return wave.tobytes()
    else:
        wave = bytearray()
        for i in range(samples):
            t = i / sample_rate
            val = 0.5 * math.sin(2 * np.pi * freq * t)
            sample = int(val * 32767)
            wave.extend(sample.to_bytes(2, 'little', signed=True))
        return bytes(wave)

def play_sound(sound_name):
    if SOUNDS.get(sound_name):
        try:
            SOUNDS[sound_name].play()
        except Exception as e:
            if game_logger:
                game_logger.error(f"音效播放失败：{str(e)}")

def play_random_ogg_music():
    if not os.path.exists(OGG_DIR):
        if game_logger:
            game_logger.warning("音乐目录不存在，跳过播放")
        return
    ogg_files = [f for f in os.listdir(OGG_DIR) if f.lower().endswith(".ogg")]
    if not ogg_files:
        if game_logger:
            game_logger.warning("无ogg音乐文件，跳过播放")
        return
    try:
        random_ogg = random.choice(ogg_files)
        ogg_path = os.path.join(OGG_DIR, random_ogg)
        pygame.mixer.music.load(ogg_path)
        pygame.mixer.music.play()
        pygame.mixer.music.set_endevent(pygame.USEREVENT + 1)
        if game_logger:
            game_logger.info(f"播放音乐：{random_ogg}")
    except Exception as e:
        if game_logger:
            game_logger.error(f"音乐加载失败：{str(e)}")

def draw_infinite_map(screen, loaded_chunks, player):
    """优化的地图绘制函数"""
    player_screen_x = SCREEN_WIDTH // 2
    player_screen_y = SCREEN_HEIGHT // 2
    
    visible_rect = pygame.Rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT)
    
    for (chunk_x, chunk_z), chunk in loaded_chunks.items():
        chunk_screen_x = (chunk_x * CHUNK_SIZE - player.world_x) * BLOCK_SIZE + player_screen_x
        chunk_screen_z = (chunk_z * CHUNK_SIZE - player.world_z) * BLOCK_SIZE + player_screen_y
        
        chunk_rect = pygame.Rect(chunk_screen_x, chunk_screen_z, CHUNK_SIZE*BLOCK_SIZE, CHUNK_SIZE*BLOCK_SIZE)
        if not visible_rect.colliderect(chunk_rect):
            continue
            
        dist = math.hypot(chunk_x - player.world_x//CHUNK_SIZE, chunk_z - player.world_z//CHUNK_SIZE)
        alpha = max(50, 255 - int(dist / SETTINGS["render_distance"] * 200))
        
        for x in range(CHUNK_SIZE):
            for z_range in range(CHUNK_SIZE):
                block_screen_x = chunk_screen_x + x * BLOCK_SIZE
                block_screen_y = chunk_screen_z + z_range * BLOCK_SIZE
                
                if (block_screen_x + BLOCK_SIZE < 0 or block_screen_x > SCREEN_WIDTH or 
                    block_screen_y + BLOCK_SIZE < 0 or block_screen_y > SCREEN_HEIGHT):
                    continue
                    
                for y in range(Y_MAX-1, -1, -1):
                    block_id = chunk.blocks[x][y][z_range]
                    if block_id != 0:
                        block_surf = pygame.Surface((BLOCK_SIZE, BLOCK_SIZE))
                        block_surf.fill(BLOCK_TYPES[block_id]["color"])
                        block_surf.set_alpha(alpha)
                        screen.blit(block_surf, (block_screen_x, block_screen_y))
                        pygame.draw.rect(screen, GRAY, (block_screen_x, block_screen_y, BLOCK_SIZE, BLOCK_SIZE), 1)
                        break

def get_mouse_block(pos, player):
    """获取鼠标指向的方块"""
    mouse_world_x = player.world_x + (pos[0] - SCREEN_WIDTH//2) / BLOCK_SIZE
    mouse_world_z = player.world_z + (pos[1] - SCREEN_HEIGHT//2) / BLOCK_SIZE
    mouse_world_y = (pos[1] - SCREEN_HEIGHT//2) / BLOCK_SIZE + player.world_z
    
    mouse_world_x = max(0, min(mouse_world_x, CHUNK_SIZE * 1000 - 1))
    mouse_world_y = max(0, min(mouse_world_y, Y_MAX - 1))
    mouse_world_z = max(0, min(mouse_world_z, CHUNK_SIZE * 1000 - 1))
    
    return (int(math.floor(mouse_world_x)), int(math.floor(mouse_world_y)), int(math.floor(mouse_world_z)))

def draw_dig_progress(screen, target_block, player, dig_progress):
    if dig_progress <= 0:
        return
        
    block_world_x, block_world_y, block_world_z = target_block
    block_screen_x = int((block_world_x - player.world_x) * BLOCK_SIZE + SCREEN_WIDTH//2)
    block_screen_y = int((block_world_z - player.world_z) * BLOCK_SIZE + SCREEN_HEIGHT//2)
    
    if (block_screen_x < -BLOCK_SIZE or block_screen_x > SCREEN_WIDTH or
        block_screen_y < -BLOCK_SIZE or block_screen_y > SCREEN_HEIGHT):
        return
    
    bar_x = block_screen_x
    bar_y = block_screen_y + BLOCK_SIZE + 5
    pygame.draw.rect(screen, PROGRESS_BG, (bar_x, bar_y, BLOCK_SIZE, 6))
    progress_width = int(BLOCK_SIZE * (dig_progress / 100))
    pygame.draw.rect(screen, PROGRESS_FG, (bar_x, bar_y, progress_width, 6))
    
    flash_freq = max(50, 200 - int(dig_progress * 1.5))
    if int(time.time() * 1000) % flash_freq < flash_freq // 2:
        pygame.draw.rect(screen, YELLOW, (block_screen_x, block_screen_y, BLOCK_SIZE, BLOCK_SIZE), 2)

# ---------------------- 核心类定义 ----------------------
class DropItem:
    def __init__(self, x, y, block_id, count=1):
        self.world_x = x
        self.world_z = y
        self.block_id = block_id
        self.count = count
        self.velocity_z = 0
        self.on_ground = False
        self.spawn_time = time.time()
        self.last_update_time = time.time()

    def update(self, loaded_chunks):
        current_time = time.time()
        delta_time = min(0.1, current_time - self.last_update_time)
        self.last_update_time = current_time
        
        if not self.on_ground:
            self.velocity_z += 15 * delta_time
            self.velocity_z = min(self.velocity_z, 10)
            self.world_z += self.velocity_z * delta_time
            
            chunk_x = int(self.world_x // CHUNK_SIZE)
            chunk_z = int(self.world_z // CHUNK_SIZE)
            if (chunk_x, chunk_z) in loaded_chunks:
                chunk = loaded_chunks[(chunk_x, chunk_z)]
                in_chunk_x = int(self.world_x % CHUNK_SIZE)
                in_chunk_y = min(Y_MAX-1, max(0, int(self.world_z)))
                in_chunk_z = int(self.world_z % CHUNK_SIZE)
                
                if (0 <= in_chunk_x < CHUNK_SIZE and 0 <= in_chunk_y < Y_MAX and 
                    0 <= in_chunk_z < CHUNK_SIZE and chunk.blocks[in_chunk_x][in_chunk_y][in_chunk_z] != 0):
                    self.on_ground = True
                    self.velocity_z = 0
                    self.world_z = chunk_z * CHUNK_SIZE + in_chunk_z
        
        if time.time() - self.spawn_time > 300:
            return False
        return True

    def draw(self, screen, player):
        screen_x = int((self.world_x - player.world_x) * BLOCK_SIZE + SCREEN_WIDTH // 2)
        screen_y = int((self.world_z - player.world_z) * BLOCK_SIZE + SCREEN_HEIGHT // 2)
        
        if (screen_x < -16 or screen_x > SCREEN_WIDTH or 
            screen_y < -16 or screen_y > SCREEN_HEIGHT):
            return
            
        drop_rect = pygame.Rect(screen_x, screen_y, 16, 16)
        pygame.draw.rect(screen, BLOCK_TYPES[self.block_id]["color"], drop_rect)
        pygame.draw.rect(screen, WHITE, drop_rect, 1)
        
        if self.count > 1:
            count_text = small_font.render(str(self.count), True, WHITE)
            screen.blit(count_text, (screen_x + 8, screen_y))

class Chunk:
    def __init__(self, chunk_x, chunk_z, seed):
        self.chunk_x = chunk_x
        self.chunk_z = chunk_z
        self.seed = seed
        
        self.terrain_gen = TerrainGenerator(seed)
        
        self.blocks = self.generate_chunk_blocks()
        self.last_accessed = time.time()

    def generate_chunk_blocks(self):
        blocks = [[[0 for _ in range(CHUNK_SIZE)] for _ in range(Y_MAX)] for _ in range(CHUNK_SIZE)]
        
        chunk_data = self.terrain_gen.generate_chunk(self.chunk_x, self.chunk_z)
        
        for x in range(CHUNK_SIZE):
            for y in range(Y_MAX):
                if y < len(chunk_data) and x < len(chunk_data[0]):
                    blocks[x][y][0] = chunk_data[y][x]
        
        if random.random() < 0.1 and self.chunk_x == 0 and self.chunk_z == 0:
            for x in range(3, 13):
                surface_y = 0
                for y in range(Y_MAX-1, -1, -1):
                    if blocks[x][y][0] in [1, 2]:
                        surface_y = y
                        break
                
                if surface_y > 0 and random.random() < 0.3:
                    trunk_height = random.randint(4, 7)
                    for y in range(surface_y + 1, min(Y_MAX, surface_y + 1 + trunk_height)):
                        blocks[x][y][0] = 5
                    
                    leaves_radius = 2
                    leaf_top = min(Y_MAX-1, surface_y + trunk_height)
                    for dx in range(-leaves_radius, leaves_radius + 1):
                        for dy in range(-leaves_radius, 1):
                            nx = x + dx
                            ny = leaf_top + dy
                            if 0 <= nx < CHUNK_SIZE and 0 <= ny < Y_MAX and math.hypot(dx, dy) <= leaves_radius:
                                if blocks[nx][ny][0] == 0:
                                    blocks[nx][ny][0] = 6
        
        return blocks

class Player:
    def __init__(self, x, y, name="Player"):
        self.world_x = x
        self.world_z = y
        self.x = SCREEN_WIDTH // 2 - (BLOCK_SIZE//2//2)
        self.y = SCREEN_HEIGHT // 2 - BLOCK_SIZE//2
        self.z = 0
        self.width = BLOCK_SIZE // 2
        self.height = BLOCK_SIZE
        
        self.speed = 5
        self.jump_power = 12
        self.velocity_y = 0
        self.on_ground = False
        
        self.name = name
        self.hp = 100
        self.hunger = 100
        self.level = 1
        self.current_tool = 0
        self.tools = {0: 0, 1: 0, 2: 0, 3: 0}
        self.inventory = {1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 9: 0, 10: 0, 12: 0, 13: 0}
        self.last_z = self.z
        self.hunger_timer = 0
        self.last_update_time = time.time()
        
        self.bag_open = False
        self.bag_selected = 2
        self.bag_spacing = 10

    def update(self, loaded_chunks):
        current_time = time.time()
        delta_time = min(0.1, current_time - self.last_update_time)
        self.last_update_time = current_time
        
        self.velocity_y += 20 * delta_time
        self.velocity_y = min(self.velocity_y, 20)
        self.y += self.velocity_y
        
        player_rect = pygame.Rect(self.x, self.y, self.width, self.height)
        self.on_ground = False
        
        for (chunk_x, chunk_z), chunk in loaded_chunks.items():
            chunk_screen_x = chunk_x * CHUNK_SIZE * BLOCK_SIZE - self.world_x * BLOCK_SIZE + SCREEN_WIDTH//2
            chunk_screen_z = chunk_z * CHUNK_SIZE * BLOCK_SIZE - self.world_z * BLOCK_SIZE + SCREEN_HEIGHT//2
            
            for x in range(CHUNK_SIZE):
                for z_range in range(CHUNK_SIZE):
                    for y in range(Y_MAX):
                        block_id = chunk.blocks[x][y][z_range]
                        if block_id == 0:
                            continue
                            
                        block_screen_x = chunk_screen_x + x * BLOCK_SIZE
                        block_screen_y = chunk_screen_z + y * BLOCK_SIZE
                        block_rect = pygame.Rect(block_screen_x, block_screen_y, BLOCK_SIZE, BLOCK_SIZE)
                        
                        if player_rect.colliderect(block_rect):
                            if self.velocity_y > 0:
                                self.y = block_screen_y - self.height
                                self.velocity_y = 0
                                self.on_ground = True
                                self.z = y
                            elif self.velocity_y < 0:
                                self.y = block_screen_y + BLOCK_SIZE
                                self.velocity_y = 0
        
        keys = pygame.key.get_pressed()
        move_speed = self.speed * delta_time * 60
        
        if keys[pygame.K_a] or keys[pygame.K_LEFT]:
            self.world_x -= move_speed / BLOCK_SIZE
        if keys[pygame.K_d] or keys[pygame.K_RIGHT]:
            self.world_x += move_speed / BLOCK_SIZE
        if keys[pygame.K_w] or keys[pygame.K_UP]:
            self.world_z -= move_speed / BLOCK_SIZE
        if keys[pygame.K_s] or keys[pygame.K_DOWN]:
            self.world_z += move_speed / BLOCK_SIZE
            
        update_player_movement_from_joystick(self, delta_time)
            
        if (keys[pygame.K_SPACE]) and self.on_ground:
            self.velocity_y = -self.jump_power
            self.on_ground = False
        
        self.hunger_timer += 1
        if self.hunger_timer >= FPS * 30:
            self.hunger = max(0, self.hunger - 1)
            self.hunger_timer = 0
            
        if self.hunger >= 20 and self.hp < 100 and self.on_ground:
            if self.hunger_timer % (FPS * 5) == 0:
                self.hp = min(100, self.hp + 1)
                
        if self.on_ground and (self.last_z - self.z) >= 5:
            self.hp = max(0, self.hp - 10)
            play_sound("hurt")
            if game_logger:
                game_logger.info(f"玩家{self.name}高处掉落，HP:{self.hp}")
            
        self.last_z = self.z
        
        self.pick_up_drop()

    def pick_up_drop(self):
        global DROPS
        new_drops = []
        player_pos = (self.world_x, self.world_z)
        
        for drop in DROPS:
            distance = math.hypot(self.world_x - drop.world_x, self.world_z - drop.world_z)
            if distance <= 1.5:
                block_id = drop.block_id
                max_stack = 16
                current = self.inventory.get(block_id, 0)
                
                if current < max_stack:
                    take = min(drop.count, max_stack - current)
                    self.inventory[block_id] += take
                    drop.count -= take
                    
                    if drop.count > 0:
                        new_drops.append(drop)
                    else:
                        if game_logger:
                            game_logger.info(f"玩家{self.name}拾取了{BLOCK_TYPES[block_id]['name']}x{take}")
                else:
                    new_drops.append(drop)
            else:
                new_drops.append(drop)
                
        DROPS = new_drops

    def craft_tool(self, recipe_id):
        recipe = CRAFT_RECIPES.get(recipe_id)
        if not recipe:
            return False, "无此合成配方"
            
        for need_id, need_count in recipe["need"].items():
            if self.inventory.get(need_id, 0) < need_count:
                return False, f"材料不足：{BLOCK_TYPES[need_id]['name']}需{need_count}个"
                
        for need_id, need_count in recipe["need"].items():
            self.inventory[need_id] -= need_count
            
        self.tools[recipe_id] += 1
        self.current_tool = recipe_id
        if game_logger:
            game_logger.info(f"玩家{self.name}合成{TOOL_TYPES[recipe_id]['name']}")
        return True, f"合成成功：{TOOL_TYPES[recipe_id]['name']}"

    def draw(self, screen):
        pygame.draw.rect(screen, YELLOW, (self.x, self.y, self.width, self.height))
        
        hunger_bar_x = 10
        hunger_bar_y = 60
        pygame.draw.rect(screen, BROWN, (hunger_bar_x, hunger_bar_y, 100, 8))
        fill_width = int(self.hunger)
        pygame.draw.rect(screen, GREEN, (hunger_bar_x, hunger_bar_y, fill_width, 8))
        hunger_text = small_font.render("饥饿", True, WHITE)
        screen.blit(hunger_text, (hunger_bar_x, hunger_bar_y - 15))
        
        tool_text = small_font.render(f"工具：{TOOL_TYPES[self.current_tool]['name']}", True, WHITE)
        screen.blit(tool_text, (10, 85))
        
        if show_fps:
            fps_text = small_font.render(f"FPS: {get_current_fps()}", True, WHITE)
            screen.blit(fps_text, (SCREEN_WIDTH - 100, 10))
        
        if self.bag_open:
            self.draw_bag(screen)

    def draw_bag(self, screen):
        bag_rect = pygame.Rect(SCREEN_WIDTH//2 - 160, SCREEN_HEIGHT//2 - 130, 320, 260)
        pygame.draw.rect(screen, (50, 50, 50), bag_rect)
        pygame.draw.rect(screen, WHITE, bag_rect, 2)
        
        bag_title = main_font.render("物品栏", True, WHITE)
        screen.blit(bag_title, (SCREEN_WIDTH//2 - 30, SCREEN_HEIGHT//2 - 115))
        
        block_ids = [1, 2, 3, 5, 7, 8, 9, 10, 12, 13]
        for i, block_id in enumerate(block_ids):
            row = i // 3
            col = i % 3
            grid_x = SCREEN_WIDTH//2 - 130 + col * (70 + self.bag_spacing)
            grid_y = SCREEN_HEIGHT//2 - 90 + row * (60 + self.bag_spacing)
            
            grid_rect = pygame.Rect(grid_x, grid_y, 50, 50)
            if block_id == self.bag_selected:
                pygame.draw.rect(screen, YELLOW, grid_rect, 3)
            else:
                pygame.draw.rect(screen, WHITE, grid_rect, 1)
            
            block_rect = pygame.Rect(grid_x + 10, grid_y + 10, 30, 30)
            pygame.draw.rect(screen, BLOCK_TYPES[block_id]["color"], block_rect)
            
            count = self.inventory.get(block_id, 0)
            count_text = small_font.render(str(count), True, WHITE)
            screen.blit(count_text, (grid_x + 35, grid_y + 35))
            
            name_text = small_font.render(BLOCK_TYPES[block_id]["name"], True, WHITE)
            screen.blit(name_text, (grid_x + 5, grid_y + 65))
        
        craft_btn = pygame.Rect(SCREEN_WIDTH//2 - 80, SCREEN_HEIGHT//2 + 70, 160, 30)
        pygame.draw.rect(screen, GREEN, craft_btn)
        craft_text = small_font.render("合成木镐（3木头+2泥土）", True, BLACK)
        screen.blit(craft_text, (craft_btn.x + 5, craft_btn.y + 12))

    def to_save_data(self):
        return {
            "name": self.name,
            "hp": self.hp,
            "hunger": self.hunger,
            "level": self.level,
            "current_tool": self.current_tool,
            "tools": self.tools,
            "inventory": self.inventory,
            "position": {
                "world_x": self.world_x,
                "world_z": self.world_z,
                "z": self.z
            }
        }

    @staticmethod
    def from_save_data(data):
        player = Player(x=data["position"]["world_x"], y=data["position"]["world_z"], name=data["name"])
        player.hp = data["hp"]
        player.hunger = data.get("hunger", 100)
        player.level = data["level"]
        player.current_tool = data.get("current_tool", 0)
        player.tools = data.get("tools", {0: 0, 1: 0, 2: 0, 3: 0})
        inventory = data.get("inventory", {1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0})
        for item in [9, 10, 12, 13]:
            if item not in inventory:
                inventory[item] = 0
        player.inventory = inventory
        player.world_x = data["position"]["world_x"]
        player.world_z = data["position"]["world_z"]
        player.z = data["position"]["z"]
        return player

class Monster:
    def __init__(self, world_x, world_z):
        self.world_x = world_x
        self.world_z = world_z
        self.width = BLOCK_SIZE // 2
        self.height = BLOCK_SIZE
        self.hp = 50
        self.speed = 2
        self.attack_cooldown = 0
        self.attack_range = 1.5
        self.attack_damage = 5
        self.last_update_time = time.time()

    def update(self, player, loaded_chunks):
        current_time = time.time()
        delta_time = min(0.1, current_time - self.last_update_time)
        self.last_update_time = current_time
        
        if is_day:
            return False
        
        dx = player.world_x - self.world_x
        dz = player.world_z - self.world_z
        distance = math.hypot(dx, dz)
        
        if distance > 15:
            return True
        
        if distance > self.attack_range:
            move_speed = self.speed * delta_time * 60
            self.world_x += (dx / distance) * move_speed / BLOCK_SIZE
            self.world_z += (dz / distance) * move_speed / BLOCK_SIZE
        
        self.attack_cooldown = max(0, self.attack_cooldown - 1)
        if distance <= self.attack_range and self.attack_cooldown == 0:
            player.hp = max(0, player.hp - self.attack_damage)
            play_sound("hurt")
            self.attack_cooldown = FPS * 2
            if game_logger:
                game_logger.info(f"玩家{player.name}被僵尸攻击，HP:{player.hp}")
        
        chunk_x = int(self.world_x // CHUNK_SIZE)
        chunk_z = int(self.world_z // CHUNK_SIZE)
        if (chunk_x, chunk_z) in loaded_chunks:
            chunk = loaded_chunks[(chunk_x, chunk_z)]
            in_chunk_x = int(self.world_x % CHUNK_SIZE)
            in_chunk_y = min(Y_MAX-1, max(0, int(self.world_z)))
            in_chunk_z = int(self.world_z % CHUNK_SIZE)
            
            if (0 <= in_chunk_x < CHUNK_SIZE and 0 <= in_chunk_y < Y_MAX and 
                0 <= in_chunk_z < CHUNK_SIZE and chunk.blocks[in_chunk_x][in_chunk_y][in_chunk_z] != 0):
                self.world_x -= (dx / distance) * 0.1 if distance != 0 else 0
                self.world_z -= (dz / distance) * 0.1 if distance != 0 else 0
        
        if self.hp <= 0:
            if random.random() < 0.5:
                DROPS.append(DropItem(self.world_x, self.world_z, 9, 1))
            if game_logger:
                game_logger.info(f"僵尸死亡，位置:({int(self.world_x)},{int(self.world_z)})")
            return False
            
        return True

    def draw(self, screen, player):
        screen_x = int((self.world_x - player.world_x) * BLOCK_SIZE + SCREEN_WIDTH // 2)
        screen_y = int((self.world_z - player.world_z) * BLOCK_SIZE + SCREEN_HEIGHT // 2)
        
        if (screen_x < -self.width or screen_x > SCREEN_WIDTH or 
            screen_y < -self.height or screen_y > SCREEN_HEIGHT):
            return
            
        monster_rect = pygame.Rect(screen_x, screen_y, self.width, self.height)
        pygame.draw.rect(screen, RED, monster_rect)
        
        hp_bar_x = screen_x
        hp_bar_y = screen_y - 10
        pygame.draw.rect(screen, BLACK, (hp_bar_x, hp_bar_y, self.width, 5))
        fill_width = int(self.hp / 50 * self.width)
        pygame.draw.rect(screen, RED, (hp_bar_x, hp_bar_y, fill_width, 5))

# ---------------------- 设置管理 ----------------------
def load_settings():
    """加载设置"""
    global SETTINGS, VIRTUAL_JOYSTICK_ENABLED, VIRTUAL_BUTTONS_ENABLED, RENDER_DISTANCE, FPS
    settings_path = os.path.join(exe_dir, "settings.json")
    
    if os.path.exists(settings_path):
        try:
            with open(settings_path, "r", encoding="utf-8") as f:
                loaded_settings = json.load(f)
                SETTINGS.update(loaded_settings)
        except Exception as e:
            if game_logger:
                game_logger.error(f"加载设置失败: {e}")
    
    VIRTUAL_JOYSTICK_ENABLED = SETTINGS["virtual_joystick"]
    VIRTUAL_BUTTONS_ENABLED = SETTINGS["virtual_buttons"]
    RENDER_DISTANCE = SETTINGS["render_distance"]
    FPS = SETTINGS["fps_limit"]
    
    for sound in SOUNDS.values():
        if sound:
            sound.set_volume(SETTINGS["sound_volume"])
    pygame.mixer.music.set_volume(SETTINGS["music_volume"])
    
    if game_logger:
        game_logger.set_enabled(SETTINGS["log_enabled"])

def save_settings():
    """保存设置"""
    settings_path = os.path.join(exe_dir, "settings.json")
    
    try:
        with open(settings_path, "w", encoding="utf-8") as f:
            json.dump(SETTINGS, f, ensure_ascii=False, indent=2)
        if game_logger:
            game_logger.info("设置保存成功")
        return True
    except Exception as e:
        if game_logger:
            game_logger.error(f"保存设置失败: {e}")
        return False

# ---------------------- 存档模块 ----------------------
def get_save_path(player_name):
    return os.path.join(SAVE_DIR, f"{player_name}.json")

def create_json_file(file_path, data, loaded_chunks, world_seed):
    try:
        save_data = {
            "player": data["player"],
            "world_seed": world_seed,
            "loaded_chunks": {},
            "game_state": data["game_state"]
        }
        
        for (chunk_x, chunk_z), chunk in loaded_chunks.items():
            default_chunk = Chunk(chunk_x, chunk_z, world_seed)
            non_default_blocks = []
            for x in range(CHUNK_SIZE):
                for y in range(Y_MAX):
                    for z_range in range(CHUNK_SIZE):
                        current = chunk.blocks[x][y][z_range]
                        default = default_chunk.blocks[x][y][z_range]
                        if current != 0 and current != default:
                            non_default_blocks.append((x, y, z_range, current))
            save_data["loaded_chunks"][f"{chunk_x},{chunk_z}"] = non_default_blocks
        
        dir_path = os.path.dirname(file_path)
        if not os.path.exists(dir_path):
            os.makedirs(dir_path, exist_ok=True)
            
        player_name = data["player"]["name"]
        
        for i in range(2, 0, -1):
            old_backup = os.path.join(SAVE_DIR, f"{player_name}_backup{i}.json")
            new_backup = os.path.join(SAVE_DIR, f"{player_name}_backup{i+1}.json")
            if os.path.exists(old_backup):
                try:
                    os.rename(old_backup, new_backup)
                except Exception as e:
                    if game_logger:
                        game_logger.error(f"备份重命名失败: {e}")
        
        if os.path.exists(file_path):
            try:
                os.rename(file_path, os.path.join(SAVE_DIR, f"{player_name}_backup1.json"))
            except Exception as e:
                if game_logger:
                    game_logger.error(f"主存档重命名失败: {e}")
        
        with open(file_path, "w", encoding="utf-8") as f:
            json.dump(save_data, f, ensure_ascii=False, indent=2)
        
        if game_logger:
            game_logger.info(f"存档成功：{file_path}")
        return True, "存档成功（含3个备份）"
    except Exception as e:
        if game_logger:
            game_logger.error(f"存档失败：{str(e)}")
        return False, f"存档失败：{str(e)}"

def load_json_file(file_path):
    try:
        if not os.path.exists(file_path):
            player_name = os.path.basename(file_path).replace(".json", "")
            for i in range(1, 4):
                backup_path = os.path.join(SAVE_DIR, f"{player_name}_backup{i}.json")
                if os.path.exists(backup_path):
                    file_path = backup_path
                    if game_logger:
                        game_logger.info(f"加载备份：{backup_path}")
                    break
            else:
                return False, "主存档与备份均不存在", None, None, None
        
        with open(file_path, "r", encoding="utf-8") as f:
            save_data = json.load(f)
        
        if "world_seed" not in save_data or save_data["world_seed"] is None:
            save_data["world_seed"] = random.randint(0, 2**32 - 1)
            if game_logger:
                game_logger.info(f"补全随机种子：{save_data['world_seed']}")
        world_seed = save_data["world_seed"]
        
        loaded_chunks = OrderedDict()
        for chunk_key_str, non_default_blocks in save_data["loaded_chunks"].items():
            try:
                chunk_x, chunk_z = map(int, chunk_key_str.split(","))
                chunk = Chunk(chunk_x, chunk_z, world_seed)
                for (x, y, z_range, block_id) in non_default_blocks:
                    if 0 <= x < CHUNK_SIZE and 0 <= y < Y_MAX and 0 <= z_range < CHUNK_SIZE:
                        chunk.blocks[x][y][z_range] = block_id
                loaded_chunks[(chunk_x, chunk_z)] = chunk
            except Exception as e:
                if game_logger:
                    game_logger.error(f"加载区块失败 {chunk_key_str}: {e}")
                continue
        
        player_data = save_data["player"]
        if game_logger:
            game_logger.info(f"加载存档成功：{file_path}")
        return True, "加载成功", player_data, loaded_chunks, world_seed
    except Exception as e:
        if game_logger:
            game_logger.error(f"加载失败：{str(e)}")
        return False, f"加载失败：{str(e)}", None, None, None

def load_save_list():
    saves = []
    if not os.path.exists(SAVE_DIR):
        return saves
    try:
        for file in os.listdir(SAVE_DIR):
            if file.endswith(".json") and not file.startswith("_backup") and not file.endswith("_backup.json"):
                saves.append(file.replace(".json", ""))
    except Exception as e:
        if game_logger:
            game_logger.error(f"读取存档列表失败: {e}")
    return saves

# ---------------------- 界面模块 ----------------------
def show_main_menu(screen):
    """显示主菜单"""
    global menu_bg
    screen.blit(menu_bg, (0, 0))
    
    title_text = main_font.render("沙盒游戏 1.10.3-rd4 Sandbox", True, YELLOW)
    title_rect = title_text.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//8))
    screen.blit(title_text, title_rect)
    
    btn_width, btn_height = 350, 70
    btn_margin = 20
    btn_y_start = SCREEN_HEIGHT//4
    
    sandbox_btn = pygame.Rect(SCREEN_WIDTH//4 - btn_width//2, btn_y_start, btn_width, btn_height)
    wzmc_new_btn = pygame.Rect(3*SCREEN_WIDTH//4 - btn_width//2, btn_y_start, btn_width, btn_height)
    wzmc_load_btn = pygame.Rect(SCREEN_WIDTH//4 - btn_width//2, btn_y_start + btn_height + btn_margin, btn_width, btn_height)
    settings_btn = pygame.Rect(3*SCREEN_WIDTH//4 - btn_width//2, btn_y_start + btn_height + btn_margin, btn_width, btn_height)
    resolution_btn = pygame.Rect(SCREEN_WIDTH//4 - btn_width//2, btn_y_start + 2*(btn_height + btn_margin), btn_width, btn_height)
    controls_btn = pygame.Rect(3*SCREEN_WIDTH//4 - btn_width//2, btn_y_start + 2*(btn_height + btn_margin), btn_width, btn_height)
    about_btn = pygame.Rect(SCREEN_WIDTH//4 - btn_width//2, btn_y_start + 3*(btn_height + btn_margin), btn_width, btn_height)
    quit_btn = pygame.Rect(3*SCREEN_WIDTH//4 - btn_width//2, btn_y_start + 3*(btn_height + btn_margin), btn_width, btn_height)
    
    pygame.draw.rect(screen, GREEN, sandbox_btn)
    pygame.draw.rect(screen, BROWN, wzmc_new_btn)
    pygame.draw.rect(screen, BLUE, wzmc_load_btn)
    pygame.draw.rect(screen, ORANGE, settings_btn)
    pygame.draw.rect(screen, YELLOW, resolution_btn)
    pygame.draw.rect(screen, (100, 100, 255), controls_btn)
    pygame.draw.rect(screen, (200, 100, 200), about_btn)
    pygame.draw.rect(screen, RED, quit_btn)
    
    screen.blit(small_font.render("沙盒模式", True, BLACK), (sandbox_btn.x + btn_width//2 - 40, sandbox_btn.y + btn_height//2 - 10))
    screen.blit(small_font.render("新游戏", True, BLACK), (wzmc_new_btn.x + btn_width//2 - 30, wzmc_new_btn.y + btn_height//2 - 10))
    screen.blit(small_font.render("加载存档", True, BLACK), (wzmc_load_btn.x + btn_width//2 - 40, wzmc_load_btn.y + btn_height//2 - 10))
    screen.blit(small_font.render("游戏设置", True, BLACK), (settings_btn.x + btn_width//2 - 40, settings_btn.y + btn_height//2 - 10))
    screen.blit(small_font.render("分辨率", True, BLACK), (resolution_btn.x + btn_width//2 - 30, resolution_btn.y + btn_height//2 - 10))
    screen.blit(small_font.render("控制设置", True, BLACK), (controls_btn.x + btn_width//2 - 40, controls_btn.y + btn_height//2 - 10))
    screen.blit(small_font.render("关于游戏", True, BLACK), (about_btn.x + btn_width//2 - 40, about_btn.y + btn_height//2 - 10))
    screen.blit(small_font.render("退出游戏", True, BLACK), (quit_btn.x + btn_width//2 - 40, quit_btn.y + btn_height//2 - 10))
    
    pygame.display.flip()
    
    return (sandbox_btn, wzmc_new_btn, wzmc_load_btn, settings_btn, 
            resolution_btn, controls_btn, about_btn, quit_btn)

def show_settings_menu(screen, scroll_offset=0):
    """显示设置菜单 - 支持滚动"""
    screen.fill(BLACK)
    title_text = main_font.render("游戏设置", True, WHITE)
    title_rect = title_text.get_rect(center=(SCREEN_WIDTH//2, 60))
    screen.blit(title_text, title_rect)
    
    btn_width, btn_height = 400, 50
    btn_margin = 15
    btn_y_start = 120
    
    settings_items = []
    
    # 虚拟摇杆开关
    joystick_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, GREEN if SETTINGS["virtual_joystick"] else RED, joystick_btn)
    joystick_text = small_font.render(f"虚拟摇杆: {'开' if SETTINGS['virtual_joystick'] else '关'}", True, BLACK)
    screen.blit(joystick_text, (joystick_btn.x + 20, joystick_btn.y + btn_height//2 - 10))
    settings_items.append(("joystick", joystick_btn))
    
    # 虚拟按钮开关
    buttons_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start + (btn_height + btn_margin) - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, GREEN if SETTINGS["virtual_buttons"] else RED, buttons_btn)
    buttons_text = small_font.render(f"虚拟按钮: {'开' if SETTINGS['virtual_buttons'] else '关'}", True, BLACK)
    screen.blit(buttons_text, (buttons_btn.x + 20, buttons_btn.y + btn_height//2 - 10))
    settings_items.append(("buttons", buttons_btn))
    
    # 声音音量
    sound_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start + 2*(btn_height + btn_margin) - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, BLUE, sound_btn)
    sound_text = small_font.render(f"声音音量: {int(SETTINGS['sound_volume'] * 100)}%", True, BLACK)
    screen.blit(sound_text, (sound_btn.x + 20, sound_btn.y + btn_height//2 - 10))
    settings_items.append(("sound", sound_btn))
    
    # 音乐音量
    music_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start + 3*(btn_height + btn_margin) - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, BLUE, music_btn)
    music_text = small_font.render(f"音乐音量: {int(SETTINGS['music_volume'] * 100)}%", True, BLACK)
    screen.blit(music_text, (music_btn.x + 20, music_btn.y + btn_height//2 - 10))
    settings_items.append(("music", music_btn))
    
    # 渲染距离
    render_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start + 4*(btn_height + btn_margin) - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, ORANGE, render_btn)
    render_text = small_font.render(f"渲染距离: {SETTINGS['render_distance']}", True, BLACK)
    screen.blit(render_text, (render_btn.x + 20, render_btn.y + btn_height//2 - 10))
    settings_items.append(("render", render_btn))
    
    # FPS限制
    fps_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start + 5*(btn_height + btn_margin) - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, ORANGE, fps_btn)
    fps_text = small_font.render(f"FPS限制: {SETTINGS['fps_limit']}", True, BLACK)
    screen.blit(fps_text, (fps_btn.x + 20, fps_btn.y + btn_height//2 - 10))
    settings_items.append(("fps", fps_btn))
    
    # 日志开关
    log_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start + 6*(btn_height + btn_margin) - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, GREEN if SETTINGS["log_enabled"] else RED, log_btn)
    log_text = small_font.render(f"游戏日志: {'开' if SETTINGS['log_enabled'] else '关'}", True, BLACK)
    screen.blit(log_text, (log_btn.x + 20, log_btn.y + btn_height//2 - 10))
    settings_items.append(("log", log_btn))
    
    # 返回按钮
    back_btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y_start + 7*(btn_height + btn_margin) - scroll_offset, btn_width, btn_height)
    pygame.draw.rect(screen, GRAY, back_btn)
    back_text = small_font.render("返回主菜单", True, BLACK)
    screen.blit(back_text, (back_btn.x + btn_width//2 - 40, back_btn.y + btn_height//2 - 10))
    settings_items.append(("back", back_btn))
    
    # 显示滚动提示
    if btn_y_start + 8*(btn_height + btn_margin) - scroll_offset > SCREEN_HEIGHT:
        tip_text = small_font.render("使用鼠标滚轮上下滚动", True, (150, 150, 150))
        screen.blit(tip_text, (SCREEN_WIDTH//2 - 100, SCREEN_HEIGHT - 30))
    
    pygame.display.flip()
    
    return settings_items

def show_save_list(screen, scroll_offset, btn_spacing, visible_btn_count):
    screen.fill(BLACK)
    title_text = main_font.render("选择wzmc存档", True, WHITE)
    title_rect = title_text.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//8))
    screen.blit(title_text, title_rect)
    
    saves = load_save_list()
    btn_list = []
    btn_width, btn_height = 350, 50
    btn_y_start = SCREEN_HEIGHT//4
    
    for i, save_name in enumerate(saves):
        btn_y = btn_y_start + i * (btn_spacing + 10) - scroll_offset
        if btn_y + btn_height < 0 or btn_y > SCREEN_HEIGHT - 150:
            continue
        btn = pygame.Rect(SCREEN_WIDTH//2 - btn_width//2, btn_y, btn_width, btn_height)
        pygame.draw.rect(screen, ORANGE, btn)
        screen.blit(small_font.render(f"存档 {i+1}: {save_name}", True, BLACK), (btn.x + 20, btn.y + 12))
        btn_list.append((btn, save_name))
    
    back_btn = pygame.Rect(SCREEN_WIDTH//4 - 100, SCREEN_HEIGHT - 110, 200, 50)
    delete_btn = pygame.Rect(SCREEN_WIDTH//2 - 100, SCREEN_HEIGHT - 110, 200, 50)
    import_btn = pygame.Rect(3*SCREEN_WIDTH//4 - 100, SCREEN_HEIGHT - 110, 200, 50)
    
    pygame.draw.rect(screen, GRAY, back_btn)
    pygame.draw.rect(screen, RED, delete_btn)
    pygame.draw.rect(screen, YELLOW, import_btn)
    
    screen.blit(small_font.render("返回主菜单", True, BLACK), (back_btn.x + 40, back_btn.y + 12))
    screen.blit(small_font.render("删除选中存档", True, BLACK), (delete_btn.x + 30, delete_btn.y + 12))
    screen.blit(small_font.render("导入.sbx存档", True, BLACK), (import_btn.x + 30, import_btn.y + 12))
    
    if len(saves) > visible_btn_count:
        scroll_tip = small_font.render("鼠标滚轮滚动查看更多", True, GRAY)
        screen.blit(scroll_tip, (SCREEN_WIDTH//2 - 100, SCREEN_HEIGHT - 30))
    
    pygame.display.flip()
    return btn_list, back_btn, delete_btn, import_btn, saves

def show_controls_info(screen):
    """显示控制说明"""
    screen.fill(BLACK)
    title_text = main_font.render("控制说明", True, WHITE)
    title_rect = title_text.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//8))
    screen.blit(title_text, title_rect)
    
    controls = [
        "键盘控制:",
        "W/A/S/D - 移动",
        "空格 - 跳跃",
        "鼠标左键 - 挖掘方块",
        "鼠标右键 - 放置方块",
        "1/2/3/4 - 切换工具",
        "I - 打开/关闭物品栏",
        "ESC - 返回主菜单",
        "F2 - 显示/隐藏FPS",
        "F5 - 快速保存",
        "",
        "触摸控制:",
        "虚拟摇杆 - 移动",
        "跳跃按钮 - 跳跃",
        "物品栏按钮 - 打开物品栏",
        "动作按钮 - 挖掘/放置方块",
        "",
        "游戏特性:",
        "1. 泰拉瑞亚风格地形生成",
        "2. 多层柏林噪声洞穴系统",
        "3. 生物群系（沙漠、森林、平原、丘陵）",
        "4. 矿石系统（煤矿、铁矿、金矿）",
        "5. 完整的合成系统",
        "6. 昼夜循环和怪物AI",
        "7. 饥饿和生命值系统",
        "8. 完整的日志系统",
        "",
        "性能提示:",
        "1. 按F2显示/隐藏FPS",
        "2. 在设置中调整渲染距离",
        "3. 关闭不需要的视觉效果",
        "4. 定期保存游戏进度",
        "",
        "开发团队: LongTeam",
        "QQ群: 131293550",
        "版本: 1.10.3-rd4"
    ]
    
    scroll_offset = 0
    line_height = 30
    total_lines = len(controls)
    visible_lines = (SCREEN_HEIGHT - 200) // line_height
    
    back_btn = pygame.Rect(SCREEN_WIDTH//2 - 100, SCREEN_HEIGHT - 100, 200, 50)
    
    scrollbar_width = 10
    scrollbar_x = SCREEN_WIDTH - scrollbar_width - 20
    
    running = True
    while running:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            elif event.type == pygame.MOUSEBUTTONDOWN:
                if back_btn.collidepoint(event.pos):
                    running = False
                elif event.button == 4:  # 滚轮上
                    scroll_offset = max(0, scroll_offset - 3)
                elif event.button == 5:  # 滚轮下
                    scroll_offset = min(total_lines - visible_lines, scroll_offset + 3)
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    running = False
                elif event.key == pygame.K_UP:
                    scroll_offset = max(0, scroll_offset - 3)
                elif event.key == pygame.K_DOWN:
                    scroll_offset = min(total_lines - visible_lines, scroll_offset + 3)
        
        screen.fill(BLACK)
        screen.blit(title_text, title_rect)
        
        start_line = scroll_offset
        end_line = min(start_line + visible_lines, total_lines)
        
        y_pos = SCREEN_HEIGHT//4
        for i in range(start_line, end_line):
            if i < len(controls):
                text = small_font.render(controls[i], True, WHITE)
                screen.blit(text, (SCREEN_WIDTH//2 - 200, y_pos))
                y_pos += line_height
        
        if total_lines > visible_lines:
            scrollbar_bg = pygame.Rect(scrollbar_x, SCREEN_HEIGHT//4, scrollbar_width, visible_lines * line_height)
            pygame.draw.rect(screen, (100, 100, 100), scrollbar_bg)
            
            scrollbar_height = max(20, visible_lines / total_lines * (visible_lines * line_height))
            scrollbar_pos = scroll_offset / (total_lines - visible_lines) * (visible_lines * line_height - scrollbar_height)
            scrollbar_rect = pygame.Rect(scrollbar_x, SCREEN_HEIGHT//4 + scrollbar_pos, scrollbar_width, scrollbar_height)
            pygame.draw.rect(screen, (200, 200, 200), scrollbar_rect)
        
        pygame.draw.rect(screen, GRAY, back_btn)
        back_text = small_font.render("返回主菜单", True, BLACK)
        screen.blit(back_text, (back_btn.x + 50, back_btn.y + 15))
        
        if total_lines > visible_lines:
            tip_text = small_font.render("使用鼠标滚轮或上下箭头键滚动", True, (150, 150, 150))
            screen.blit(tip_text, (SCREEN_WIDTH//2 - 150, SCREEN_HEIGHT - 30))
        
        pygame.display.flip()

def show_about_screen(screen):
    """显示关于游戏信息"""
    screen.fill(BLACK)
    title_text = main_font.render("关于游戏", True, WHITE)
    title_rect = title_text.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//8))
    screen.blit(title_text, title_rect)
    
    about_info = [
        "沙盒游戏 1.10.3-rd4",
        "基于Python和Pygame开发",
        "",
        "特性:",
        "- 泰拉瑞亚风格无限生成的世界",
        "- 多层柏林噪声地形生成",
        "- 生物群系系统（沙漠、森林等）",
        "- 完整的方块和物品系统",
        "- 矿石和洞穴系统",
        "- 昼夜循环和怪物AI",
        "- 完整的存档和备份系统",
        "- 虚拟控制支持",
        "- 详细的日志系统",
        "",
        "开发团队: LongTeam",
        "版权所有 © 2025-2026 LongTeam",
        "盗版将追究法律责任",
        "QQ群: 131293550 (仅供玩家交流)",
        "",
        "Hello from the pygame community.",
        "https://www.pygame.org/contribute.html"
    ]
    
    y_pos = SCREEN_HEIGHT//4
    for info in about_info:
        text = small_font.render(info, True, WHITE)
        screen.blit(text, (SCREEN_WIDTH//2 - 200, y_pos))
        y_pos += 30
    
    back_btn = pygame.Rect(SCREEN_WIDTH//2 - 100, SCREEN_HEIGHT - 100, 200, 50)
    pygame.draw.rect(screen, GRAY, back_btn)
    back_text = small_font.render("返回主菜单", True, BLACK)
    screen.blit(back_text, (back_btn.x + 50, back_btn.y + 15))
    
    pygame.display.flip()
    
    waiting = True
    while waiting:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            elif event.type == pygame.MOUSEBUTTONDOWN:
                if back_btn.collidepoint(event.pos):
                    waiting = False
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    waiting = False

def show_tip(screen, tip_text, duration=1500):
    screen.fill(BLACK)
    text_surf = small_font.render(tip_text, True, WHITE)
    text_rect = text_surf.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//2))
    screen.blit(text_surf, text_rect)
    pygame.display.flip()
    time.sleep(duration / 1000)

def find_safe_spawn_location():
    """找到安全的出生点位置"""
    for attempt in range(100):
        spawn_x = random.randint(-20, 20)
        spawn_z = 0
        
        temp_gen = TerrainGenerator(WORLD_SEED)
        surface_height = int(temp_gen.get_height(spawn_x))
        
        chunk_x = int(spawn_x // CHUNK_SIZE)
        chunk_z = int(spawn_z // CHUNK_SIZE)
        
        if (chunk_x, chunk_z) not in LOADED_CHUNKS:
            LOADED_CHUNKS[(chunk_x, chunk_z)] = Chunk(chunk_x, chunk_z, WORLD_SEED)
            
        chunk = LOADED_CHUNKS[(chunk_x, chunk_z)]
        in_x = int(spawn_x % CHUNK_SIZE)
        in_z = int(spawn_z % CHUNK_SIZE)
        
        safe = True
        for y_offset in range(3):
            y_pos = surface_height + 2 + y_offset
            if y_pos < Y_MAX:
                if chunk.blocks[in_x][y_pos][in_z] != 0:
                    safe = False
                    break
        
        if safe and surface_height + 1 < Y_MAX:
            if chunk.blocks[in_x][surface_height + 1][in_z] == 0:
                safe = False
        
        if safe:
            return spawn_x, surface_height + 2
    
    return 0, Y_MAX // 2

def load_chunks_around_player(player):
    """加载玩家周围的区块"""
    player_chunk_x = int(player.world_x // CHUNK_SIZE)
    player_chunk_z = int(player.world_z // CHUNK_SIZE)
    
    for dx in range(-RENDER_DISTANCE, RENDER_DISTANCE + 1):
        for dz in range(-RENDER_DISTANCE, RENDER_DISTANCE + 1):
            target_chunk_x = player_chunk_x + dx
            target_chunk_z = player_chunk_z + dz
            if (target_chunk_x, target_chunk_z) not in LOADED_CHUNKS:
                LOADED_CHUNKS[(target_chunk_x, target_chunk_z)] = Chunk(target_chunk_x, target_chunk_z, WORLD_SEED)

def show_player_name_input(screen):
    screen.fill(BLACK)
    title_text = main_font.render("wzmc新游戏 - 输入玩家名称", True, WHITE)
    title_rect = title_text.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//4))
    screen.blit(title_text, title_rect)
    
    tip_text1 = small_font.render("请在命令行输入玩家名称（回车用默认名）", True, YELLOW)
    tip_rect1 = tip_text1.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//2 - 30))
    default_name = f"Player_{int(time.time())}"
    tip_text2 = small_font.render(f"默认名称: {default_name}", True, WHITE)
    tip_rect2 = tip_text2.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//2 + 20))
    
    screen.blit(tip_text1, tip_rect1)
    screen.blit(tip_text2, tip_rect2)
    
    confirm_btn = pygame.Rect(SCREEN_WIDTH//2 - 120, SCREEN_HEIGHT//2 + 80, 240, 50)
    pygame.draw.rect(screen, GREEN, confirm_btn)
    screen.blit(small_font.render("命令行输入后点击确认", True, BLACK), (confirm_btn.x + 10, confirm_btn.y + 12))
    
    pygame.display.flip()
    return confirm_btn, default_name

def show_resolution_select(screen):
    screen.fill(BLACK)
    title_text = main_font.render("选择分辨率", True, WHITE)
    title_rect = title_text.get_rect(center=(SCREEN_WIDTH//2, SCREEN_HEIGHT//4))
    screen.blit(title_text, title_rect)
    
    res1_btn = pygame.Rect(SCREEN_WIDTH//2 - 120, SCREEN_HEIGHT//2 - 50, 240, 50)
    res2_btn = pygame.Rect(SCREEN_WIDTH//2 - 120, SCREEN_HEIGHT//2 + 30, 240, 50)
    fullscreen_btn = pygame.Rect(SCREEN_WIDTH//2 - 120, SCREEN_HEIGHT//2 + 110, 240, 50)
    
    pygame.draw.rect(screen, GREEN, res1_btn)
    pygame.draw.rect(screen, GREEN, res2_btn)
    pygame.draw.rect(screen, YELLOW, fullscreen_btn)
    
    screen.blit(small_font.render("1. 800×600（默认）", True, BLACK), (res1_btn.x + 40, res1_btn.y + 12))
    screen.blit(small_font.render("2. 1024×768", True, BLACK), (res2_btn.x + 60, res2_btn.y + 12))
    screen.blit(small_font.render("3. 全屏模式（F11切换）", True, BLACK), (fullscreen_btn.x + 20, fullscreen_btn.y + 12))
    
    pygame.display.flip()
    return res1_btn, res2_btn, fullscreen_btn

def show_settings_screen(screen):
    """显示设置屏幕 - 支持滚动"""
    scroll_offset = 0
    max_scroll = 200  # 最大滚动距离
    
    while True:
        settings_items = show_settings_menu(screen, scroll_offset)
        
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            elif event.type == pygame.USEREVENT + 1:
                play_random_ogg_music()
            elif event.type == pygame.MOUSEBUTTONDOWN:
                mx, my = event.pos
                
                if event.button == 4:  # 滚轮上
                    scroll_offset = max(0, scroll_offset - 50)
                elif event.button == 5:  # 滚轮下
                    scroll_offset = min(max_scroll, scroll_offset + 50)
                else:
                    for setting_type, btn in settings_items:
                        if btn.collidepoint(mx, my):
                            if setting_type == "joystick":
                                SETTINGS["virtual_joystick"] = not SETTINGS["virtual_joystick"]
                                save_settings()
                                load_settings()
                            elif setting_type == "buttons":
                                SETTINGS["virtual_buttons"] = not SETTINGS["virtual_buttons"]
                                save_settings()
                                load_settings()
                            elif setting_type == "sound":
                                SETTINGS["sound_volume"] = (SETTINGS["sound_volume"] + 0.1) % 1.1
                                if SETTINGS["sound_volume"] > 1.0:
                                    SETTINGS["sound_volume"] = 0.0
                                save_settings()
                                load_settings()
                            elif setting_type == "music":
                                SETTINGS["music_volume"] = (SETTINGS["music_volume"] + 0.1) % 1.1
                                if SETTINGS["music_volume"] > 1.0:
                                    SETTINGS["music_volume"] = 0.0
                                save_settings()
                                load_settings()
                            elif setting_type == "render":
                                SETTINGS["render_distance"] = (SETTINGS["render_distance"] % 5) + 1
                                save_settings()
                                load_settings()
                            elif setting_type == "fps":
                                SETTINGS["fps_limit"] = 60 if SETTINGS["fps_limit"] == 120 else 120
                                save_settings()
                                load_settings()
                            elif setting_type == "log":
                                SETTINGS["log_enabled"] = not SETTINGS["log_enabled"]
                                save_settings()
                                load_settings()
                            elif setting_type == "back":
                                return

# ---------------------- 游戏主循环 ----------------------
def return_to_main_menu(screen):
    global LOADED_CHUNKS, WORLD_SEED, DROPS, MONSTERS
    LOADED_CHUNKS = OrderedDict()
    WORLD_SEED = random.randint(0, 2**32 - 1)
    DROPS = []
    MONSTERS = []
    scroll_offset = 0
    btn_spacing = 60
    visible_btn_count = 5
    game_started = False
    game_mode = ""
    player = None
    fullscreen = False

    while True:
        buttons = show_main_menu(screen)
        (sandbox_btn, wzmc_new_btn, wzmc_load_btn, settings_btn, 
         resolution_btn, controls_btn, about_btn, quit_btn) = buttons

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                if game_logger:
                    game_logger.info("用户退出游戏")
                pygame.quit()
                sys.exit()
            elif event.type == pygame.USEREVENT + 1:
                play_random_ogg_music()
            elif event.type == pygame.MOUSEBUTTONDOWN:
                mx, my = event.pos
                if sandbox_btn.collidepoint(mx, my):
                    if game_logger:
                        game_logger.info("进入沙盒模式")
                    spawn_x, spawn_z = find_safe_spawn_location()
                    player = Player(x=spawn_x, y=spawn_z, name="Sandbox_Player")
                    load_chunks_around_player(player)
                    game_mode = "sandbox"
                    game_started = True
                    start_game_loop(screen, player, game_mode, fullscreen)
                elif wzmc_new_btn.collidepoint(mx, my):
                    confirm_btn, default_name = show_player_name_input(screen)
                    name_confirmed = False
                    while not name_confirmed:
                        for sub_event in pygame.event.get():
                            if sub_event.type == pygame.QUIT:
                                pygame.quit()
                                sys.exit()
                            elif sub_event.type == pygame.USEREVENT + 1:
                                play_random_ogg_music()
                            elif sub_event.type == pygame.MOUSEBUTTONDOWN:
                                sub_mx, sub_my = sub_event.pos
                                if confirm_btn.collidepoint(sub_mx, sub_my):
                                    try:
                                        user_input = input("请输入玩家名称：").strip()
                                    except:
                                        user_input = ""
                                    final_name = user_input if user_input else default_name
                                    spawn_x, spawn_z = find_safe_spawn_location()
                                    player = Player(x=spawn_x, y=spawn_z, name=final_name)
                                    load_chunks_around_player(player)
                                    save_data = {
                                        "player": player.to_save_data(),
                                        "game_state": {"current_map": "平原", "time": "白天" if is_day else "黑夜", "completed_quests": []}
                                    }
                                    success, msg = create_json_file(get_save_path(final_name), save_data, LOADED_CHUNKS, WORLD_SEED)
                                    show_tip(screen, msg)
                                    game_mode = "wzmc"
                                    game_started = True
                                    name_confirmed = True
                                    if game_logger:
                                        game_logger.info(f"创建新游戏，玩家: {final_name}")
                                    start_game_loop(screen, player, game_mode, fullscreen)
                elif wzmc_load_btn.collidepoint(mx, my):
                    saves = load_save_list()
                    if not saves:
                        show_tip(screen, "无wzmc存档，返回主菜单")
                        continue
                    max_scroll = max(0, (len(saves) - visible_btn_count) * (btn_spacing + 10))
                    selected_save = None
                    while selected_save is None:
                        btn_list, back_btn, delete_btn, import_btn, _ = show_save_list(screen, scroll_offset, btn_spacing, visible_btn_count)
                        for sub_event in pygame.event.get():
                            if sub_event.type == pygame.QUIT:
                                pygame.quit()
                                sys.exit()
                            elif sub_event.type == pygame.USEREVENT + 1:
                                play_random_ogg_music()
                            elif sub_event.type == pygame.MOUSEBUTTONDOWN:
                                sub_mx, sub_my = sub_event.pos
                                if sub_event.button == 4:
                                    scroll_offset = max(0, scroll_offset - (btn_spacing + 10))
                                elif sub_event.button == 5:
                                    scroll_offset = min(max_scroll, scroll_offset + (btn_spacing + 10))
                                else:
                                    for btn, save_name in btn_list:
                                        if btn.collidepoint(sub_mx, sub_my):
                                            selected_save = save_name
                                            break
                                    if back_btn.collidepoint(sub_mx, sub_my):
                                        selected_save = "back"
                                        break
                                    if delete_btn.collidepoint(sub_mx, sub_my) and selected_save:
                                        try:
                                            confirm = input(f"确定删除「{selected_save}」？输入D确认：").strip().upper()
                                        except:
                                            confirm = ""
                                        if confirm == "D":
                                            try:
                                                os.remove(get_save_path(selected_save))
                                                show_tip(screen, f"删除成功：{selected_save}")
                                                saves = load_save_list()
                                                max_scroll = max(0, (len(saves) - visible_btn_count) * (btn_spacing + 10))
                                                scroll_offset = 0
                                            except Exception as e:
                                                show_tip(screen, f"删除失败: {e}")
                                        else:
                                            show_tip(screen, "取消删除")
                                        selected_save = None
                    if selected_save not in ("back", None):
                        success, msg, player_data, loaded_chunks, world_seed = load_json_file(get_save_path(selected_save))
                        if success:
                            LOADED_CHUNKS = loaded_chunks
                            WORLD_SEED = world_seed
                            player = Player.from_save_data(player_data)
                            game_mode = "wzmc"
                            show_tip(screen, "加载成功")
                            if game_logger:
                                game_logger.info(f"加载存档: {selected_save}")
                            start_game_loop(screen, player, game_mode, fullscreen)
                        else:
                            show_tip(screen, msg)
                elif settings_btn.collidepoint(mx, my):
                    show_settings_screen(screen)
                elif resolution_btn.collidepoint(mx, my):
                    res1_btn, res2_btn, fullscreen_btn = show_resolution_select(screen)
                    res_confirmed = False
                    while not res_confirmed:
                        for sub_event in pygame.event.get():
                            if sub_event.type == pygame.QUIT:
                                pygame.quit()
                                sys.exit()
                            elif sub_event.type == pygame.USEREVENT + 1:
                                play_random_ogg_music()
                            elif sub_event.type == pygame.MOUSEBUTTONDOWN:
                                sub_mx, sub_my = sub_event.pos
                                if res1_btn.collidepoint(sub_mx, sub_my):
                                    global SCREEN_WIDTH, SCREEN_HEIGHT
                                    SCREEN_WIDTH, SCREEN_HEIGHT = 800, 600
                                    screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
                                    show_tip(screen, "已切换为800×600")
                                    res_confirmed = True
                                elif res2_btn.collidepoint(sub_mx, sub_my):
                                    SCREEN_WIDTH, SCREEN_HEIGHT = 1024, 768
                                    screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
                                    show_tip(screen, "已切换为1024×768")
                                    res_confirmed = True
                                elif fullscreen_btn.collidepoint(sub_mx, sub_my):
                                    fullscreen = not fullscreen
                                    if fullscreen:
                                        screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.FULLSCREEN)
                                    else:
                                        screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
                                    show_tip(screen, f"已切换为{'全屏' if fullscreen else '窗口'}模式")
                                    res_confirmed = True
                elif controls_btn.collidepoint(mx, my):
                    show_controls_info(screen)
                elif about_btn.collidepoint(mx, my):
                    show_about_screen(screen)
                elif quit_btn.collidepoint(mx, my):
                    if game_logger:
                        game_logger.info("用户退出游戏")
                    pygame.quit()
                    sys.exit()

def start_game_loop(screen, player, game_mode, fullscreen):
    global LOADED_CHUNKS, WORLD_SEED, DROPS, MONSTERS, is_day
    selected_block = 2
    current_dig_block = None
    current_dig_progress = 0
    clock = pygame.time.Clock()
    DAY_DURATION = 5 * 60 * FPS
    current_time = 0
    monster_spawn_timer = 0
    monster_spawn_interval = FPS * 15
    
    frame_counter = 0
    
    if USE_DOUBLE_BUFFER:
        buffer_surface = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT))

    while True:
        delta_time = clock.tick(FPS) / 1000.0
        frame_counter += 1
        
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    return_to_main_menu(screen)
                elif event.key in (pygame.K_1, pygame.K_2, pygame.K_3, pygame.K_4):
                    tool_id = int(event.unicode) - 1
                    if 0 <= tool_id < 4 and player.tools.get(tool_id, 0) > 0:
                        player.current_tool = tool_id
                elif event.key in (pygame.K_UP, pygame.K_DOWN):
                    selected_block = (selected_block - 1) % len(BLOCK_TYPES) if event.key == pygame.K_UP else (selected_block + 1) % len(BLOCK_TYPES)
                elif event.key == pygame.K_i:
                    player.bag_open = not player.bag_open
                elif event.key == pygame.K_F5:
                    save_data = {"player": player.to_save_data(), "game_state": {"current_map": "平原", "time": "白天" if is_day else "黑夜", "completed_quests": []}}
                    success, msg = create_json_file(get_save_path(player.name), save_data, LOADED_CHUNKS, WORLD_SEED)
                    show_tip(screen, msg)
                elif event.key == pygame.K_F2:
                    global show_fps
                    show_fps = not show_fps
            elif event.type == pygame.MOUSEBUTTONDOWN:
                if handle_virtual_controls(event, player):
                    continue
                    
                if event.button == 1:
                    mouse_pos = pygame.mouse.get_pos()
                    target_block = get_mouse_block(mouse_pos, player)
                    block_x, block_y, block_z = target_block
                    chunk_x, chunk_z = int(block_x//CHUNK_SIZE), int(block_z//CHUNK_SIZE)
                    if (chunk_x, chunk_z) in LOADED_CHUNKS:
                        chunk = LOADED_CHUNKS[(chunk_x, chunk_z)]
                        in_x, in_z = int(block_x % CHUNK_SIZE), int(block_z % CHUNK_SIZE)
                        if 0 <= in_x < CHUNK_SIZE and 0 <= block_y < Y_MAX and 0 <= in_z < CHUNK_SIZE:
                            block_id = chunk.blocks[in_x][block_y][in_z]
                            if block_id != 0 and BLOCK_TYPES[block_id]["breakable"]:
                                current_dig_block = target_block
                                current_dig_progress = 0
                elif event.button == 3:
                    if player.inventory.get(selected_block, 0) > 0:
                        mouse_pos = pygame.mouse.get_pos()
                        target_block = get_mouse_block(mouse_pos, player)
                        block_x, block_y, block_z = target_block
                        chunk_x, chunk_z = int(block_x//CHUNK_SIZE), int(block_z//CHUNK_SIZE)
                        if (chunk_x, chunk_z) in LOADED_CHUNKS:
                            chunk = LOADED_CHUNKS[(chunk_x, chunk_z)]
                            in_x, in_z = int(block_x % CHUNK_SIZE), int(block_z % CHUNK_SIZE)
                            if 0 <= in_x < CHUNK_SIZE and 0 <= block_y < Y_MAX and 0 <= in_z < CHUNK_SIZE:
                                if chunk.blocks[in_x][block_y][in_z] == 0:
                                    chunk.blocks[in_x][block_y][in_z] = selected_block
                                    player.inventory[selected_block] -= 1
                                    play_sound("place")
            elif event.type in (pygame.MOUSEMOTION, pygame.MOUSEBUTTONUP):
                handle_virtual_controls(event, player)

        current_time = (current_time + 1) % DAY_DURATION
        if current_time == 0:
            is_day = not is_day
            
        if not is_day and frame_counter % FRAME_SKIP == 0:
            monster_spawn_timer = (monster_spawn_timer + 1) % monster_spawn_interval
            if monster_spawn_timer == 0 and len(MONSTERS) < 5:
                spawn_x = player.world_x + random.randint(-10, 10)
                spawn_z = player.world_z + random.randint(-10, 10)
                MONSTERS.append(Monster(spawn_x, spawn_z))

        load_chunks_around_player(player)
        
        if frame_counter % FRAME_SKIP == 0:
            player_chunk_x = int(player.world_x // CHUNK_SIZE)
            player_chunk_z = int(player.world_z // CHUNK_SIZE)
            chunks_to_unload = []
            for (chunk_x, chunk_z) in LOADED_CHUNKS:
                if math.hypot(chunk_x - player_chunk_x, chunk_z - player_chunk_z) > RENDER_DISTANCE + 2:
                    chunks_to_unload.append((chunk_x, chunk_z))
            for chunk_key in chunks_to_unload:
                del LOADED_CHUNKS[chunk_key]

        player.update(LOADED_CHUNKS)
        
        if frame_counter % FRAME_SKIP == 0:
            limited_monsters = limit_updates_per_frame(MONSTERS)
            new_monsters = []
            for m in limited_monsters:
                if m.update(player, LOADED_CHUNKS):
                    new_monsters.append(m)
            MONSTERS = new_monsters
        
        if frame_counter % FRAME_SKIP == 0:
            limited_drops = limit_updates_per_frame(DROPS)
            new_drops = []
            for d in limited_drops:
                if d.update(LOADED_CHUNKS):
                    new_drops.append(d)
            DROPS = new_drops

        if current_dig_block:
            block_x, block_y, block_z = current_dig_block
            chunk_x, chunk_z = int(block_x//CHUNK_SIZE), int(block_z//CHUNK_SIZE)
            if (chunk_x, chunk_z) in LOADED_CHUNKS:
                chunk = LOADED_CHUNKS[(chunk_x, chunk_z)]
                in_x, in_z = int(block_x % CHUNK_SIZE), int(block_z % CHUNK_SIZE)
                if 0 <= in_x < CHUNK_SIZE and 0 <= block_y < Y_MAX and 0 <= in_z < CHUNK_SIZE:
                    block_id = chunk.blocks[in_x][block_y][in_z]
                    if block_id != 0:
                        tool = TOOL_TYPES[player.current_tool]
                        if block_id in tool["breakable_blocks"]:
                            hardness = BLOCK_TYPES[block_id]["hardness"]
                            efficiency = tool["efficiency"]
                            current_dig_progress += efficiency / hardness * delta_time * 60
                            if current_dig_progress >= 100:
                                drop_id = BLOCK_TYPES[block_id]["drop"]
                                if drop_id != 0:
                                    DROPS.append(DropItem(block_x, block_z, drop_id))
                                chunk.blocks[in_x][block_y][in_z] = 0
                                current_dig_block = None
                                current_dig_progress = 0
                                play_sound("dig")
                                
                                if tool["durability"] > 0:
                                    used_durability = getattr(player, "used_durability", 0) + 1
                                    player.used_durability = used_durability
                                    if used_durability >= tool["durability"]:
                                        player.tools[player.current_tool] -= 1
                                        if player.tools[player.current_tool] <= 0:
                                            player.current_tool = 0
                                        player.used_durability = 0
                                        show_tip(screen, "工具损坏，已切换为徒手")
                        else:
                            current_dig_block = None
                    else:
                        current_dig_block = None
            else:
                current_dig_block = None

        target_surface = buffer_surface if USE_DOUBLE_BUFFER else screen
        target_surface.fill((255,255,255) if is_day else (10, 10, 30))
        
        draw_infinite_map(target_surface, LOADED_CHUNKS, player)
        
        if frame_counter % max(1, FRAME_SKIP // 2) == 0:
            for drop in DROPS:
                drop.draw(target_surface, player)
            for monster in MONSTERS:
                monster.draw(target_surface, player)
            
        player.draw(target_surface)
        
        draw_virtual_controls(target_surface)
        
        selected_surf = small_font.render(f"选中方块：{BLOCK_TYPES[selected_block]['name']}", True, WHITE)
        target_surface.blit(selected_surf, (10, 30))
        
        hp_bar_x = SCREEN_WIDTH - 110
        hp_bar_y = 10
        pygame.draw.rect(target_surface, BLACK, (hp_bar_x, hp_bar_y, 100, 8))
        hp_fill = int(player.hp)
        pygame.draw.rect(target_surface, RED, (hp_bar_x, hp_bar_y, hp_fill, 8))
        hp_text = small_font.render("HP", True, WHITE)
        target_surface.blit(hp_text, (hp_bar_x - 30, hp_bar_y - 2))
        
        if current_dig_block and current_dig_progress > 0:
            draw_dig_progress(target_surface, current_dig_block, player, current_dig_progress)
        
        if USE_DOUBLE_BUFFER:
            screen.blit(buffer_surface, (0, 0))
            
        pygame.display.flip()

# ---------------------- 主函数 ----------------------
def main():
    global menu_bg, main_font, small_font, IS_MOBILE, show_fps, game_logger
    
    # 初始化日志系统
    game_logger = GameLogger(LOG_DIR, enabled=True)
    
    # 模拟版本检查错误（如你提供的日志示例）
    game_logger.info("Hello from the pygame community. https://www.pygame.org/contribute.html")
    game_logger.info("com.lonteam.wzmcgame, by ©2025 - 2026 LongTeam")
    game_logger.info("Piracy will be held legally accountable.")
    game_logger.info("QQ Group: 131293550 (Player Communication Only)")
    game_logger.info("")
    game_logger.info("Game launched, starting automatic version check and update process")
    game_logger.info("Detected local current version: 1.10.3-rd4")
    game_logger.info("Detected server target version: unknown \"-1\"")
    game_logger.error("Exception thrown during version span verification in <update> class")
    game_logger.error("Exception Cause: Version span from local 1.10.3-rd4 to target -1 exceeds allowed range (max allowed span: 1024), version number difference verification failed")
    game_logger.warning("Automatic version check and update process execution failed, continuing with local version")
    game_logger.info("哈哈，只是玩笑")
    game_logger.info("")
    
    # 检测是否在移动设备上运行
    try:
        import android
        import android.mixer
        IS_MOBILE = True
        game_logger.info("运行在移动设备上")
    except ImportError:
        IS_MOBILE = False
        game_logger.info("运行在桌面设备上")
    
    pygame.init()
    pygame.mixer.init()
    
    screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
    pygame.display.set_caption("沙盒游戏 1.10.3-rd4-NewLogTime")
    
    main_font = pygame.font.SysFont("simhei", 48)
    small_font = pygame.font.SysFont("simhei", 24)
    
    load_settings()
    
    try:
        if os.path.exists(BG_PHOTO_PATH):
            menu_bg = pygame.image.load(BG_PHOTO_PATH).convert()
            menu_bg = pygame.transform.scale(menu_bg, (SCREEN_WIDTH, SCREEN_HEIGHT))
            game_logger.info(f"背景图加载成功：{BG_PHOTO_PATH}")
        else:
            menu_bg = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT))
            menu_bg.fill(BROWN)
            game_logger.warning(f"背景图不存在，使用棕色背景：{BG_PHOTO_PATH}")
    except Exception as e:
        menu_bg = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT))
        menu_bg.fill(BROWN)
        game_logger.error(f"背景图加载失败：{str(e)}，使用棕色背景")
        
    init_sounds()
    play_random_ogg_music()
    
    print("=" * 60)
    print("com.lonteam.wzmcgame, by ©2025 - 2026 LongTeam")
    print("如有发现盗版，必会追究责任")
    print("QQ群: 131293550 (仅供玩家交流)")
    print("游戏版本: 1.10.3-rd4")
    print("日志系统已启用，日志文件保存在: " + LOG_DIR)
    print("=" * 60)
    
    return_to_main_menu(screen)

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        if game_logger:
            game_logger.fatal("游戏运行时发生致命错误")
            game_logger.exception("错误详情", e)
            game_logger.exit("游戏异常退出", exit_code=-1)
        else:
            print(f"[FATAL] 游戏运行时发生致命错误: {e}")
            traceback.print_exc()
        pygame.quit()
        sys.exit(-1)
