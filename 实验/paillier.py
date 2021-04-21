from pypbc import *
from gmpy2 import mpz, is_prime, random_state, mpz_urandomb, mpz_random, powmod, bit_length, mul, invert, t_mod, next_prime, f_div
import random
import sys
import hashlib
import math
import paillier
from time import time
import hmac
from AesEverywhere import aes256
import base64

#初始化系统难度
N=200# 用户人数
d=10000000#单位数据最大数值
J=50#每J次给用户发送奖励
reward_p = 10#奖励系数
huan_number = 50#环签名人数

#初始化类
class SMi():
    def __init__(self):
        self.ai=Element.random( pairing2, Zr )
        self.bi=Element.random( pairing2, Zr )
        self.wi=Element.random( pairing1, Zr )
        self.Ai=Element( pairing2, G2, value = G_blc*self.ai )
        self.Bi=Element( pairing2, G2, value = G_blc*self.bi )
        self.Wi=Element( pairing1, G2, value = P_pki*self.wi )
        self.Conti = get_random_prime(1024)

class Up():
    def __init__(self):
        self.x  =Element.random( pairing2, Zr )
        self.X = Element( pairing2, G2, value = G_blc*self.x )
        self.y = Element.random(pairing1, Zr)
        self.Y = Element(pairing1, G2, value=P_pki * self.y)

class PCs():
    def __init__(self):
        self.z = Element.random( pairing1, Zr )
        self.Z = Element(pairing1, G2, value=P_pki * self.z)

#初始化PKI下的PKCs
params1 = Parameters(qbits=512, rbits=160)
pairing1 = Pairing(params1)
P_pki = Element.random( pairing1, G2 )

def hash_pki(message):
    hash_value = Element.from_hash(pairing1, G1, str(message))
    return hash_value

#初始化blockchain下的PKCs
params2 = Parameters(qbits=256, rbits=160)
pairing2 = Pairing(params2)
G_blc = Element.random( pairing2, G2 )

def hash_blc_G(message):
    hash_value = Element.from_hash(pairing2, G2, str(message))
    return hash_value

def hash_blc_Z(message):
    hash_value = Element.from_hash(pairing2, Zr, str(message))
    return hash_value

#初始化P密码系统(bits,N,d)
paillier_priv,paillier_pub = paillier.generate_keypair(128,N,d)
#print(paillier.huifu(paillier.decrypt(paillier_priv, paillier_pub, qqq),paillier_priv))

#hmac(0,1)--Zd
def paillier_hmac(key,message,d):
    message=bytes(message,encoding='utf-8')
    key=bytes(key,encoding='utf-8')
    hmac_p=hmac.new(key, message, digestmod='SHA256')
    hmac_p = int(hmac_p.hexdigest(),16)%d
    return hmac_p

#初始化公私钥
for i in range(1,N+1):#初始化用户
    locals()[f'user{i}'] = SMi()

UP=Up()#初始化管理员
PCS =PCs()#初始化计算中心
#第一阶段：基于合同的授权
start = time()
for i in range(1,N+1):
    locals()[f'user{i}'].user_hash1 = hash_pki( locals()[f'user{i}'].Conti)
    locals()[f'user{i}'].qian1 = Element(pairing1, G1, value = locals()[f'user{i}'].user_hash1 * UP.y )
    locals()[f'user{i}'].ki = hex(get_random_prime(128))
stop = time()
print("基于合同的授权（单位用户）:"+str((stop-start)/N) +"秒")

#第二阶段：匿名认证
verify1_left = Element.zero( pairing1, G1 )
verify1_right = Element.zero( pairing1, G1 )
start = time()
for i in range(1,N+1):
    locals()[f'user{i}'].rand1 = Element.random( pairing1, Zr )
    verify1_left += Element(pairing1, G1, value = locals()[f'user{i}'].qian1 * locals()[f'user{i}'].rand1 )
    verify1_right += Element(pairing1, G1, value = locals()[f'user{i}'].user_hash1 * locals()[f'user{i}'].rand1 )
if pairing1.apply(verify1_left,P_pki) == pairing1.apply(verify1_right,UP.Y):
    stop = time()
    print("匿名认证（单位用户）:"+str((stop-start)/N) +"秒")

#第三阶段：数据上传
start = sys_t = time()
for i in range(1,N+1):
    plain1 = random.randrange(d)
    plain2 = random.randrange(d)
    plain3 =paillier_hmac(locals()[f'user{i}'].ki,str(locals()[f'user{i}'].Ai)+str(locals()[f'user{i}'].Bi)+str(sys_t),d)
    locals()[f'user{i}'].C_i_t = paillier.encrypt(paillier_pub, plain1,plain2,plain3)
    #解密算法#print(paillier.huifu(paillier.decrypt(paillier_priv, paillier_pub, locals()[f'user{i}'].C_i_t),paillier_priv))
    locals()[f'user{i}'].C_k_i_t = aes256.encrypt(str(plain1)+","+str(plain2)+","+str(plain3)+","+str(sys_t),locals()[f'user{i}'].ki)
    locals()[f'user{i}'].user_hash2 = hash_pki( str(locals()[f'user{i}'].Ai)+","+str(locals()[f'user{i}'].Bi)+","+str(locals()[f'user{i}'].C_i_t)+","+str(locals()[f'user{i}'].C_k_i_t)+","+str(sys_t))
    locals()[f'user{i}'].qian2 = Element(pairing1, G1, value = locals()[f'user{i}'].user_hash2 * locals()[f'user{i}'].wi)
stop = time()
print("数据上传（单位用户）:"+str((stop-start)/N) +"秒")

#第四阶段：数据聚合
verify2_left = Element.zero( pairing1, G1 )
verify2_right = Element.one( pairing1, GT )
C_t = 1
start = time()
for i in range(1,N+1):#签名验证
    locals()[f'user{i}'].rand2 = Element.random( pairing1, Zr )
    verify2_left += Element(pairing1, G1, value = locals()[f'user{i}'].qian2 * locals()[f'user{i}'].rand2 )
    verify2_right *= pairing1.apply(Element(pairing1, G1, value = locals()[f'user{i}'].user_hash2 * locals()[f'user{i}'].rand2 ),locals()[f'user{i}'].Wi)
if pairing1.apply(verify2_left,P_pki) == verify2_right:#数据聚合
    for i in range(1,N+1):
        C_t = paillier.e_add(paillier_pub,C_t, locals()[f'user{i}'].C_i_t)
    PCS.hash1 =  hash_pki(str(C_t)+","+str(time()))
    PCS.qian1 = Element(pairing1, G1, value = PCS.hash1 * PCS.z)
    #解密算法print(paillier.huifu(paillier.decrypt(paillier_priv, paillier_pub, C_t),paillier_priv))
stop=time()
print("数据聚合（单位用户）:" + str((stop - start) / N) + "秒")

#第五阶段：验证和解密
Q_t = 0
start = time()
if pairing1.apply(PCS.qian1,P_pki)==pairing1.apply(PCS.hash1,PCS.Z):
    for i in range(1, N + 1):
        Q_t += paillier_hmac(locals()[f'user{i}'].ki,str(locals()[f'user{i}'].Ai)+str(locals()[f'user{i}'].Bi)+str(sys_t),d)
    D1,D2,D3 = paillier.huifu(paillier.decrypt(paillier_priv, paillier_pub, C_t), paillier_priv)
    if D3 == Q_t:
        pass
    else:
        print("wrong")
stop = time()
print("验证和解密（单位用户）:" + str((stop - start)/N) + "秒")

#第六阶段匿名奖励
start = time()
for j in range (1,J+1):#生成J个时段的密文数据
    locals()[f'sys_t_{j}'] = time()
    for i in range(1,N+1):
        plain1 = random.randrange(d)
        plain2 = random.randrange(d)
        plain3 =paillier_hmac(locals()[f'user{i}'].ki,str(locals()[f'user{i}'].Ai)+str(locals()[f'user{i}'].Bi)+str(locals()[f'sys_t_{j}']),d)
        locals()[f'user{i}.C_i_{j}']=paillier.encrypt(paillier_pub, plain1,plain2,plain3)
        #解密算法#print(paillier.huifu(paillier.decrypt(paillier_priv, paillier_pub, locals()[f'user{i}'].C_i_t),paillier_priv))
        #locals()[f'user{i}.C__k_i_{j}'] = aes.encrypt(str(plain1)+","+str(plain2)+","+str(plain3)+","+str(sys_t),locals()[f'user{i}'].ki)
        #locals()[f'user{i}'].user_hash2 = hash_pki( str(locals()[f'user{i}'].Ai)+","+str(locals()[f'user{i}'].Bi)+","+str(locals()[f'user{i}'].C_i_t)+","+str(locals()[f'user{i}'].C_k_i_t)+","+str(sys_t))
        #locals()[f'user{i}'].qian2 = Element(pairing1, G1, value = locals()[f'user{i}'].user_hash2 * locals()[f'user{i}'].wi)
for i in range(1,N+1):#聚合单位用户J个时段的密文数据
    locals()[f'user{i}'].C_i_T = 1
    for j in range(1,J+1):
        locals()[f'user{i}'].C_i_T = paillier.e_add(paillier_pub, locals()[f'user{i}'].C_i_T,  locals()[f'user{i}.C_i_{j}'])

for i in range(1,N+1):#PCS签名
    locals()[f'PCS.hash2_C_{i}_T'] = hash_pki(str(locals()[f'user{i}'].C_i_T) + "," + str(time()))
    locals()[f'PCS.qian2_C_{i}_T'] = Element(pairing1, G1, value=locals()[f'PCS.hash2_C_{i}_T'] * PCS.z)

verify3_left = Element.zero( pairing1, G1 )
verify3_right = Element.zero( pairing1, G1 )
for i in range(1,N+1):#UP验证
        locals()[f'user{i}'].rand2 = Element.random(pairing1, Zr)
        verify3_left += Element(pairing1, G1, value=locals()[f'PCS.qian2_C_{i}_T'] * locals()[f'user{i}'].rand2)
        verify3_right += Element(pairing1, G1, value=locals()[f'PCS.hash2_C_{i}_T'] * locals()[f'user{i}'].rand2)
        if pairing1.apply(verify3_left, P_pki) == pairing1.apply(verify3_right, PCS.Z):
            for i in range(1,N+1):
                locals()[f'user{i}'].D1_T,locals()[f'user{i}'].D2_T,locals()[f'user{i}'].D3_T = paillier.huifu(paillier.decrypt(paillier_priv, paillier_pub, locals()[f'user{i}'].C_i_T), paillier_priv)
                locals()[f'user{i}'].Q_i_T = 0
                for j in range(1,J+1):
                    locals()[f'user{i}'].Q_i_T += paillier_hmac(locals()[f'user{i}'].ki,str(locals()[f'user{i}'].Ai)+str(locals()[f'user{i}'].Bi)+str(locals()[f'sys_t_{j}']),d)
                if locals()[f'user{i}'].D3_T ==locals()[f'user{i}'].Q_i_T:
                    pass
                else:
                    print("wrong")

UP.miu = Element.random( pairing2, Zr )
UP.p_c = Element.random( pairing2, Zr )
UP.P_c = Element( pairing2, G2, value = G_blc*UP.p_c )
UP.R = Element( pairing2, G2, value = G_blc * UP.miu)
for i in range(1,N+1):#生成区块连奖励地址
    locals()[f'user{i}'].P_i = Element( pairing2 , G2 )
    locals()[f'user{i}'].P_i = G_blc *  hash_blc_Z(Element( pairing2, G2, value = locals()[f'user{i}'].Ai * UP.miu ))+locals()[f'user{i}'].Bi
    locals()[f'user{i}'].bal = locals()[f'user{i}'].D2_T * reward_p

UP.m = get_random_prime(512)
UP.A = hash_blc_G(UP.m)#模拟对签名的哈希
UP.I = Element(pairing2,G2)
UP.I = hash_blc_G(UP.X) * UP.x
n_number = 0
UP.c_plus = Element.zero(pairing2,Zr)
for i in random.sample(range(1,N+1),huan_number):#生成环签名
    n_number += 1
    locals()[f'UP.q_{n_number}'] = Element.random( pairing2, Zr )
    locals()[f'UP.w_{n_number}'] = Element.random( pairing2, Zr )
    locals()[f'UP.L_{n_number}'] = Element(pairing2,G2)
    locals()[f'UP.L_{n_number}'] = G_blc * locals()[f'UP.q_{n_number}'] + locals()[f'user{i}'].P_i *  locals()[f'UP.w_{n_number}']
    locals()[f'UP.R_{n_number}'] = Element(pairing2,G2)
    locals()[f'UP.R_{n_number}'] = hash_blc_G(locals()[f'user{i}'].P_i) * locals()[f'UP.q_{n_number}']+UP.I * locals()[f'UP.w_{n_number}']
    locals()[f'UP.c_{n_number}'] = locals()[f'UP.w_{n_number}']
    UP.c_plus += locals()[f'UP.c_{n_number}']
    locals()[f'UP.r_{n_number}'] = locals()[f'UP.q_{n_number}']
    locals()[f'UP.P_i_{n_number}'] = locals()[f'user{i}'].P_i
    if n_number == huan_number:
        n_number += 1
        locals()[f'UP.P_i_{n_number}'] = UP.X
        locals()[f'UP.q_{n_number}'] = Element.random(pairing2, Zr)
        locals()[f'UP.L_{n_number}'] = Element(pairing2, G2)
        locals()[f'UP.L_{n_number}'] = G_blc * locals()[f'UP.q_{n_number}']
        locals()[f'UP.R_{n_number}'] = Element(pairing2, G2)
        locals()[f'UP.R_{n_number}'] = hash_blc_G(UP.X) * locals()[f'UP.q_{n_number}']
        yaojiami =str(UP.m)+','+str(UP.A)
        for ii in range(1,huan_number+2):
            yaojiami += ","+str(locals()[f'UP.L_{ii}'])+","+ str(locals()[f'UP.R_{ii}'])
        UP.c = hash_blc_Z(yaojiami)
        locals()[f'UP.c_{n_number}'] = (UP.c - UP.c_plus)
        locals()[f'UP.r_{n_number}'] = locals()[f'UP.q_{n_number}']- locals()[f'UP.c_{n_number}']*UP.x
stop = time()
print("匿名奖励（单位用户）:" + str((stop - start)/N) + "秒")

#第七阶段：验证和接受奖励
start = time()
UP.c_max = Element.zero(pairing2,Zr)
for i in range(1,huan_number+2):
    locals()[f'Verify.L_{i}'] = G_blc * locals()[f'UP.r_{i}'] + locals()[f'UP.P_i_{i}']*locals()[f'UP.c_{n_number}']
    locals()[f'Verify.R_{i}'] = hash_blc_G(locals()[f'UP.P_i_{i}'])*locals()[f'UP.r_{i}'] + UP.I * locals()[f'UP.c_{n_number}']
    UP.c_max += locals()[f'UP.c_{i}']
yaojiami2 =str(UP.m)+','+str(UP.A)

for i in range(1, huan_number + 2):
    yaojiami2 += "," + str(locals()[f'Verify.L_{i}']) + "," + str(locals()[f'Verify.R_{i}'])
UP.c_verify = hash_blc_Z(yaojiami2)
if UP.c_verify == UP.c_max:
    pass
else:
    print("wrong")

for i in range(1,N+1):#计算奖励地址
    locals()[f'user{i}'].RE = G_blc*hash_blc_Z(UP.R*locals()[f'user{i}'].ai) + locals()[f'user{i}'].Bi
    locals()[f'user{i}'].re = hash_blc_Z(UP.R*locals()[f'user{i}'].ai) + locals()[f'user{i}'].bi
stop = time()

print("验证和接收奖励（单位用户）:" + str((stop - start)/N) + "秒")
