
#有限域上椭圆曲线群律运算以及相关算法
#version 2018.12.23
#written by yichugang

import random
p=1009                                #素数域
A=37                                  #椭圆曲线的A
B=0                                   #椭圆曲线的B

#==============有限域上椭圆曲线群律运算=====================
#===========================================================
def ZZ_p(x):                          #将x限制在有限域
    global p
    if (x>=0):
        return (x % p)
    return ((((-x//p)+1)*p+x)% p)

def generate_O():                     #生成一个不在椭圆曲线上面的点代表这个椭圆曲线上的零元，方便后面运算
    global p
    while True:
        testx,testy=random.randint(0, p),random.randint(0, p)
        if (ZZ_p(testy*testy)!=ZZ_p(testx*testx*testx+A*testx+B)):
            return testx,testy

#！！！！
Ox,Oy=generate_O()                   #事先约定Ox和Oy是有限域上椭圆曲线点群的零元
#！！！！

def gcd(a, b):#求最大公约数
    a=ZZ_p(a)
    b=ZZ_p(b)
    if (a<b):
        tt=a
        a=b
        b=tt
    if b==0:
        return -1
    if (a%b==0):
        return b
    return gcd(b,a%b)

def Extended_Euclidean(a,b):          #拓展欧几里得算法
    global p
    if b == 0:  
        return (1,0,a)   
    xx, yy, rr = Extended_Euclidean(b,a%b)  
    temp = xx   
    xx = yy    
    yy = temp - (a // b) * yy    
    return xx,yy,rr

def inv(x,modp):                #拓展欧几里得算法求逆
    ans=0
    if x==0:
        return ans
    xx,yy,dd=Extended_Euclidean(x, modp)
    return xx % modp 

def plus(x1, y1, x2, y2):                #有限域上椭圆曲线群律加法
    global p
    global Ox
    global Oy
    #以（Ox,Oy）来代替表示0元素，（Ox,Oy）不在曲线上，单独考虑
    if ((x1==Ox)and(y1==Oy)):#  0+Q
        return x2,y2
    if((x2==Ox)and(y2==Oy)):#  P+0
       return x1,y1
    if (x1==x2)&(y1!=y2):  #  P+（-P）
        return (Ox,Oy)
    if (x1==x2)&(y1==y2):   #P+Q 
        lamda=ZZ_p(ZZ_p(3*x1*x1+A)*inv(ZZ_p(2*y1),p))
    else:
        lamda=ZZ_p(ZZ_p(y1-y2)*inv(ZZ_p(x1-x2),p))   
    x3=ZZ_p(lamda*lamda-x1-x2)
    y3=ZZ_p(lamda*(x1-x3)-y1)
    return x3, y3

def mul(n, x4, y4):               #有限域上椭圆曲线求n倍（x4，y4）
    t1,t2=0,0
    q1,q2=x4,y4
    while (n>=1):
        if (n % 2==1):
            t1,t2=plus(t1,t2,q1,q2)
        q1,q2=plus(q1,q2,q1,q2)
        n=n//2
    return t1,t2

def sqrt_mod(x):                  #有限域开平方，p=4k+3有简便方法，需补充；
    global p
    ys=[]#会出现两个平方根
    for i in range(1,p):
        if (ZZ_p(i*i)==x):
            ys.append(i)
    return ys

def returny(x):                       #已知x，求该椭圆曲线上的坐标y
    temp=ZZ_p(x*x*x+A*x+B)
    return(sqrt_mod(temp))

#==============Miller算法=====================
#=============================================

def miller_g(gx1, gy1, gx2, gy2, tarx, tary):#双线性对中的g函数,求g_pq(tarx,tary),p(gx1,gx2),q(gx2,gy2)
    global p
    if (gx1==gx2)and(gy1!=gy2):#lambda=inf
        return ZZ_p(tarx-gx1)

    if (gx1==gx2)and(gy1==gy2):#lambda!=inf
        lambdag=ZZ_p(ZZ_p(3*gx1*gx1+A)*inv(ZZ_p(2*gy1),p))
    else:
        lambdag=ZZ_p(gy1-gy2)*inv(ZZ_p(gx1-gx2),p)
    fenzi=ZZ_p(tary-gy1-lambdag*(tarx-gx1))#分子
    fenmu=ZZ_p(tarx+gx1+gx2-lambdag*lambdag)#分母
    return ZZ_p(fenzi*inv(fenmu,p))

def miller_f(m, px, py, xx, yy):           #双线性对中f函数计算 Miller算法
    tx,ty = px,py
    mm = m
    f = 1
    mt=[]#存储二进制数码
    while mm > 0:
        mt.append(mm % 2)
        mm=mm//2
    mt.reverse()#倒序
    #print(mt)
    #Miller 算法
    for i in range(1,len(mt)):
        #print("i=",i,"mi",mt[i])
        f=ZZ_p(f*f*miller_g(tx,ty,tx,ty,xx,yy))
        tx,ty=plus(tx,ty,tx,ty)
        if (mt[i]==1):
            f=f*miller_g(tx,ty,px,py,xx,yy)
            tx,ty=plus(tx,ty,px,py)
        f=ZZ_p(f)
        #print("f",f)
    #print("ansf",f)
    return f

def cal_pairing(m,px,py,qx,qy,sx,sy):  #计算双线性对e_m(P,Q)， S为辅助点
    global p
    ans=0
    x1,y1=plus(qx,qy,sx,sy)           #Q+S
    x2,y2=sx,sy                       #S
    invsx,invsy=sx,-sy               
    x3,y3=plus(px,py,invsx,invsy)     #P-S
    x4,y4=invsx,invsy                 #-S
    #print("Q+S",x1,y1)
    #print("S",x2,y2)
    #print("P-S",x3,y3)
    #print("-S",x4,y4)
    s1=ZZ_p(miller_f(m,px,py,x1,y1)*inv(miller_f(m,px,py,x2,y2),p))#分子
    #print("s1",s1)
    s2=ZZ_p(miller_f(m,qx,qy,x3,y3)*inv(miller_f(m,qx,qy,x4,y4),p))#分母
    #print("s2",s2)
    ans=ZZ_p(s1*inv(s2,p))
    return ans

##-----test-----
#print("快速幂加法:",mul(7,2,4))
#print("gcd(27,18):",gcd(18,27))
#print("拓展欧几里得5x+3y=1",Extended_Euclidean(5,3))
#print("拓展欧几里得逆:",inv(9))
#xp=1980
#yp=431
#Qbx,Qby=mul(1943,xp,yp)
#print("Qb=nb*P",Qbx,Qby)
#print("na*Qb",mul(1943,2110,543))
#x5=2
#y5=returny(x5)
#print("Qb=nb*P",mul(875,xp,yp))
#print("nb*Qa",mul(875,x5,y5)
##-----test-----

###Miller算法计算双线性对
#ppx,ppy=417,952#P
#qqx,qqy=561,153#Q
#ssx,ssy=0,0#S
#m=7
#print("P({x},{y})".format(x=ppx,y=ppy))
#print("Q({x},{y})".format(x=qqx,y=qqy))
#print("e_5(P,Q)={x}".format(x=cal_pairing(m,ppx,ppy,qqx,qqy,ssx,ssy)))
print(inv(14,361))