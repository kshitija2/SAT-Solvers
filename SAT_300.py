# Following code contains three fucntions with following three different heuristics to find possibly optimal truth assignments 
# for variables in Boolean formulas (total 300 formulas in dimacs format) and also compares performances of these heuristics.

# 1)	Hill Climbing Algorithm:
# Implemented hill climbing algorithm such that it randomly selects a new variable every time and assigns that variable a value
# (True or False) and calculate the number of clauses with truth assignment we get for both values i.e. True and False .
# Finally it selects the value to be assigned to that variable based on which gives higher number of true clauses.
# In this way it selects value for each variable in the formula.

# 2)	WalkSAT algorithm:
# Implemented walkSAT algorithm as it is given in the reference book of the class. 
# Used maximum flips as 100 as the formulas have 100 variables at most and p=0.5 as suggested in the reference book.
# Implemented algorithm first assigns random values to all the variables and loops for max flips. 
# In each loop, it chooses clause with truth value false and pick any variable from that clause and flips the value of that variable in the model with probability 0.5.

# 3)	DPLL algorithm:
# DPLL algorithm uses pure variable rule as well as unit propagation rule to resolve the formula in quick manner and 
# also a random variable is assigned a truth value and it checks if the formula is satisfiable. 
# When it assigns value to the variable, all the clauses with that variable are deleted from formula and 
# the clauses which has negation of that variable, simply that variable is deleted from the clause. 
# DPLL algorithm uses backtracking to assign truth values to variables and check if formula is satisfied. 
# It terminates when it founds formula empty i.e. the formula is satisfiable or one of the clauses empty 
# i.e. the formula is unsatisfiable.




# coding: utf-8

# In[ ]:

from random import *
import random
import copy
import glob
import os
import numpy as np
import matplotlib.pyplot as plt
import time
path = 'C:/Downloads/3cnf_100atoms/'
number=0
r_dpll=[]
r_hc=[]
r_ws=[]
t_dpll=[]
t_hc=[]
t_ws=[]
for filename in glob.glob(os.path.join(path, '*.cnf')):
    number=number+1
    file = open(filename, 'r')
    f=file.readlines()
    line=f[0]
    variables=int(line.split()[2])
    clauses=int(line.split()[3])
    file = open(filename, 'r')
    fp=file.readlines()

    arrayClauses=[]

    count=0
    for line in fp:
        for word in line.split():
            if word!=0:
                count=count+1
        if line.split()[0]=='p':
            arrayClauses.append([])
        elif line.split()[0]=='c':
            continue
        else:
            arrayClauses.append(list(map(int, line.split())))

    arrayClauses.remove([])

    for each in arrayClauses:
        if 0 in each:
            each.remove(0)


    def dpll(clauses=arrayClauses):
        if len(clauses)==0:
            return True

        for each in clauses:
            if len(each)==0:
                return False

        for each in clauses:
            for e in each:
                if -e in each:
                    each.remove(e)
                    each.remove(-e)
        pureLiterals=1
        while pureLiterals!=0:
            pureLiterals=0
            for i in range(1,variables+1):
                f=0
                for each in clauses:
                    if i in each:
                        f=1
                        break
                if f==1:
                    flag=0
                    for each in clauses:
                        if -i in each:
                            flag=1
                            break
                    if flag==1:
                        continue
                    if flag==0:
                        pureLiterals=i
                        break

                elif f==0:
                    flag1=0
                    for each in clauses:
                        if -i in each:
                            flag1=1
                            pureLiterals=-i
                            break
                    if flag1==1:
                        break
            if pureLiterals!=0:
                clausesWithPureLiterals=[]
                for each in clauses:
                    if pureLiterals in each:
                        clausesWithPureLiterals.append(each)

                for each in clausesWithPureLiterals:
                    clauses.remove(each)
        v=1
        while v!=0:
            v=0
            vList=[]
            for each in clauses:
                if len(each)==1:
                    v=each[0]
                    break

            if v!=0:
                for each in clauses:
                    if v in each:
                        vList.append(each)
                    if -(v) in each:
                        each.remove(-v)
                for z in vList:
                    clauses.remove(z)
        if len(clauses)==0:
            return True

        for each in clauses:
            if len(each)==0:
                return False

        varList=[]
        for each in clauses:
            for e in each:
                if abs(e) not in varList:
                    varList.append(abs(e))
        var=random.choice(varList)

        clauses1=copy.deepcopy(clauses)
        clauses2=copy.deepcopy(clauses)
        list1=[]
        for each in clauses1:
            if var in each:
                list1.append(each)
            if -(var) in each:
                each.remove(-var)
        for z in list1:
            if len(z)!=1:
                clauses1.remove(z)

        list2=[]
        for each in clauses2:
            if var in each:
                each.remove(var)
            if -(var) in each:
                list2.append(each)
        for z in list2:
            if len(z)!=1:
                clauses2.remove(z)
        result=dpll(clauses1) or dpll(clauses2)
        if result==True:
            return True
        else:
            return False

    def hillClimbing(clauses=arrayClauses):
        check=[]
        assignment={}
        for i in range(variables+1):
            f=0
            while f==0:
                x=randint(1,variables)
                f=1
                if x in check:
                    f=0
            check.append(x)
            y=True
            assignment.update({x:y})
            clauses1=[]
            for each in clauses:
                dict1={}
                for e in each:
                    dict1.update({e:' '})
                clauses1.append(dict1)
            for each in clauses1:
                for key,value in each.items():
                    if key in assignment.keys():
                        each[key]=assignment.get(key)
                    if -key in assignment.keys():
                        each[key]=not(assignment.get(key))

            max1=0
            for each in clauses1:
                if True in each.values():
                    max1=max1+1

            z=False
            del assignment[x]
            assignment.update({x:z})
            clauses1=[]
            for each in clauses:
                dict1={}
                for e in each:
                    dict1.update({e:' '})
                clauses1.append(dict1)
            for each in clauses1:
                for key,value in each.items():
                    if key in assignment.keys():
                        each[key]=assignment.get(key)
                    if -key in assignment.keys():
                        each[key]=not(assignment.get(key))

            max2=0
            for each in clauses1:
                if True in each.values():
                    max2=max2+1

            if max1>max2:
                del assignment[x]
                assignment.update({x:y})

            if max1>max2:
                return max1
            else:
                return max2

    def walkSAT(clauses=arrayClauses,p=0.5,max_flips=100):
        max1=0
        clauses1=[]
        for each in clauses:
            d={}
            for s in each:
                d.update({s:0})
            clauses1.append(d)
        model={}
        for i in range(1,variables+1):
            assignment=random.choice([True,False])
            model.update({i:assignment})
        for i in range(max_flips):
            for each in clauses1:
                for key,value in each.items():
                    h=abs(key)
                    if key>0:
                        each[key]=model.get(h)
                    if key<0:
                        each[key]=not(model.get(h))
    #         print(clauses1)
            c=0
            for each in clauses1:
                if True in each.values():
                    c=c+1
            if c==len(clauses):
                return model
            if c>max1:
                max1=copy.deepcopy(c)
            r1=[]
            r=[]
            r1_value=True
            while(1):
                r=random.choice(clauses1)
                if True not in r.values():
                    q=[]
                    for keys in r.keys():
                        q.append(keys)
                    r1=random.choice(q)
                    r1_value=r.get(r1)
                    break
                if True in r.values():
                    continue
            for each in clauses1:
                for key,value in each.items():
                    if key==r1:
                        if random.random()>=p:
                            each[key]=r1_value
                    if key==-(r1):
                        if random.random()>=p:
                            each[key]=not(r1_value)
        return (max1)

    
    start_time = time.time()
    result1=dpll(arrayClauses)
    if result1==True:
        result1=410
    if result1==False:
        result1=0
    r_dpll.append(result1)
    elapsed_time1 = time.time() - start_time
    t_dpll.append(elapsed_time1)
    
    start_time = time.time()
    result2=hillClimbing(arrayClauses)
    r_hc.append(result2)
    elapsed_time2 = time.time() - start_time
    t_hc.append(elapsed_time2)
    
    start_time = time.time()
    result3=walkSAT(arrayClauses)
    r_ws.append(result3)
    elapsed_time3 = time.time() - start_time
    t_ws.append(elapsed_time3)

x=[]
for i in range(1,301):
    x.append(i)
    
plt.ylabel('Number of Clauses Satisfied')
plt.xlabel('Serial Number of Instances')
plt.xticks(x)
plt.scatter(x,r_dpll,color='red')
plt.scatter(x,r_hc,color='blue')
plt.scatter(x,r_ws,color='yellow')

plt.show()

import matplotlib.pyplot as plt1
plt1.ylabel('Elapsed Time')
plt1.xlabel('Serial Number of Instances')
plt.xticks(x)
plt1.scatter(x,t_dpll,color='red')

plt1.scatter(x,t_hc,color='blue')


plt1.scatter(x,t_ws,color='yellow')
plt1.show()
    


# In[ ]:



