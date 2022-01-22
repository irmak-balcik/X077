load "ozmansiksek.m";
X,Z,phi,j,al,jd:=modeqns(77,11); //takes a while
RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
rows:=[[&+ [RowSequence(a)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]] : a in al] ;
w7:=iso<X->X | rows[1],rows[1]>;
w11:=iso<X->X | rows[2],rows[2]>;
w77:=iso<X->X | rows[3],rows[3]>;
cusps:=PointSearch(X,1500);
Dtors:=[Divisor(cusps[i]) - Divisor(cusps[1]) : i in [2,3,4]]; //takes a while
J:=JZero(77);
A:=RationalCuspidalSubgroup(J);
A; //returns Z10 x Z60

//Finding generators of Z10 x Z60
X3:=ChangeRing(X,GF(3));
C,phi,psi:=ClassGroup(X3); 
Z:=FreeAbelianGroup(1);
degr:=hom<C->Z | [Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
JF3:=Kernel(degr);
JF3; //returns Z10 x Z420
redDtors:=[JF3!psi(reduce(X,X3,DD)) : DD in Dtors];
A:=sub<JF3 | redDtors>;
A; //returns Z10 X Z60
Z3:=FreeAbelianGroup(3);
hh:=hom<Z3->A | redDtors>;
hh(Z3.1); // returns 9A.1 + 3A.2
hh(Z3.2); // returns 8A.1 + 35A.1
hh(Z3.3); // returns A.1 + 8A.2
//solving for A.1 and A.2 we obtain
assert hh(-8*Z3.1+3*Z3.3) eq A.1;
assert hh(31*Z3.2-8*Z3.3) eq A.2;
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 6*hh(31*Z3.2-8*Z3.3) eq hh(-8*Z3.1+3*Z3.3); 
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 18*hh(31*Z3.2-8*Z3.3) eq hh(-8*Z3.1+3*Z3.3);
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 42*hh(31*Z3.2-8*Z3.3) eq hh(-8*Z3.1+3*Z3.3);
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 54*hh(31*Z3.2-8*Z3.3) eq hh(-8*Z3.1+3*Z3.3);
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 12*hh(31*Z3.2-8*Z3.3) eq 2*hh(-8*Z3.1+3*Z3.3);
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 24*hh(31*Z3.2-8*Z3.3) eq 2*hh(-8*Z3.1+3*Z3.3);
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 36*hh(31*Z3.2-8*Z3.3) eq 2*hh(-8*Z3.1+3*Z3.3);
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 48*hh(31*Z3.2-8*Z3.3) eq 2*hh(-8*Z3.1+3*Z3.3);
Order(hh(31*Z3.2-8*Z3.3)) eq 60 and not 30*hh(31*Z3.2-8*Z3.3) eq 5*hh(-8*Z3.1+3*Z3.3);

//computing C:=X/<w77> and J(C)(Q)
Cprime,projC:=CurveQuotient(AutomorphismGroup(X,[w77])); //takes a while
C,h:=SimplifiedModel(Cprime);
XtoC:=Expand(projC*h);
ptsC:=Setseq(Points(C: Bound:=1000));
ptsC;
J:=Jacobian(C);
TorsionSubgroup(J);//returns Z5
RankBounds(J); //this shows J(C)(Q) has rank 1
ptsJ:=[ptsC[i] - ptsC[1] : i in [2,3,4,5,6]];
Q1:=ptsC[6]-ptsC[1];
Order(Q1); // Q1 has order 5
Q2:=ptsC[2]-ptsC[1];
Order(Q2); // Q2 has an infinite order

//free generator of J(X)(Q) 
D1:=Pullback(XtoC, Place(ptsC[2]) - Place(ptsC[1]));
bp:=Pullback(XtoC, Place(ptsC[1]));
assert bp eq Place(cusps[2]) + Place(cusps[4]);
or
assert bp eq Place(cusps[2]) + Place(w77,Place(cusps[2])); //takes a few minutes
Km19<rtm19>:=QuadraticField(-19);
P1:=X(Km19)![1/2*(rtm19-1), rtm19-1, 1/2*(rtm19-5), rtm19-2, 1/2*(3*rtm19-1),1/2*(3*rtm19-1),1];
assert Place(P1) - bp eq D1; //takes a while

P2:=X(Km19)![1/2*(-rtm19-7), 1/2*(-3*rtm19 -3), -rtm19, 1/2*(-rtm19+1),-rtm19-1, 1/2*(-3*rtm19-5),1];
Km7<rtm7>:=QuadraticField(-7);
P3:=X(Km7)![-rtm7-2, 1/2*(-3*rtm7-1), 1/2*(-rtm7-1),1/2*(-rtm7-3),1/2*(-3*rtm7-3), 1/2*(-3*rtm7-3),1];
P4:=X(Km7)![rtm7-2, 1/2*(7*rtm7-1), 1/2*(rtm7-1),1/2*(5*rtm7-3),1/2*(3*rtm7-3), 1/2*(-3+7*rtm7),1];
pls2:=[Place(P1),Place(P2),Place(P3),Place(P4)];
ptsX:=PointSearch(X,1500);
pls1:=[Place(pt) : pt in ptsX];
deg2:=[1*pl : pl in pls2] cat [1*Place(pt1) + 1*Place(pt2) : pt1 in ptsX, pt2 in ptsX];
deg2pb:=[1*pl : pl in pls2 | XtoC(RepresentativePoint(pl)) in C(Rationals())] cat [1*pl1 + 1*pl2 : pl1 in pls1, pl2 in pls1 | w77(RepresentativePoint(pl1)) eq RepresentativePoint(pl2)]; 
deg2npb:=[DD : DD in deg2 | not DD in deg2pb];
A:=AbelianGroup([0,10,60]);
divs:=[D1,-8*Dtors[1]+3*Dtors[3],31*Dtors[2]-8*Dtors[3]];
genusC:=Genus(C);
auts:=[al[3]];
I:=2;
primes:=[19,23];
load "quadptssieve.m";
MWSieve(deg2,primes,X,A,divs,auts,genusC,deg2pb,deg2npb,I,bp); 
