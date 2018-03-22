include "globals.mzn";
include "alldifferent.mzn";
int :nr;
int :nc;
int :ndefh;
int :ndefv;
int :r;
int :s;
array[1..nr, 1..nc] of var r..s: solution;
array[1..ndefh,1..3] of int: defH;
array[1..ndefv,1..3] of int: defV;
array[1..nr,1..nc] of int: problem;



constraint forall(i in 1..ndefh) ( 
                if defH[i,1] mod nc != 0 then
                  sum (j in 1..nc where j >= (defH[i,1] mod nc)  /\ j < ((defH[i,1] mod nc) + defH[i,3])) (solution[(defH[i,1] div nc)+1,j]) = defH[i,2] 
                else
                  sum (j in 1..nc where j >= nc) (solution[(defH[i,1] div nc),j]) = defH[i,2]
                endif         
);


constraint forall(i in 1..ndefv) (                         
              if defV[i,1] mod nc == 0 then
                sum ( j in 1..nr where j >= (defV[i,1] div nc) /\ j < ((defV[i,1] div nc) + defV[i,3])) (solution[j, nc]) = defV[i,2]
              else
                sum ( j in 1..nr where j >= (defV[i,1] div nc)+1 /\ j < ((defV[i,1] div nc) + 1 + (defV[i,3]))) (solution[j, defV[i,1] mod nc]) = defV[i,2]
              endif   
);


solve satisfy;

output[
if problem[i,j] == 0 then
  if j mod nc == 0 then 
    " *" ++ "\n" 
  else " *" ++ " "
  endif
else
  if j mod nc == 0 then show_int(2,solution[i,j]) ++ "\n"
  else show_int(2,solution[i,j]) ++ " "
  endif
endif | i in 1..nr, j in 1..nc


];      

