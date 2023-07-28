/* genvectors.m

Last Updated: May 10, 2016
   
These functions are primarily Magma versions of GAP programs
written by Thomas Breuer.
   
Breuer, Thomas. Characters and automorphism groups of compact Riemann surfaces. London Mathematical Society Lecture Note Series,  v. 280. Cambridge University Press, Cambridge, 2000.

The original GAP code has the following copyright:
Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany

We are grateful to Thomas Breuer for permission to post the Magma version of this code. 
   
Functions:
ConvertToPerm(G)

CardinalityOfHom(C, g0, tbl, classlengths, ordG)
NonGenerationByScottCriterion(tbl, C, sizeconjclass, ordG)
WeakTestGeneration(C, g0, G)
HardTestGeneration(C, g0, G)
RepresentativesEpimorphisms(signature, G)

Procedure:
AddMonodromy(g)  

*/



Z:=Integers();   /* Used for coersion below */

SetColumns(0);  /* Better Printing */



/* ***************************************
ConvertToPerm(G)

Inputs: G            group 

Outputs: a group of type GrpPerm in Magma

Based on Magma algorithm here:
http://magma.maths.usyd.edu.au/magma/handbook/text/705#7874


************************************ */

ConvertToPerm:=function(G);
        
if   Type(G) eq GrpPC then
   SL := Subgroups(G);
   T := {X`subgroup: X in SL};
   TrivCore := {H:H in T| #Core(G,H) eq 1};
   mdeg := Min({Index(G,H):H in TrivCore});
   Good := {H: H in TrivCore| Index(G,H) eq mdeg};
   H := Rep(Good);
   f,G,K := CosetAction(G,H); 
end if;

return G;

end function;



/* ***************************************
CardinalityOfHom( C, g0, tbl, classlengths,ordG)

Inputs: C
        g0           orbit genus
        tbl          character table of a group G
        classlength  list of size of each conj class 
        ordG         order of a group G



Outputs: the cardinality of Hom_C(g_0,G) computed using
         a result of Jones (Section 14 of Breuer)


Used in WeakTestGeneration
************************************ */

CardinalityOfHom := function( C, g0, tbl ,classlength, ordG)

r:=#C; 
M:=[];
    
for i in [ 1 .. r ] do
   if C[i] in Z then
      M[i]:= [C[i]];
   else
      M[i]:=C[i];  
   end if;
end for;
C:=M;
      
exp:= 2 - 2*g0 - r;
sum:=0; 

for i in [1..#tbl] do
   chi:=tbl[i];   
   product:=1;   
   for Ci in C do
      temp:=0;  
      for j in [1..#Ci] do
         temp:=temp+chi[Ci[j]]*classlength[Ci[j]]; 
      end for;
   product:=product*temp;  
   end for;          
   sum:=sum+(chi[1]^exp*product);   
end for;
   
sum:=Rationals()!sum;
    
return ordG^( 2*g0 - 1 )* sum;

end function;





/* ***************************************
NonGenerationByScottCriterion(tbl, C, sizeconjclass, ordG )

Tests the Nongeneration Criterion of Scott 
    (Section 15.3 in Breuer)

Input:  Character Table of a group
        C list of 
        sizeconjclass
        ordG   The order of the group G


Output: true if the nongeneration criterion of Scott 
           confirms that there is no epimorphism   
        false otherwise

Used in: WeakTestGeneration

************************************ */

NonGenerationByScottCriterion := function( tbl,C,G,Con)

        
for chi in tbl do
   degree:= chi[1]; 
   dim:= 2 * ( degree - InnerProduct( chi,tbl[1]));  
       
   for i in C do
      xi:= Con[i,3];
      S:=sub<G|xi>;
      Ts:=CharacterTable(S);
      dim:= dim - degree + InnerProduct(Restriction(chi,S) ,Ts[1]);
   end for;
    
   if 0 lt dim then
      return true;
   end if;
end for;

return false;

end function;





/* ***************************************
WeakTestGeneration(C, g0, G)

Inputs:  C the class structure of G
         g0 the orbit genus
         G a finite group

Outputs: false if Epi_C(g,G) is empty based on
            Nongeneration criterion of Scott or
            conditions on the cardinality of Hom 
            (Section 15.1 of Breuer) 

         true otherwise

Used in RepresentativesEpimorphisms
************************************ */

WeakTestGeneration := function( C, g0, G )
        
tbl:= CharacterTable( G );    
size:=#G; 
Con:=ConjugacyClasses(G);
numb:=0;
sizeconjclass:=[];
        
for i in [1..#Con] do  
   if Con[i][2] eq 1 then 
      numb:=numb+1;
   end if;
   Append(~sizeconjclass,Con[i][2]);
end for;
       
if CardinalityOfHom(C, g0, tbl, sizeconjclass,size) lt size/numb  then    
   return false; 
elif g0 eq 0 and NonGenerationByScottCriterion( tbl, C, G, Con ) then 
   return false;
end if;

return true;

end function;





/* ***************************************  
HardTestGeneration(C, g0, G)

Inputs:  C the class structure of G
         g0 the orbit genus
         G a finite group


Outputs: tup   which is a list of elements of G 
               representing the monodromy

         [id_G,id_G]  otherwise


Used in RepresentativesEpimorphisms

************************************ */

HardTestGeneration := function( C, g0, G )

r:=#C;
n:=#( G );
id:=Identity(G);
 

Con:=ConjugacyClasses(G);
sigma:=[];   /* list of representatives of conjugacy classes */
for i in [1..r] do 
   Append(~sigma,Con[C[i]][3]); 
end for;
 

rep_cen:=[]; /* list of centralizers for each element of sigma */
for s in sigma do 
   Append(~rep_cen,Centralizer(G,s)); 
end for;

/*Initialize iteration */
if 0 lt  r then
   iter_cen:= [rep_cen[1]];
   R:= [[id]];
else
   iter_cen:= [];
   R:= [];
end if;

  
for i in [ 2 .. r-1 ] do
   R[i]:= DoubleCosetRepresentatives(G, rep_cen[i],iter_cen[i-1] );       
   iter_cen[i]:= iter_cen[i-1] meet Centralizer(G,sigma[i]^R[i][1] );
end for;
  
  
if 1 lt  r then
   R[r]:= DoubleCosetRepresentatives( G, rep_cen[r], iter_cen[r-1] );
end if;
   
max:=[];
for i in [1..#R] do 
   Append(~max,#R[i]);
end for; 
    
    /* List of all ones  */
choice:= [];
for i in [1..r] do 
   Append(~choice,1);
end for;
   
     /* list of sigma[i]^R[i][1]; */
tuple:=[];
for i in [1..r] do 
   Append(~tuple, sigma[i]^R[i][1] );
end for;
  
  

/* function: NextElementTuple */
     
NextElementTuple:= function(choice, bleck, iter_cen, R, max)
      
      
  pos:= r;
  while 1 lt pos and choice[pos] eq max[pos] do
     pos:= pos - 1;
  end while;
  if pos le 1 then
     return choice, [id,id], iter_cen, R, max;
  end if;

       
  choice[pos]:= choice[pos] + 1;
  bleck[pos]:= sigma[pos]^R[pos][choice[pos]]; 
  if pos lt r then
     iter_cen[pos]:= iter_cen[pos-1] meet  Centralizer(G,sigma[pos]^R[pos][choice[pos]]);
     pos:= pos + 1;
     while pos le r do
        R[pos]:= DoubleCosetRepresentatives(G, rep_cen[pos], iter_cen[pos-1]);
        bleck[pos]:= sigma[pos]^R[pos][1];
        choice[pos]:= 1;
        max[pos]:= #R[pos] ;
       iter_cen[pos]:=iter_cen[pos-1] meet Centralizer(G,sigma[pos]^R[pos][1]);
        pos:= pos + 1;
     end while;

   end if;


   return choice, bleck, iter_cen, R, max;
end function;
    
  
      
tup:= tuple;
genvecs:=[];
      
while tup ne [id,id] do

      
   prod:= id;
   for i in [1..r] do
      prod:= prod * tup[i];
   end for;

   

   if g0 eq 0 then
      if prod eq  id and #sub<G | tup >  eq  n then
                 
         hypgens:=[];
       
         for t in tup do 
            Append(~hypgens,t);
         end for;

        Append(~genvecs, hypgens);
   
          
      end if;
      
      else
        ReduceGenerators(~G);  /* removes redundancies */

      if   prod  eq  id and NumberOfGenerators(G)  le g0 then

      hypgens:=[];
      for h in Generators(G) do
         Append(~hypgens,h);
         Append(~hypgens,id);
      end for;
 
      for i in [#hypgens+1..2*g0] do
         Append(~hypgens,id);
      end for;
   
      for t in tup do
          Append(~hypgens,t);
      end for;

      Append(~genvecs, hypgens);
         


   elif prod eq id and IsAbelian(G) and NumberOfGenerators(G) le  2*g0 then

      hypgens:=Generators(G);
      hypgens:=SetToSequence(hypgens);

      for i in [#hypgens+1..2*g0] do
         Append(~hypgens,id);
      end for;

      for t in tup do          
         Append(~hypgens,t);
      end for;

        Append(~genvecs, hypgens);
            


          
   else
      
      elms:=[];
          
      for h in G do  
         Append(~elms,h);
      end for;
          
          
      counter:=[]; 
      counter[1]:= 0;
      for i in [2..2*g0] do
         Append(~counter,1); 
      end for;
     
      repeat
         i:= 1;
         while i le 2*g0 and counter[i] eq n do
            counter[i]:= 1;
            i:= i+1;
         end while;

         if i le 2*g0 then
            counter[i]:=counter[i] + 1;
            commprod:= id;
            for j in [1..g0] do
               commprod:=commprod*(elms[counter[2*j-1]], elms[counter[2*j]]);
                  /* commutator is (g,h) */
            end for;
            
                                                              

            if commprod*prod eq id then
    
               
               tempelms:=[];
               for c in counter do
                  Append(~tempelms,elms[c]);
               end for;
                 
               H:=tup;
               for h in tempelms do
                  Append(~H,h);
               end for;      
              
               if #sub<G|H> eq n then

                     for t in tup do
                        Append(~tempelms, t);
                     end for;  
                     
             Append(~genvecs, tempelms);
             

               end if; 
            end if;
         end if ;
         until i  gt  2*g0;
      end if;  end if;
         


   choice, tup, iter_cen, R, max:= NextElementTuple(choice, tup, iter_cen, R, max);

end  while;


if #genvecs gt 0 then
   return genvecs;
else 
   return [[id,id]];
end if;

end function;


  


/* ***************************************
RepresentativesEpimorphisms(signature,G)
 

Input: signature  
       group G


Output: a list of records containing
           the signature,
           the numbers listing which conjugacy classes
             contain branching data,
           the group,
           the monodromy
 

Breuer's notes:  

##  Let <signature> be the list $[ g_0, r, m_1, m_2, \ldots, m_r ]$,
##  with $m_1 \leq m_2 \leq \cdots m_r$.
##
##  First the conjugacy classes of <G> are computed.
##  Then all possible class structures $C = ( C_1, C_2, \ldots, C_r )$
##  are checked for a surface kernel epimorphism with image of $c_i$ in
##  class $C_i$.
##
##  We restrict the search to the class structures where the elements of
##  class $C_i$ have order $m_i$,
##  and for $m_i = m_{i+1}$, we consider only the case that $C_i$ comes
##  not after $C_{i+1}$ in the fixed ordering of classes.
##

************************************ */

RepresentativesEpimorphisms := function(signature,G)

g0:= signature[1];      /* orbit genus */
r:= #signature  - 1;    /* branch points */    
m:= Reverse(Prune(Reverse(signature)));
        


  /* Change G to GrpPerm if of type GrpPC */
if Type(G) ne GrpPerm then
  if Type(G) eq GrpPC then
     G:=ConvertToPerm(G);
  else
     return "Error: Must be a group of type GrpPerm or GrpPC.";
  end if;  
end if;

           

ccl:= ConjugacyClasses( G );
nccl:= #ccl;
orders:= [];
    


for conjclass in ccl  do 
   Append(~orders, conjclass[1] );
end for;
     
images:=[];
for i in [1..r] do
   temp:=[];
   for j in [1..nccl] do
      if orders[j] eq m[i] then  
         Append(~temp,j);
      end if;
   end for;
   Append(~images, temp);
end for;     
  
if exists(u){x: x in images | #x eq 0} then 
   return [];        
end if;
  
epi:= [];    
ReFo := recformat< signature,Con,Gro,genimages>;  

max:= [];
for im in images do 
   Append(~max, #im);
end for;
   
counter:= [];
for i in [1..#images] do 
   Append(~counter,1 );
end for;
    
if 0 lt r then
   counter[r]:= 0;
end if;


 
/* function: NextClassStructure  */
    
if r eq 0 then  /* create function for case where there is no ramification */

    NextClassStructure:= function(counter,max)
       if counter ne [-100] then
          counter:= [-100];
          return [],counter;
       else
          return [-100],counter;
       end if;
    end function;

else      /* function for case where there is ramification */

    NextClassStructure:= function(counter,max)
       for i:=r to 1 by -1  do
          if counter[i] eq max[i] then
             counter[i]:= 1;

          else
             counter[i]:= counter[i] + 1;
             j:= i;
             while j lt r and m[j] eq m[j+1] do
                if counter[j+1] lt counter[j] then
                   counter[j+1]:= counter[j];
                end if;
                j:= j+1;
             end while;

             templist:=[];
             for j in [1..r] do 
                Append(~templist,images[j][counter[j]]);
             end for; 
                            
             return  templist,counter;
      
            end if;
          end for;
          return [-100],counter;
      end function;

end if;
    
C,counter:= NextClassStructure(counter,max);
             
while C ne [-100] do
   weak:= WeakTestGeneration( C, g0, G );
             
   if weak ne false then
            
  
   test:= HardTestGeneration( C, g0, G);
             
          
      if test ne  [[Identity(G), Identity(G)]] then
        for t in test do
         Append(~epi, rec<ReFo|signature:=signature, Con:=C, Gro:=G, genimages:=t>);
        end for;
      
      end if;
   end if;
      

   C,counter:= NextClassStructure(counter,max);
end while;

return epi;

end function;






/* *************************************
Add Monodromy(g)

Input: g genus
       BrDataPath location of Breuer data
       OutputPath location to store monodromy data

Output: write to file "storefilename" with monodromy data 

**************************************** */

AddMonodromy:=procedure(g,BrDataPath,OutputPath)


/* Load Data from Breuer */
if g lt 10 then
        
   filename:=BrDataPath cat "genus" cat "0" cat IntegerToString(g) cat  "/groups" cat "0" cat IntegerToString(g);
   storefilename:= OutputPath cat "grpmono" cat "0" cat IntegerToString(g);


else   

    filename:=BrDataPath cat "genus"  cat IntegerToString(g) cat  "/groups"  cat IntegerToString(g);
    storefilename:=OutputPath cat "grpmono" cat  IntegerToString(g);

end if;      


FP:=Open(filename, "r");


dataline:=Gets(FP);

count:=1;
while IsEof(dataline) eq false  do 

/* if starts with "#" or  "R" skip */
if dataline[1] ne "#" and dataline[1] ne "R" then

   i:=1;
   while dataline[i] ne "[" do
      i+:=1;
   end while;

   i+:=1;
   sign:=[];
   while dataline[i] ne "]" do
      if (dataline[i] ne ",") and (dataline[i] ne " ") then
	 term:=dataline[i];
	 i+:=1;
	 while dataline[i] ne "," and dataline[i] ne " " do
	    term:=term cat dataline[i];
	    i+:=1;
	 end while;	
	 Append(~sign,StringToInteger(term));
      end if;
      i+:=1;
   end while;
	
                  
   while dataline[i] ne "[" do
      i+:=1;
   end while;

   i+:=1;
   gpsize:=dataline[i];
   while dataline[i+1] ne "," do
      gpsize:=gpsize cat dataline[i+1];
      i+:=1;
   end while;		

   i+:=3;
   gpnum:=dataline[i];
   while dataline[i+2] ne "]" do
      gpnum:=gpnum cat dataline[i+1];
      i+:=1;
   end while;	

  /* save sign, gpsize,gpnum; */

   gpsize:=StringToInteger(gpsize);
   gpnum:=StringToInteger(gpnum);
   G:=SmallGroup(gpsize,gpnum);


   if #sign eq 1 then  /* deal with case of no monodromy separately */
      groupstring:=  "(" cat IntegerToString(gpsize) cat"," cat IntegerToString(gpnum) cat")"; 

      PrintFile( storefilename, groupstring);
      PrintFile( storefilename, sign);
      PrintFile(storefilename, "[]"); 
      PrintFile(storefilename, "*"); 

   else 

      RepEp:=RepresentativesEpimorphisms(sign, G);

      for rep in RepEp do
        groupstring:=  "(" cat IntegerToString(gpsize) cat"," cat IntegerToString(gpnum) cat")"; 
        PrintFile( storefilename, groupstring);
        PrintFile( storefilename,Sprint(rep`signature));
        PrintFile(storefilename, Sprint(rep`Con)); 

        for i in [1..#rep`genimages] do	 
           tempval:=Eltseq(rep`genimages[i]);
           stringperm:=IntegerToString(tempval[1]);
	   for j in [2..#tempval] do
              stringperm:=stringperm cat " " cat  IntegerToString(tempval[j]);
           end for;  
    	   PrintFile( storefilename, stringperm);
        end for;   

        PrintFile(storefilename, "*"); 
          
      end for;
   end if;
end if;

dataline:=Gets(FP);

end while;


end procedure;
