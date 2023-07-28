/* Copyright 2015 by Jennifer Paulhus 

This work is licensed under a Creative 
CommonsAttribution-NonCommercial-ShareAlike 
4.0 International license. 
*/

   
/*

To use these programs, you will need to enter a "filename" for
the path of the data for a specific genus downloaded from:
  http://www.math.grinnell.edu/~paulhusj/monodromy.html

Remember, if you want to use the generating vectors, you must convert
  the group G to a permutation group first. Code to do this is included here
  as the function ConvertToPerm.
  
*/


/*  
Programs
--------
ConvertToPerm(G) -- converts group of type PC to permutation gp

ReadData(filename, function) -- reads in file "filename", executes
boolean "function" on the data, and returns all entries from the 
data which satisfy the "function" as a list of Magma readable data

FindGroup(filename,groupsize,groupnum) -- finds all occurances of 
SmallGroup(groupsize,groupnum) in the data of "filename"

FindSignature(filename,signature) -- finds all occurances of 
[signature] in the date of "filename"

LoadAllData(filename) -- loads all data in the file in a list of 
Magma readable data.  WARNING: This is too big for larger genus.  

At the bottom of this file are two samples of Magma programs which
show how to use the program ReadData to either enter all Nilpotent
examples for a given genus directly into Magma as a list, or to
print the examples to an external file. The programs have been
commented out so you can read this file without calling them
    
*/





/* *************************************
ConvertToPerm(G)

Input: G a group of type PC

Output: a group of type Perm

Based on Magma algorithm here:
http://magma.maths.usyd.edu.au/magma/handbook/text/705#7874
**************************************** */ 
         
ConvertToPerm:=function(G);
        
if Type(G) eq GrpPC then
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





/* *************************************
ReadData(filename, functioncall)

Input: - name of file of Breuer type data
       - function you wish to have 
         executed on the data, it must call 
         variables G (group), sign (signature), 
         Lmonod (the generating vectors) and
         return "true/false"


Output: OutputList

**************************************** */ 

ReadData:=function(filename,functioncall);


OutputList:=[* *];  /* List that is data in Magma format which
                       satisfies criteria of functioncall */

FP:=Open(filename, "r");

dataline:=Gets(FP);


while IsEof(dataline) eq false do


if #dataline ne 0 then  /* Deals with blank lines */

  nomonod:=0;    /* test variable for cases with no monod */

/* read group order from line 1*/
  order:=dataline[2];
  i:=3;
  while dataline[i] ne "," do
     order:=order cat dataline[i];
     i+:=1;
  end while;
  GpOrder:=StringToInteger(order);

  i+:=1;    /* go past comma in line 1*/
 


/* read group size */
  numb:=dataline[i];
  i+:=1;
  while dataline[i] ne ")" do
     numb:=numb cat dataline[i];
  i+:=1;
  end while;
  GpNum:=StringToInteger(numb);



/* create group G from line 1 as permutation group */
  G:=ConvertToPerm(SmallGroup(GpOrder,GpNum));



/* read line 2*/   
  dataline:=Gets(FP);


/* read signature */
  sign:=[];
  i:=3;
  while dataline[i] ne "]" do
    
    term:=dataline[i];
    i+:=1;
    while (dataline[i] ne ",") and (dataline[i] ne " ") do
       term:= term cat dataline[i] ;
       i+:=1;
    end while;

    Append(~sign, StringToInteger(term));   
    i+:=1;
  end while;



/* read line 3*/   
  dataline:=Gets(FP);

/* read conjugacy classes of signature */
  conjclasses:=[];

  if dataline[2] eq "]" then  /* case with no monod */
     nomonod:=1;
  else 

  i:=3;
  while dataline[i] ne "]" do
    
    term:=dataline[i];
    i+:=1;
    while (dataline[i] ne ",") and (dataline[i] ne " ") do
       term:=term cat dataline[i];
       i+:=1;
    end while;
    Append(~conjclasses, StringToInteger(term));   
    i+:=1;
  end while;

  end if;


/* read remaining lines which are generating vectors */

  dataline:=Gets(FP);



  Lmonod:=[];  /* this will be the list of generating vectors */
  while dataline[1] ne "*" do
                     
     /* read each term one by one */ 
    elt:=[];  /* permutation element of group*/

    i:=1;

    if nomonod eq 1 then
       Append(~Lmonod, []);

    else
    while i le #dataline do 
       term:=dataline[i];
       if i eq #dataline then
          Append(~elt, StringToInteger(term)); 
       else
          i+:=1;
          tester:=0;
          while (dataline[i] ne " ") and (tester eq 0) do
             if i eq #dataline then
                term:=term cat dataline[i];   
                tester:=1;
             else  
                term:=term cat dataline[i];                   
                i+:=1;
             end if;
          end while;
          Append(~elt, StringToInteger(term));
       end if;
 
       i+:=1;
    end while;

    Append(~Lmonod,G!elt); 
    end if; 

    dataline:=Gets(FP); 
  end while;



  if functioncall(G,sign,Lmonod) eq true then
     Append(~OutputList,[*G,sign,Lmonod*]);
  end if;


end if;

dataline:=Gets(FP); 

end while;   

return OutputList;

end function;


/* The next set of programs are samples that
   may be used as input for ReadData */



/* *************************************
FindGroup(filename,gpsize,gpnum)

Input: - name of file of Breuer type data
       - group (gpsize,gpnum)

Output: list of groups,signatures and 
        monodromy of any entry of this genus 
        with such a group

**************************************** */ 

FindGroup:=function(filename,gpsize,gpnum);

   H:=SmallGroup(gpsize,gpnum);

   CompareGroup:=function(G,sign,Lmonod);
     if IsIsomorphic(G,H) then
        return true;
        else return false;
     end if;
   end function;

   L:=ReadData(filename,CompareGroup);

   return L;

end function;



/* *************************************
FindSignature(filename,signature)

Input: - name of file of Breuer type data
       - sign (signature) 

Output: list of groups,signatures and 
        monodromy of any entry of this genus 
        with such a signature

**************************************** */ 

FindSignature:=function(filename,signature);

   CompareSign:=function(G,sign,Lmonod);
      return signature eq sign;
   end function;
 
   L:=ReadData(filename,CompareSign);

   return L;

end function;


/* *************************************
LoadAllData(filename)

Input: - name of file of Breuer type data
      

Output: all data from the file stored in
        a list of Magma readable information

WARNING:  This will not be tenable for high 
          genus as the data is too large.

**************************************** */ 

LoadAllData:=function(filename);

   AllTrue:=function(G,sign,Lmonod);
      return true;
   end function;
 
   L:=ReadData(filename,AllTrue);

   return L;

end function;



/* *********************************************** 
   Finally we provide a sample of two ways to use
   ReadData. The first example saves all Nilpotent
   Groups in the data in a list directly in Magma.
   The second example prints the list to an
   external file. 
 ********************************************** */


/* Example One -- Enter list directly to Magma 
Nilp1:=function(G,sign,Lmonod);

    return IsNilpotent(G);   

end function;


L:=ReadData(filename, Nilp1);  */





/* Example Two -- Print results to external file 

outputfile:="FILL";
   
Nilp2:=function(G,sign,Lmonod);

  if IsNilpotent(G) then
      PrintFile(outputfile, "Group:");
      PrintFile(outputfile, "(" cat IntegerToString(IdentifyGroup(G)[1]) cat ", " cat IdentifyGroup(G)[2]) cat ")" );
      PrintFile(outputfile, "Signature:" );
      PrintFile(outputfile, sign );
     PrintFile(outputfile, "Generating vectors:");
     PrintFile(outputfile, Lmonod);
     PrintFile(outputfile, "*******");

   return false;
    
end function;


ReadData(filename, Nilp2);

   */









