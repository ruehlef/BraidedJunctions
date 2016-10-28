(* ::Package:: *)

(* ::Text:: *)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%                                                                                                                                                  			%*)
(*%                                                                   BraidedJunctions v0.1                                                                     	%*)
(*%                                                                                                                                                                           	%*)
(*%                                                                  author: Fabian Ruehle                                                      	      	%*)
(*%                                                      email: fabian.ruehle@physics.ox.ac.uk                          		      	%*)
(*%                                                                                                                                                  			%*)
(*%                                                                                                                                                  			%*)
(*%            Developed for:    	Dualities of Deformed N = 2 SCFTs from Link Monodromy on D3-brane States	%*)
(*%				Antonella Grassi, Jim Halverson, Fabian Ruehle, Julius Shaneson			%*)
(*%				arXiv: 16xx.xxxxx									%*)
(*%                                                                                                                                                  			% *)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


BraidedJunctions::usage=
"This package has been developed to carry out basic computations for string junctions and torus knots/links. It contains functions used in [arXiv:]. 

The main focus is on computing group theory related information for string junction vectors and how they behave under an action induced by a torus knot or link. The conventions used here (e.g. for the vanishing cycles, braiding, ...) are the ones used and explained in the paper. Please make sure you either use these conventions or adapt the code according to your conventions. 

The vanising cycles are chosen as pi1 = {1, 0}, pi2 = {-1, -1}, pi3 = {0, 1}.
"
?BraidedJunctions


(* ::Section:: *)
(*Global Functions*)


(* ::Subsection::Closed:: *)
(*General Functions*)


removeAnd := {(x__) && (y__) :> {x, y}}; 
removeOr := {(x__) || (y__) :> {x, y}}; 
putArrow := {(x__) == (y__) :> x -> y}; 
compareSets[s1_, s2_] := Return[Length[s1] == Length[s2] && Complement[s1, s2] == {}]; 
pi1 = {1, 0}; pi2 = {-1, -1}; pi3 = {0, 1}; 
hw27 = {{1}, {1, 2}, {1, 2, 3}, {1, 2, 3, 4}, {1, 2, 3, 6}, {1, 2, 3, 4, 5}, {1, 2, 3, 6, 4}, {1, 2, 3, 4, 5, 6}, 
    {1, 2, 3, 6, 4, 3}, {1, 2, 3, 4, 5, 6, 3}, {1, 2, 3, 6, 4, 3, 2}, {1, 2, 3, 4, 5, 6, 3, 4}, {1, 2, 3, 4, 5, 6, 3, 2}, 
    {1, 2, 3, 6, 4, 3, 2, 1}, {1, 2, 3, 4, 5, 6, 3, 4, 2}, {1, 2, 3, 6, 4, 3, 2, 1, 5}, {1, 2, 3, 4, 5, 6, 3, 4, 2, 3}, 
    {1, 2, 3, 6, 4, 3, 2, 1, 5, 4}, {1, 2, 3, 4, 5, 6, 3, 4, 2, 3, 6}, {1, 2, 3, 6, 4, 3, 2, 1, 5, 4, 3}, 
    {1, 2, 3, 4, 5, 6, 3, 4, 2, 3, 6, 1}, {1, 2, 3, 6, 4, 3, 2, 1, 5, 4, 3, 2}, {1, 2, 3, 4, 5, 6, 3, 4, 2, 3, 6, 1, 2}, 
    {1, 2, 3, 4, 5, 6, 3, 4, 2, 3, 6, 1, 2, 3}, {1, 2, 3, 4, 5, 6, 3, 4, 2, 3, 6, 1, 2, 3, 4}, 
    {1, 2, 3, 4, 5, 6, 3, 4, 2, 3, 6, 1, 2, 3, 4, 5}}; 
allRootJunctionsE8 = {{-2, -1, 0, -1, 1, 0, 1, 1, 0, 1}, {-1, -2, 1, 0, 1, 1, 0, 1, -1, 0}, 
    {-1, -1, -1, -1, 1, 0, 1, 1, 0, 1}, {-1, -1, 0, -1, 0, 0, 1, 1, 0, 1}, {-1, -1, 0, -1, 1, 0, 0, 1, 0, 1}, 
    {-1, -1, 0, -1, 1, 0, 1, 1, -1, 1}, {-1, -1, 0, -1, 1, 0, 1, 2, -1, 0}, {-1, -1, 0, -1, 1, 1, 0, 0, 0, 1}, 
    {-1, -1, 0, -1, 1, 1, 0, 1, 0, 0}, {-1, -1, 0, -1, 1, 1, 1, 1, -1, 0}, {-1, -1, 0, -1, 2, 1, 0, 1, -1, 0}, 
    {-1, -1, 0, 0, 0, -1, 1, 1, 0, 1}, {-1, -1, 0, 0, 0, 0, 0, 0, 1, 1}, {-1, -1, 0, 0, 0, 0, 1, 0, 0, 1}, 
    {-1, -1, 0, 0, 0, 0, 1, 1, 0, 0}, {-1, -1, 0, 0, 1, 0, 0, 0, 0, 1}, {-1, -1, 0, 0, 1, 0, 0, 1, 0, 0}, 
    {-1, -1, 0, 0, 1, 0, 1, 1, -1, 0}, {-1, -1, 0, 0, 1, 1, 0, 0, 0, 0}, {-1, -1, 1, -1, 1, 1, 0, 1, -1, 0}, 
    {-1, -1, 1, 0, 0, 0, 0, 0, 0, 1}, {-1, -1, 1, 0, 0, 0, 0, 1, 0, 0}, {-1, -1, 1, 0, 0, 0, 1, 1, -1, 0}, 
    {-1, -1, 1, 0, 0, 1, 0, 0, 0, 0}, {-1, -1, 1, 0, 1, 0, 0, 1, -1, 0}, {-1, -1, 1, 0, 1, 1, -1, 0, 0, 0}, 
    {-1, -1, 1, 0, 1, 1, 0, 0, -1, 0}, {-1, -1, 1, 0, 1, 1, 0, 1, -1, -1}, {-1, -1, 1, 1, 0, 0, 0, 0, 0, 0}, 
    {-1, 0, -1, -2, 1, 0, 1, 1, 0, 1}, {-1, 0, -1, -1, 0, -1, 1, 0, 1, 2}, {-1, 0, -1, -1, 0, -1, 1, 1, 1, 1}, 
    {-1, 0, -1, -1, 0, -1, 2, 1, 0, 1}, {-1, 0, -1, -1, 0, 0, 1, 0, 1, 1}, {-1, 0, -1, -1, 1, -1, 1, 1, 0, 1}, 
    {-1, 0, -1, -1, 1, 0, 0, 0, 1, 1}, {-1, 0, -1, -1, 1, 0, 1, 0, 0, 1}, {-1, 0, -1, -1, 1, 0, 1, 1, 0, 0}, 
    {-1, 0, -1, 0, 0, -1, 1, 0, 1, 1}, {-1, 0, 0, -1, 0, -1, 1, 1, 0, 1}, {-1, 0, 0, -1, 0, 0, 0, 0, 1, 1}, 
    {-1, 0, 0, -1, 0, 0, 1, 0, 0, 1}, {-1, 0, 0, -1, 0, 0, 1, 1, 0, 0}, {-1, 0, 0, -1, 1, 0, 0, 0, 0, 1}, 
    {-1, 0, 0, -1, 1, 0, 0, 1, 0, 0}, {-1, 0, 0, -1, 1, 0, 1, 1, -1, 0}, {-1, 0, 0, -1, 1, 1, 0, 0, 0, 0}, 
    {-1, 0, 0, 0, -1, -1, 1, 0, 1, 1}, {-1, 0, 0, 0, 0, -1, 0, 0, 1, 1}, {-1, 0, 0, 0, 0, -1, 1, 0, 0, 1}, 
    {-1, 0, 0, 0, 0, -1, 1, 1, 0, 0}, {-1, 0, 0, 0, 0, 0, 0, -1, 1, 1}, {-1, 0, 0, 0, 0, 0, 0, 0, 1, 0}, 
    {-1, 0, 0, 0, 0, 0, 1, 0, 0, 0}, {-1, 0, 0, 0, 1, 0, 0, 0, 0, 0}, {-1, 0, 1, 0, 0, 0, 0, 0, 0, 0}, 
    {-1, 1, -1, -1, 0, -1, 1, 0, 1, 1}, {0, -1, 0, -1, 1, 1, 0, 1, -1, 0}, {0, -1, 0, 0, 0, 0, 0, 0, 0, 1}, 
    {0, -1, 0, 0, 0, 0, 0, 1, 0, 0}, {0, -1, 0, 0, 0, 0, 1, 1, -1, 0}, {0, -1, 0, 0, 0, 1, 0, 0, 0, 0}, 
    {0, -1, 0, 0, 1, 0, 0, 1, -1, 0}, {0, -1, 0, 0, 1, 1, -1, 0, 0, 0}, {0, -1, 0, 0, 1, 1, 0, 0, -1, 0}, 
    {0, -1, 0, 0, 1, 1, 0, 1, -1, -1}, {0, -1, 0, 1, 0, 0, 0, 0, 0, 0}, {0, -1, 1, 0, 0, 0, 0, 1, -1, 0}, 
    {0, -1, 1, 0, 0, 1, -1, 0, 0, 0}, {0, -1, 1, 0, 0, 1, 0, 0, -1, 0}, {0, -1, 1, 0, 0, 1, 0, 1, -1, -1}, 
    {0, -1, 1, 0, 1, 1, -1, 0, -1, 0}, {0, -1, 1, 0, 1, 1, -1, 1, -1, -1}, {0, -1, 1, 0, 1, 1, 0, 1, -2, -1}, 
    {0, -1, 1, 0, 1, 2, -1, 0, -1, -1}, {0, -1, 1, 1, -1, 0, 0, 0, 0, 0}, {0, -1, 1, 1, 0, 0, -1, 0, 0, 0}, 
    {0, -1, 1, 1, 0, 0, 0, 0, -1, 0}, {0, -1, 1, 1, 0, 0, 0, 1, -1, -1}, {0, -1, 1, 1, 0, 1, -1, -1, 0, 0}, 
    {0, -1, 1, 1, 0, 1, -1, 0, 0, -1}, {0, -1, 1, 1, 0, 1, 0, 0, -1, -1}, {0, -1, 1, 1, 1, 1, -1, 0, -1, -1}, 
    {0, -1, 2, 1, 0, 1, -1, 0, -1, -1}, {0, 0, -1, -1, 0, -1, 1, 1, 0, 1}, {0, 0, -1, -1, 0, 0, 0, 0, 1, 1}, 
    {0, 0, -1, -1, 0, 0, 1, 0, 0, 1}, {0, 0, -1, -1, 0, 0, 1, 1, 0, 0}, {0, 0, -1, -1, 1, 0, 0, 0, 0, 1}, 
    {0, 0, -1, -1, 1, 0, 0, 1, 0, 0}, {0, 0, -1, -1, 1, 0, 1, 1, -1, 0}, {0, 0, -1, -1, 1, 1, 0, 0, 0, 0}, 
    {0, 0, -1, 0, -1, -1, 1, 0, 1, 1}, {0, 0, -1, 0, 0, -1, 0, 0, 1, 1}, {0, 0, -1, 0, 0, -1, 1, 0, 0, 1}, 
    {0, 0, -1, 0, 0, -1, 1, 1, 0, 0}, {0, 0, -1, 0, 0, 0, 0, -1, 1, 1}, {0, 0, -1, 0, 0, 0, 0, 0, 1, 0}, 
    {0, 0, -1, 0, 0, 0, 1, 0, 0, 0}, {0, 0, -1, 0, 1, 0, 0, 0, 0, 0}, {0, 0, 0, -1, 0, 0, 0, 0, 0, 1}, 
    {0, 0, 0, -1, 0, 0, 0, 1, 0, 0}, {0, 0, 0, -1, 0, 0, 1, 1, -1, 0}, {0, 0, 0, -1, 0, 1, 0, 0, 0, 0}, 
    {0, 0, 0, -1, 1, 0, 0, 1, -1, 0}, {0, 0, 0, -1, 1, 1, -1, 0, 0, 0}, {0, 0, 0, -1, 1, 1, 0, 0, -1, 0}, 
    {0, 0, 0, -1, 1, 1, 0, 1, -1, -1}, {0, 0, 0, 0, -1, -1, 0, 0, 1, 1}, {0, 0, 0, 0, -1, -1, 1, 0, 0, 1}, 
    {0, 0, 0, 0, -1, -1, 1, 1, 0, 0}, {0, 0, 0, 0, -1, 0, 0, -1, 1, 1}, {0, 0, 0, 0, -1, 0, 0, 0, 1, 0}, 
    {0, 0, 0, 0, -1, 0, 1, 0, 0, 0}, {0, 0, 0, 0, 0, -1, 0, 0, 0, 1}, {0, 0, 0, 0, 0, -1, 0, 1, 0, 0}, 
    {0, 0, 0, 0, 0, -1, 1, 1, -1, 0}, {0, 0, 0, 0, 0, 0, -1, -1, 1, 1}, {0, 0, 0, 0, 0, 0, -1, 0, 1, 0}, 
    {0, 0, 0, 0, 0, 0, 0, -1, 0, 1}, {0, 0, 0, 0, 0, 0, 0, 1, 0, -1}, {0, 0, 0, 0, 0, 0, 1, 0, -1, 0}, 
    {0, 0, 0, 0, 0, 0, 1, 1, -1, -1}, {0, 0, 0, 0, 0, 1, -1, -1, 1, 0}, {0, 0, 0, 0, 0, 1, 0, -1, 0, 0}, 
    {0, 0, 0, 0, 0, 1, 0, 0, 0, -1}, {0, 0, 0, 0, 1, 0, -1, 0, 0, 0}, {0, 0, 0, 0, 1, 0, 0, 0, -1, 0}, 
    {0, 0, 0, 0, 1, 0, 0, 1, -1, -1}, {0, 0, 0, 0, 1, 1, -1, -1, 0, 0}, {0, 0, 0, 0, 1, 1, -1, 0, 0, -1}, 
    {0, 0, 0, 0, 1, 1, 0, 0, -1, -1}, {0, 0, 0, 1, -1, -1, 0, -1, 1, 1}, {0, 0, 0, 1, -1, -1, 0, 0, 1, 0}, 
    {0, 0, 0, 1, -1, -1, 1, 0, 0, 0}, {0, 0, 0, 1, -1, 0, 0, -1, 1, 0}, {0, 0, 0, 1, 0, -1, 0, 0, 0, 0}, 
    {0, 0, 0, 1, 0, 0, -1, -1, 1, 0}, {0, 0, 0, 1, 0, 0, 0, -1, 0, 0}, {0, 0, 0, 1, 0, 0, 0, 0, 0, -1}, 
    {0, 0, 1, 0, -1, 0, 0, 0, 0, 0}, {0, 0, 1, 0, 0, 0, -1, 0, 0, 0}, {0, 0, 1, 0, 0, 0, 0, 0, -1, 0}, 
    {0, 0, 1, 0, 0, 0, 0, 1, -1, -1}, {0, 0, 1, 0, 0, 1, -1, -1, 0, 0}, {0, 0, 1, 0, 0, 1, -1, 0, 0, -1}, 
    {0, 0, 1, 0, 0, 1, 0, 0, -1, -1}, {0, 0, 1, 0, 1, 1, -1, 0, -1, -1}, {0, 0, 1, 1, -1, -1, 0, 0, 0, 0}, 
    {0, 0, 1, 1, -1, 0, -1, -1, 1, 0}, {0, 0, 1, 1, -1, 0, 0, -1, 0, 0}, {0, 0, 1, 1, -1, 0, 0, 0, 0, -1}, 
    {0, 0, 1, 1, 0, 0, -1, -1, 0, 0}, {0, 0, 1, 1, 0, 0, -1, 0, 0, -1}, {0, 0, 1, 1, 0, 0, 0, 0, -1, -1}, 
    {0, 0, 1, 1, 0, 1, -1, -1, 0, -1}, {0, 1, -2, -1, 0, -1, 1, 0, 1, 1}, {0, 1, -1, -1, -1, -1, 1, 0, 1, 1}, 
    {0, 1, -1, -1, 0, -1, 0, 0, 1, 1}, {0, 1, -1, -1, 0, -1, 1, 0, 0, 1}, {0, 1, -1, -1, 0, -1, 1, 1, 0, 0}, 
    {0, 1, -1, -1, 0, 0, 0, -1, 1, 1}, {0, 1, -1, -1, 0, 0, 0, 0, 1, 0}, {0, 1, -1, -1, 0, 0, 1, 0, 0, 0}, 
    {0, 1, -1, -1, 1, 0, 0, 0, 0, 0}, {0, 1, -1, 0, -1, -2, 1, 0, 1, 1}, {0, 1, -1, 0, -1, -1, 0, -1, 2, 1}, 
    {0, 1, -1, 0, -1, -1, 1, -1, 1, 1}, {0, 1, -1, 0, -1, -1, 1, 0, 1, 0}, {0, 1, -1, 0, 0, -1, 0, -1, 1, 1}, 
    {0, 1, -1, 0, 0, -1, 0, 0, 1, 0}, {0, 1, -1, 0, 0, -1, 1, 0, 0, 0}, {0, 1, -1, 0, 0, 0, 0, -1, 1, 0}, 
    {0, 1, 0, -1, 0, 0, 0, 0, 0, 0}, {0, 1, 0, 0, -1, -1, 0, -1, 1, 1}, {0, 1, 0, 0, -1, -1, 0, 0, 1, 0}, 
    {0, 1, 0, 0, -1, -1, 1, 0, 0, 0}, {0, 1, 0, 0, -1, 0, 0, -1, 1, 0}, {0, 1, 0, 0, 0, -1, 0, 0, 0, 0}, 
    {0, 1, 0, 0, 0, 0, -1, -1, 1, 0}, {0, 1, 0, 0, 0, 0, 0, -1, 0, 0}, {0, 1, 0, 0, 0, 0, 0, 0, 0, -1}, 
    {0, 1, 0, 1, -1, -1, 0, -1, 1, 0}, {1, -1, 1, 1, 0, 1, -1, 0, -1, -1}, {1, 0, -1, 0, 0, 0, 0, 0, 0, 0}, 
    {1, 0, 0, 0, -1, 0, 0, 0, 0, 0}, {1, 0, 0, 0, 0, 0, -1, 0, 0, 0}, {1, 0, 0, 0, 0, 0, 0, 0, -1, 0}, 
    {1, 0, 0, 0, 0, 0, 0, 1, -1, -1}, {1, 0, 0, 0, 0, 1, -1, -1, 0, 0}, {1, 0, 0, 0, 0, 1, -1, 0, 0, -1}, 
    {1, 0, 0, 0, 0, 1, 0, 0, -1, -1}, {1, 0, 0, 0, 1, 1, -1, 0, -1, -1}, {1, 0, 0, 1, -1, -1, 0, 0, 0, 0}, 
    {1, 0, 0, 1, -1, 0, -1, -1, 1, 0}, {1, 0, 0, 1, -1, 0, 0, -1, 0, 0}, {1, 0, 0, 1, -1, 0, 0, 0, 0, -1}, 
    {1, 0, 0, 1, 0, 0, -1, -1, 0, 0}, {1, 0, 0, 1, 0, 0, -1, 0, 0, -1}, {1, 0, 0, 1, 0, 0, 0, 0, -1, -1}, 
    {1, 0, 0, 1, 0, 1, -1, -1, 0, -1}, {1, 0, 1, 0, 0, 1, -1, 0, -1, -1}, {1, 0, 1, 1, -1, 0, -1, -1, 0, 0}, 
    {1, 0, 1, 1, -1, 0, -1, 0, 0, -1}, {1, 0, 1, 1, -1, 0, 0, 0, -1, -1}, {1, 0, 1, 1, -1, 1, -1, -1, 0, -1}, 
    {1, 0, 1, 1, 0, 0, -1, 0, -1, -1}, {1, 0, 1, 1, 0, 1, -2, -1, 0, -1}, {1, 0, 1, 1, 0, 1, -1, -1, -1, -1}, 
    {1, 0, 1, 1, 0, 1, -1, 0, -1, -2}, {1, 0, 1, 2, -1, 0, -1, -1, 0, -1}, {1, 1, -1, -1, 0, 0, 0, 0, 0, 0}, 
    {1, 1, -1, 0, -1, -1, 0, -1, 1, 1}, {1, 1, -1, 0, -1, -1, 0, 0, 1, 0}, {1, 1, -1, 0, -1, -1, 1, 0, 0, 0}, 
    {1, 1, -1, 0, -1, 0, 0, -1, 1, 0}, {1, 1, -1, 0, 0, -1, 0, 0, 0, 0}, {1, 1, -1, 0, 0, 0, -1, -1, 1, 0}, 
    {1, 1, -1, 0, 0, 0, 0, -1, 0, 0}, {1, 1, -1, 0, 0, 0, 0, 0, 0, -1}, {1, 1, -1, 1, -1, -1, 0, -1, 1, 0}, 
    {1, 1, 0, 0, -1, -1, 0, 0, 0, 0}, {1, 1, 0, 0, -1, 0, -1, -1, 1, 0}, {1, 1, 0, 0, -1, 0, 0, -1, 0, 0}, 
    {1, 1, 0, 0, -1, 0, 0, 0, 0, -1}, {1, 1, 0, 0, 0, 0, -1, -1, 0, 0}, {1, 1, 0, 0, 0, 0, -1, 0, 0, -1}, 
    {1, 1, 0, 0, 0, 0, 0, 0, -1, -1}, {1, 1, 0, 0, 0, 1, -1, -1, 0, -1}, {1, 1, 0, 1, -2, -1, 0, -1, 1, 0}, 
    {1, 1, 0, 1, -1, -1, -1, -1, 1, 0}, {1, 1, 0, 1, -1, -1, 0, -1, 0, 0}, {1, 1, 0, 1, -1, -1, 0, 0, 0, -1}, 
    {1, 1, 0, 1, -1, 0, -1, -2, 1, 0}, {1, 1, 0, 1, -1, 0, -1, -1, 1, -1}, {1, 1, 0, 1, -1, 0, 0, -1, 0, -1}, 
    {1, 1, 0, 1, 0, 0, -1, -1, 0, -1}, {1, 1, 1, 1, -1, 0, -1, -1, 0, -1}, {1, 2, -1, 0, -1, -1, 0, -1, 1, 0}, 
    {2, 1, 0, 1, -1, 0, -1, -1, 0, -1}}; 
allRootJunctionsE8Basis2 = {{-2, 1, 0, 1, 1, 0, 1, -1, 0, -1}, {-1, -1, -1, 1, 0, 1, 1, 0, 1, -1}, 
    {-1, 0, -1, 0, 0, 1, 1, 0, 1, -1}, {-1, 0, -1, 1, 0, 0, 1, 0, 1, -1}, {-1, 0, -1, 1, 0, 1, 1, -1, 1, -1}, 
    {-1, 0, -1, 1, 0, 1, 1, 0, 1, -2}, {-1, 0, -1, 1, 0, 1, 2, -1, 0, -1}, {-1, 0, -1, 1, 1, 0, 0, 0, 1, -1}, 
    {-1, 0, -1, 1, 1, 0, 1, -1, 0, 0}, {-1, 0, -1, 1, 1, 0, 1, 0, 0, -1}, {-1, 0, -1, 1, 1, 1, 1, -1, 0, -1}, 
    {-1, 0, -1, 2, 1, 0, 1, -1, 0, -1}, {-1, 0, 0, 0, -1, 1, 1, 0, 1, -1}, {-1, 0, 0, 0, 0, 0, 0, 0, 1, 0}, 
    {-1, 0, 0, 0, 0, 0, 0, 1, 1, -1}, {-1, 0, 0, 0, 0, 0, 1, 0, 0, 0}, {-1, 0, 0, 0, 0, 1, 0, 0, 1, -1}, 
    {-1, 0, 0, 0, 0, 1, 1, -1, 0, 0}, {-1, 0, 0, 0, 0, 1, 1, 0, 0, -1}, {-1, 0, 0, 0, 1, 0, 0, 0, 0, 0}, 
    {-1, 0, 0, 1, 0, 0, 0, 0, 1, -1}, {-1, 0, 0, 1, 0, 0, 1, -1, 0, 0}, {-1, 0, 0, 1, 0, 0, 1, 0, 0, -1}, 
    {-1, 0, 0, 1, 0, 1, 1, -1, 0, -1}, {-1, 0, 0, 1, 1, -1, 0, 0, 0, 0}, {-1, 0, 0, 1, 1, 0, 0, -1, 0, 0}, 
    {-1, 0, 0, 1, 1, 0, 0, 0, 0, -1}, {-1, 0, 0, 1, 1, 0, 1, -1, -1, 0}, {-1, 0, 1, 0, 0, 0, 0, 0, 0, 0}, 
    {-1, 1, -1, 1, 1, 0, 1, -1, 0, -1}, {-1, 1, 0, 0, 0, 0, 0, 0, 1, -1}, {-1, 1, 0, 0, 0, 0, 1, -1, 0, 0}, 
    {-1, 1, 0, 0, 0, 0, 1, 0, 0, -1}, {-1, 1, 0, 0, 0, 1, 1, -1, 0, -1}, {-1, 1, 0, 0, 1, -1, 0, 0, 0, 0}, 
    {-1, 1, 0, 0, 1, 0, 0, -1, 0, 0}, {-1, 1, 0, 0, 1, 0, 0, 0, 0, -1}, {-1, 1, 0, 0, 1, 0, 1, -1, -1, 0}, 
    {-1, 1, 0, 1, 0, 0, 1, -1, 0, -1}, {-1, 1, 0, 1, 1, -1, 0, -1, 0, 0}, {-1, 1, 0, 1, 1, -1, 0, 0, 0, -1}, 
    {-1, 1, 0, 1, 1, -1, 1, -1, -1, 0}, {-1, 1, 0, 1, 1, 0, 0, -1, 0, -1}, {-1, 1, 0, 1, 1, 0, 1, -2, -1, 0}, 
    {-1, 1, 0, 1, 1, 0, 1, -1, -1, -1}, {-1, 1, 0, 1, 2, -1, 0, -1, -1, 0}, {-1, 1, 1, -1, 0, 0, 0, 0, 0, 0}, 
    {-1, 1, 1, 0, 0, -1, 0, 0, 0, 0}, {-1, 1, 1, 0, 0, 0, 0, -1, 0, 0}, {-1, 1, 1, 0, 0, 0, 0, 0, 0, -1}, 
    {-1, 1, 1, 0, 0, 0, 1, -1, -1, 0}, {-1, 1, 1, 0, 1, -1, -1, 0, 0, 0}, {-1, 1, 1, 0, 1, -1, 0, -1, -1, 1}, 
    {-1, 1, 1, 0, 1, -1, 0, 0, -1, 0}, {-1, 1, 1, 0, 1, 0, 0, -1, -1, 0}, {-1, 1, 1, 1, 1, -1, 0, -1, -1, 0}, 
    {-1, 2, 1, 0, 1, -1, 0, -1, -1, 0}, {0, -1, -2, 1, 0, 1, 1, 0, 1, -1}, {0, -1, -1, 0, -1, 1, 0, 1, 2, -1}, 
    {0, -1, -1, 0, -1, 1, 1, 0, 1, 0}, {0, -1, -1, 0, -1, 1, 1, 1, 1, -1}, {0, -1, -1, 0, -1, 2, 1, 0, 1, -1}, 
    {0, -1, -1, 0, 0, 0, 0, 1, 1, 0}, {0, -1, -1, 0, 0, 1, 0, 0, 1, 0}, {0, -1, -1, 0, 0, 1, 0, 1, 1, -1}, 
    {0, -1, -1, 0, 0, 1, 1, 0, 0, 0}, {0, -1, -1, 1, -1, 1, 1, 0, 1, -1}, {0, -1, -1, 1, 0, 0, 0, 0, 1, 0}, 
    {0, -1, -1, 1, 0, 0, 0, 1, 1, -1}, {0, -1, -1, 1, 0, 0, 1, 0, 0, 0}, {0, -1, -1, 1, 0, 1, 0, 0, 1, -1}, 
    {0, -1, -1, 1, 0, 1, 1, -1, 0, 0}, {0, -1, -1, 1, 0, 1, 1, 0, 0, -1}, {0, -1, -1, 1, 1, 0, 0, 0, 0, 0}, 
    {0, -1, 0, -1, -1, 1, 0, 1, 1, 0}, {0, -1, 0, 0, -1, 0, 0, 1, 1, 0}, {0, -1, 0, 0, -1, 1, 0, 0, 1, 0}, 
    {0, -1, 0, 0, -1, 1, 0, 1, 1, -1}, {0, -1, 0, 0, -1, 1, 1, 0, 0, 0}, {0, -1, 0, 0, 0, 0, -1, 1, 1, 0}, 
    {0, -1, 0, 0, 0, 0, 0, 0, 0, 1}, {0, -1, 0, 0, 0, 0, 0, 1, 0, 0}, {0, -1, 0, 0, 0, 1, 0, 0, 0, 0}, 
    {0, -1, 0, 1, 0, 0, 0, 0, 0, 0}, {0, 0, -1, 0, -1, 1, 1, 0, 1, -1}, {0, 0, -1, 0, 0, 0, 0, 0, 1, 0}, 
    {0, 0, -1, 0, 0, 0, 0, 1, 1, -1}, {0, 0, -1, 0, 0, 0, 1, 0, 0, 0}, {0, 0, -1, 0, 0, 1, 0, 0, 1, -1}, 
    {0, 0, -1, 0, 0, 1, 1, -1, 0, 0}, {0, 0, -1, 0, 0, 1, 1, 0, 0, -1}, {0, 0, -1, 0, 1, 0, 0, 0, 0, 0}, 
    {0, 0, -1, 1, 0, 0, 0, 0, 1, -1}, {0, 0, -1, 1, 0, 0, 1, -1, 0, 0}, {0, 0, -1, 1, 0, 0, 1, 0, 0, -1}, 
    {0, 0, -1, 1, 0, 1, 1, -1, 0, -1}, {0, 0, -1, 1, 1, -1, 0, 0, 0, 0}, {0, 0, -1, 1, 1, 0, 0, -1, 0, 0}, 
    {0, 0, -1, 1, 1, 0, 0, 0, 0, -1}, {0, 0, -1, 1, 1, 0, 1, -1, -1, 0}, {0, 0, 0, -1, -1, 0, 0, 1, 1, 0}, 
    {0, 0, 0, -1, -1, 1, 0, 0, 1, 0}, {0, 0, 0, -1, -1, 1, 0, 1, 1, -1}, {0, 0, 0, -1, -1, 1, 1, 0, 0, 0}, 
    {0, 0, 0, -1, 0, 0, -1, 1, 1, 0}, {0, 0, 0, -1, 0, 0, 0, 0, 0, 1}, {0, 0, 0, -1, 0, 0, 0, 1, 0, 0}, 
    {0, 0, 0, -1, 0, 1, 0, 0, 0, 0}, {0, 0, 0, 0, -1, 0, 0, 0, 1, 0}, {0, 0, 0, 0, -1, 0, 0, 1, 1, -1}, 
    {0, 0, 0, 0, -1, 0, 1, 0, 0, 0}, {0, 0, 0, 0, -1, 1, 0, 0, 1, -1}, {0, 0, 0, 0, -1, 1, 1, -1, 0, 0}, 
    {0, 0, 0, 0, -1, 1, 1, 0, 0, -1}, {0, 0, 0, 0, 0, -1, -1, 1, 1, 0}, {0, 0, 0, 0, 0, -1, 0, 0, 0, 1}, 
    {0, 0, 0, 0, 0, -1, 0, 1, 0, 0}, {0, 0, 0, 0, 0, 0, -1, 0, 1, 0}, {0, 0, 0, 0, 0, 0, -1, 1, 1, -1}, 
    {0, 0, 0, 0, 0, 0, 0, -1, 0, 1}, {0, 0, 0, 0, 0, 0, 0, 1, 0, -1}, {0, 0, 0, 0, 0, 0, 1, -1, -1, 1}, 
    {0, 0, 0, 0, 0, 0, 1, 0, -1, 0}, {0, 0, 0, 0, 0, 1, 0, -1, 0, 0}, {0, 0, 0, 0, 0, 1, 0, 0, 0, -1}, 
    {0, 0, 0, 0, 0, 1, 1, -1, -1, 0}, {0, 0, 0, 0, 1, -1, -1, 0, 0, 1}, {0, 0, 0, 0, 1, -1, -1, 1, 0, 0}, 
    {0, 0, 0, 0, 1, -1, 0, 0, -1, 1}, {0, 0, 0, 0, 1, 0, -1, 0, 0, 0}, {0, 0, 0, 0, 1, 0, 0, -1, -1, 1}, 
    {0, 0, 0, 0, 1, 0, 0, 0, -1, 0}, {0, 0, 0, 1, 0, -1, 0, 0, 0, 0}, {0, 0, 0, 1, 0, 0, 0, -1, 0, 0}, 
    {0, 0, 0, 1, 0, 0, 0, 0, 0, -1}, {0, 0, 0, 1, 0, 0, 1, -1, -1, 0}, {0, 0, 0, 1, 1, -1, -1, 0, 0, 0}, 
    {0, 0, 0, 1, 1, -1, 0, -1, -1, 1}, {0, 0, 0, 1, 1, -1, 0, 0, -1, 0}, {0, 0, 0, 1, 1, 0, 0, -1, -1, 0}, 
    {0, 0, 1, -1, -1, 0, -1, 1, 1, 0}, {0, 0, 1, -1, -1, 0, 0, 0, 0, 1}, {0, 0, 1, -1, -1, 0, 0, 1, 0, 0}, 
    {0, 0, 1, -1, -1, 1, 0, 0, 0, 0}, {0, 0, 1, -1, 0, -1, -1, 1, 0, 1}, {0, 0, 1, -1, 0, 0, -1, 0, 0, 1}, 
    {0, 0, 1, -1, 0, 0, -1, 1, 0, 0}, {0, 0, 1, -1, 0, 0, 0, 0, -1, 1}, {0, 0, 1, 0, -1, 0, 0, 0, 0, 0}, 
    {0, 0, 1, 0, 0, -1, -1, 0, 0, 1}, {0, 0, 1, 0, 0, -1, -1, 1, 0, 0}, {0, 0, 1, 0, 0, -1, 0, 0, -1, 1}, 
    {0, 0, 1, 0, 0, 0, -1, 0, 0, 0}, {0, 0, 1, 0, 0, 0, 0, -1, -1, 1}, {0, 0, 1, 0, 0, 0, 0, 0, -1, 0}, 
    {0, 0, 1, 0, 1, -1, -1, 0, -1, 1}, {0, 1, 0, -1, 0, 0, 0, 0, 0, 0}, {0, 1, 0, 0, 0, -1, 0, 0, 0, 0}, 
    {0, 1, 0, 0, 0, 0, 0, -1, 0, 0}, {0, 1, 0, 0, 0, 0, 0, 0, 0, -1}, {0, 1, 0, 0, 0, 0, 1, -1, -1, 0}, 
    {0, 1, 0, 0, 1, -1, -1, 0, 0, 0}, {0, 1, 0, 0, 1, -1, 0, -1, -1, 1}, {0, 1, 0, 0, 1, -1, 0, 0, -1, 0}, 
    {0, 1, 0, 0, 1, 0, 0, -1, -1, 0}, {0, 1, 0, 1, 1, -1, 0, -1, -1, 0}, {0, 1, 1, -1, -1, 0, 0, 0, 0, 0}, 
    {0, 1, 1, -1, 0, -1, -1, 0, 0, 1}, {0, 1, 1, -1, 0, -1, -1, 1, 0, 0}, {0, 1, 1, -1, 0, -1, 0, 0, -1, 1}, 
    {0, 1, 1, -1, 0, 0, -1, 0, 0, 0}, {0, 1, 1, -1, 0, 0, 0, -1, -1, 1}, {0, 1, 1, -1, 0, 0, 0, 0, -1, 0}, 
    {0, 1, 1, -1, 1, -1, -1, 0, -1, 1}, {0, 1, 1, 0, 0, -1, -1, 0, 0, 0}, {0, 1, 1, 0, 0, -1, 0, -1, -1, 1}, 
    {0, 1, 1, 0, 0, -1, 0, 0, -1, 0}, {0, 1, 1, 0, 0, 0, 0, -1, -1, 0}, {0, 1, 1, 0, 1, -2, -1, 0, -1, 1}, 
    {0, 1, 1, 0, 1, -1, -1, -1, -1, 1}, {0, 1, 1, 0, 1, -1, -1, 0, -1, 0}, {0, 1, 1, 0, 1, -1, 0, -1, -2, 1}, 
    {0, 1, 2, -1, 0, -1, -1, 0, -1, 1}, {1, -2, -1, 0, -1, 1, 0, 1, 1, 0}, {1, -1, -1, -1, -1, 1, 0, 1, 1, 0}, 
    {1, -1, -1, 0, -1, 0, 0, 1, 1, 0}, {1, -1, -1, 0, -1, 1, 0, 0, 1, 0}, {1, -1, -1, 0, -1, 1, 0, 1, 1, -1}, 
    {1, -1, -1, 0, -1, 1, 1, 0, 0, 0}, {1, -1, -1, 0, 0, 0, -1, 1, 1, 0}, {1, -1, -1, 0, 0, 0, 0, 0, 0, 1}, 
    {1, -1, -1, 0, 0, 0, 0, 1, 0, 0}, {1, -1, -1, 0, 0, 1, 0, 0, 0, 0}, {1, -1, -1, 1, 0, 0, 0, 0, 0, 0}, 
    {1, -1, 0, -1, -2, 1, 0, 1, 1, 0}, {1, -1, 0, -1, -1, 0, -1, 1, 1, 1}, {1, -1, 0, -1, -1, 0, -1, 2, 1, 0}, 
    {1, -1, 0, -1, -1, 0, 0, 1, 0, 1}, {1, -1, 0, -1, -1, 1, -1, 1, 1, 0}, {1, -1, 0, -1, -1, 1, 0, 0, 0, 1}, 
    {1, -1, 0, -1, -1, 1, 0, 1, 0, 0}, {1, -1, 0, -1, 0, 0, -1, 1, 0, 1}, {1, -1, 0, 0, -1, 0, -1, 1, 1, 0}, 
    {1, -1, 0, 0, -1, 0, 0, 0, 0, 1}, {1, -1, 0, 0, -1, 0, 0, 1, 0, 0}, {1, -1, 0, 0, -1, 1, 0, 0, 0, 0}, 
    {1, -1, 0, 0, 0, -1, -1, 1, 0, 1}, {1, -1, 0, 0, 0, 0, -1, 0, 0, 1}, {1, -1, 0, 0, 0, 0, -1, 1, 0, 0}, 
    {1, -1, 0, 0, 0, 0, 0, 0, -1, 1}, {1, -1, 1, -1, -1, 0, -1, 1, 0, 1}, {1, 0, -1, 0, 0, 0, 0, 0, 0, 0}, 
    {1, 0, 0, -1, -1, 0, -1, 1, 1, 0}, {1, 0, 0, -1, -1, 0, 0, 0, 0, 1}, {1, 0, 0, -1, -1, 0, 0, 1, 0, 0}, 
    {1, 0, 0, -1, -1, 1, 0, 0, 0, 0}, {1, 0, 0, -1, 0, -1, -1, 1, 0, 1}, {1, 0, 0, -1, 0, 0, -1, 0, 0, 1}, 
    {1, 0, 0, -1, 0, 0, -1, 1, 0, 0}, {1, 0, 0, -1, 0, 0, 0, 0, -1, 1}, {1, 0, 0, 0, -1, 0, 0, 0, 0, 0}, 
    {1, 0, 0, 0, 0, -1, -1, 0, 0, 1}, {1, 0, 0, 0, 0, -1, -1, 1, 0, 0}, {1, 0, 0, 0, 0, -1, 0, 0, -1, 1}, 
    {1, 0, 0, 0, 0, 0, -1, 0, 0, 0}, {1, 0, 0, 0, 0, 0, 0, -1, -1, 1}, {1, 0, 0, 0, 0, 0, 0, 0, -1, 0}, 
    {1, 0, 0, 0, 1, -1, -1, 0, -1, 1}, {1, 0, 1, -2, -1, 0, -1, 1, 0, 1}, {1, 0, 1, -1, -1, -1, -1, 1, 0, 1}, 
    {1, 0, 1, -1, -1, 0, -1, 0, 0, 1}, {1, 0, 1, -1, -1, 0, -1, 1, 0, 0}, {1, 0, 1, -1, -1, 0, 0, 0, -1, 1}, 
    {1, 0, 1, -1, 0, -1, -2, 1, 0, 1}, {1, 0, 1, -1, 0, -1, -1, 0, -1, 2}, {1, 0, 1, -1, 0, -1, -1, 1, -1, 1}, 
    {1, 0, 1, -1, 0, 0, -1, 0, -1, 1}, {1, 0, 1, 0, 0, -1, -1, 0, -1, 1}, {1, 1, 1, -1, 0, -1, -1, 0, -1, 1}, 
    {2, -1, 0, -1, -1, 0, -1, 1, 0, 1}}; 


(* ::Subsection:: *)
(*Group Theory related functions*)


getPositiveRoots::usage=
"getPositiveRoots[roots_]:
This function computes a set of positive roots, given a set of roots.
Arguments:
	*) roots_: A set of roots of a Lie algebra
Returns:
	A set of positive roots. We pick a Weyl chamber in which a root is positive if its first non-zero entry is positive
"
getPositiveRoots[roots_]:=Module[{i,j,posRoots},( 
posRoots={};
For[i=1,i<=Length[roots],i++,
For[j=1,j<=Length[roots[[i]]],j++,
If[roots[[i,j]]==0,Continue[]];
If[roots[[i,j]]<0,Break[]];
If[roots[[i,j]]>0,AppendTo[posRoots,roots[[i]]];
Break[]];
];
];
Return[posRoots];
)];

getSimpleRootsFromPosRoots::usage=
"getSimpleRootsFromPosRoots[posRoots_]:
This function computes a set of simple roots, given a set of positive roots.
Arguments:
	*) posRoots_: A set of positive roots of a Lie algebra, using the convention that a root is positive if its first non-zero entry is positive
Returns:
	A set of simple roots.
"
getSimpleRootsFromPosRoots[posRoots_]:=Module[{i,j,k,isNotSimple,coeffeqn,tmpEqn,tmpeqres,simpleRoots},( 
simpleRoots={};
(*Check whether each root can be written as a sum of two other roots. This is much faster*)
For[i=1,i<=Length[posRoots],i++,
isNotSimple=False;
For[j=1,j<=Length[posRoots],j++,
For[k=1,k<=Length[posRoots],k++,
If[posRoots[[i]]==posRoots[[j]]+posRoots[[k]],isNotSimple=True;];
];
];
If[!isNotSimple,AppendTo[simpleRoots,posRoots[[i]]]]
];
Return[simpleRoots];
)];

getCartanMatrix::usage=
"getCartanMatrix[SRT_,intMat_]:
This function computes the Cartan matrix with respect to an intersection matrix for inner products of roots.
Arguments:
	*) SRT_: A set of simple roots
	*) intMat_: A Length(SRT) x Length(SRT) matrix with respect to which the inner product of roots is computed. If omitted, the identity matrix is used.
Returns:
	The Cartan matrix of the Lie Algebra associated with the simple root set.
"
getCartanMatrix[SRT_,intMat_]:= Return[Table[2 SRT[[i]].intMat.SRT[[j]]/SRT[[i]].intMat.SRT[[i]],{i,Length[SRT]},{j,Length[SRT]}]];
getCartanMatrix[SRT_]:= Return[getCartanMatrix[SRT,IdentityMatrix[Length[SRT]]]];

getDynkLbl::usage=
"getDynkLbl[SRT_,irrep_,intMat_]:
This function computes the Dynkin labels for a given weight or root.
Arguments:
	*) SRT_: A set of simple roots
	*) irrep: A weight of an irreducible representation for which the Dynkin labels shall be computed
	*) intMat_: A Length(SRT[[i]]) x Length(SRT[[i]]) matrix with respect to which the inner product of roots is computed
Returns:
	The Dynkin labels associated with the weight vector irrep_.
"
getDynkLbl[SRT_,irrep_,intMat_]:=Return[Table[SRT[[i]].intMat.irrep,{i,Length[SRT]}]];

getReflectionM::usage=
"getReflectionM[v_]:
This function computes the reflection matrix with respect to the vector v_.
Arguments:
	*) v_: The vector specifying the plane of relection
Returns:
	The matrix associated with a reflection along a plane prependicular to v_.
"
getReflectionM[v_]:=Return[Table[KroneckerDelta[i,j] -v[[i]] v[[j]],{i,Length[v]},{j,Length[v]}]];

checkTrafoInWG::usage=
"checkTrafoInWG[SRTs_,trafoM_,WG_]:
This function computes whether a transformation of simple roots is a  Weyl group element (inner automorphism) or not (outer automorphism) 
Arguments:
	*) SRTs_: A set of simple roots
	*) trafoM: a Length(SRT[[i]]) x Length(SRT[[i]]) that specifies an automorphism in simple root space
	*) WG: A list of Weyl group elements
Returns:
	If a Weyl group element in WG_ induces the transformation of trafoM_ directly or modulo permutations, it returns this Weyl group element. Otherwise it returns an empty set (this means that trafoM_ induced neither inner nor outer automrophisms).
"
checkTrafoInWG[SRTs_,trafoM_,WG_]:=Module[{i,SRTsTransformed,SRTsTry,foundOuter},( 
SRTsTransformed=trafoM.Table[SRTs[[i]],{i,Length[SRTs]}];
foundOuter=False;
For[i=1,i<=Length[WG],i++,
SRTsTry=Table[WG[[i]].SRTs[[j]],{j,Length[SRTs]}];
If[SRTsTry==SRTsTransformed,Print["Found Weyl group element at position ",i,". Automorphism is ",Style["inner.",Green]];Return[WG[[i]]];,
If[compareSets[SRTsTry,SRTsTransformed],
foundOuter=True;Print["Found Weyl group element at position ",i," that maps simple roots up to permutations. Automorphism is ",Style["outer.",Orange]];
Return[WG[[i]]];
];
];
];
Print[Style["No Weyl group element induces the specified action. Automorphism is outer, but no inner automorphism that is an automorphism modulo outer automorphism was found, which is strange...",Red]];
Return[{{}}];
)];

getWeylGroupA::usage=
"getWeylGroupA[n_]:
Computes the Weyl group for SU(N). These are the permutation matrices if the simple roots are in the orthogonal root basis. Order is n!
Arguments:
	*) n_: The rank of the SU(N) Lie algebra for which the Weyl group shall be computed
Returns:
	All elements of the Weyl group of SU(N), i.e. n! permutation matrices.
"
getWeylGroupA[n_]:=Module[{lines,indices},( 
lines=Permutations[PadRight[{1},n+1]];
indices=Permutations[Table[i,{i,n+1}]];
Return[Table[lines[[indices[[i,j]]]],{i,Length[indices]},{j,Length[indices[[i]]]}]];
)];

getWeylGroupD::usage=
"getWeylGroupD[n_]:
Computes the Weyl group for SO(2N). These are the permutation matrices  plus even sign flips if the simple roots are in the orthogonal root basis. Order is n! 2^(n-1)
Arguments:
	*) n_: The rank of the SO(N) Lie algebra for which the Weyl group shall be computed
Returns:
	All elements of the Weyl group of SO(2N).
"
getWeylGroupD[n_]:=Module[{diagonals,diagonal,signCombis,signFlipMatrices,AnWG,i,j},( 
diagonals={};
For[i=0,i<=n,i=i+2,
diagonal={};
For[j=1,j<=i,j++,AppendTo[diagonal,-1]];
For[j=Length[diagonal]+1,j<=n,j++,AppendTo[diagonal,1]];
AppendTo[diagonals,diagonal];
];
signCombis=Join@@Table[Permutations[diagonals[[i]]],{i,Length[diagonals]}];
signFlipMatrices=Table[DiagonalMatrix[signCombis[[i]]],{i,Length[signCombis]}];
AnWG=getWeylGroupA[n-1];
Return[Flatten[Table[AnWG[[i]].signFlipMatrices[[j]],{i,Length[AnWG]},{j,Length[signFlipMatrices]}],1]];
)];

getWeylGroupE::usage=
"getWeylGroupE[n_]:
Computes the Weyl group for \!\(\*SubscriptBox[\(E\), \(n\)]\). \!\(\*SubscriptBox[\(E\), \(7\)]\) is the one of \!\(\*SubscriptBox[\(D\), \(5\)]\) with the 27 added, \!\(\*SubscriptBox[\(E\), \(7\)]\) that of \!\(\*SubscriptBox[\(E\), \(6\)]\) with the 56 added and \!\(\*SubscriptBox[\(E\), \(8\)]\) that of \!\(\*SubscriptBox[\(E\), \(7\)]\) with the 240 added. Since this takes a while (1 minute as of 2016), the function writes the result to \"WGEn.txt\" in the notebook directory. If it finds such a file it reads it instead of computing from scratch. Note: Since all automorphisms are inner for \!\(\*SubscriptBox[\(E\), \(7\)]\) and \!\(\*SubscriptBox[\(E\), \(8\)]\) we have not implemented the Weyl group computation for these. But implementation generalizes straightforwardly as explained above.
Arguments:
	*) n_: The rank of the \!\(\*SubscriptBox[\(E\), \(n\)]\) Lie algebra for which the Weyl group shall be computed
Returns:
	All elements of the Weyl group of \!\(\*SubscriptBox[\(E\), \(n\)]\).
"
getWeylGroupE[n_]:=Module[{hnd,D5WG,padD5,newElem,SRTE6,substM,newActs,curr,i,j,WGE6,s},( 
If[n==6,
If[FileExistsQ[NotebookDirectory[]<>"WGE6.txt"],
Print["Found file ",NotebookDirectory[],"WGE6.txt. Using its content. To force a new computation delete this file."];
hnd=OpenRead[NotebookDirectory[]<>"WGE6.txt"];
WGE6=Read[hnd];
Close[hnd];
Return[WGE6];
];
Print["File ",NotebookDirectory[],"WGE6.txt not found. Computing Weyl group from scratch. This can take a while (around 1 minute on normal desktop in 2016)."];
D5WG=getWeylGroupD[5];
padD5={};
For[i=1,i<=Length[D5WG],i++,
newElem=Table[PadRight[D5WG[[i,j]],8],{j,Length[D5WG[[i]]]}];
AppendTo[newElem,{0,0,0,0,0,1,0,0}];
AppendTo[newElem,{0,0,0,0,0,0,1,0}];
AppendTo[newElem,{0,0,0,0,0,0,0,1}];
AppendTo[padD5,newElem];
];
(*Simple roots of Subscript[E, 6], sorry for hard-coding this...*)
SRTE6={{1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,1/2},{-1,1,0,0,0,0,0,0},{0,-1,1,0,0,0,0,0},{0,0,-1,1,0,0,0,0},{0,0,0,-1,1,0,0,0},{1,1,0,0,0,0,0,0}};
(* get fundamental reflections *)
substM=Table[s[i]->getReflectionM[SRTE6[[i]]],{i,6}];
newActs={IdentityMatrix[8]};
For[i=1,i<=Length[hw27],i++,
curr=IdentityMatrix[8];
For[j=1,j<=Length[hw27[[i]]],j++,
curr=curr.(s[hw27[[i,j]]]/.substM);
];
AppendTo[newActs,curr];
];
WGE6={};
For[i=1,i<=Length[newActs],i++,
For[j=1,j<=Length[padD5],j++,
AppendTo[WGE6,padD5[[j]].newActs[[i]]]
];
];
Print["Writing Weyl group of E6 to file ",NotebookDirectory[]<>"WGE6.txt."];
hnd=OpenWrite[NotebookDirectory[]<>"WGE6.txt"];
Write[hnd,WGE6];
Close[hnd];
Return[WGE6];
];
If[n==7,
Print["Not implemented for \!\(\*SubscriptBox[\(E\), \(7\)]\). In principle this works exactly the same as for \!\(\*SubscriptBox[\(E\), \(6\)]\), but is somewhat slow. Also \!\(\*SubscriptBox[\(E\), \(7\)]\) does not have outer automorphisms, so if it is an automorphism, it is automatically inner."];
Return[{{}}];
];
If[n==8,
Print["Not implemented for \!\(\*SubscriptBox[\(E\), \(8\)]\). In principle this works exactly the same as for \!\(\*SubscriptBox[\(E\), \(6\)]\), but is somewhat slow. Also \!\(\*SubscriptBox[\(E\), \(8\)]\) does not have outer automorphisms, so if it is an automorphism, it is automatically inner."];
Return[{{}}];
];
If[i!=6&&i!=7&&i!=8,Print[Style["Not an \!\(\*SubscriptBox[\(E\), \(N\)]\) group.",Red]];Return[{{}}];];
)];

isAutomorphism::usage=
"isAutomorphism[allRootsTransformed_,allRoots_]:
Checks whether a root map is an automorphism at all, either inner or outer.
Arguments:
	*) allRootsTransformed_: A list of roots that has been transformed with the map in question
	*) allRoots: A list of roots prior to transformation 
Returns:
	All elements of the Weyl group of \!\(\*SubscriptBox[\(E\), \(n\)]\).
"
isAutomorphism[allRootsTransformed_,allRoots_]:=(If[compareSets[allRootsTransformed,allRoots],Print["Braid action is ",Style["automorphism",Green,Bold]],Print["Braid action is ",Style["no automorphism",Red,Bold]]]);

highestWeightProcedure::usage=
"highestWeightProcedure[weightDynkBasis_,cartanM_,highestWeight_,SRTs_]:
Performs the highest weight procedure, starting with highestWeight_.
Arguments:
	*) weightDynkBasis_: The Dynkin labels of the highest weights
	*) cartanM_: The Cartan matrix of the Lie Algebra to which the highest weight belongs
	*) highestWeight_: The highest weight with which to start
	*) SRTs_: A set of simple roots of the Lie Algebra to which the highest weight belongs
Returns:
	All weights in the irrep of which highestWeight_ is the highest weight.
"
highestWeightProcedure[weightDynkBasis_,cartanM_,highestWeight_,SRTs_]:=Module[{res},( 
dynkLbls={{weightDynkBasis,lvl->0}};
weightVecs={{highestWeight,lvl->0}};
res=HighestWeightProcedure[weightDynkBasis,cartanM,SRTs];
Clear[dynkLbls,weightVecs];
Return[res];
)];

(*Do not use by itself. Called by function above.*)
HighestWeightProcedure[weight_,cartanM_,SRTs_]:=Module[{i,j,weightN,weightDescend,level,weightD},( 
weightDescend=Table[a[j],{j,Length[cartanM]}]/.Solve[dynkLbls[[1,1]]==weight+Sum[a[i] cartanM[[i]],{i,Length[cartanM]}]][[1]];
level=Plus@@weightDescend;
weightN={weightVecs[[1,1]]+Sum[a[i] SRTs[[i]],{i,Length[SRTs]}],lvl->level}/.Table[a[i]->weightDescend[[i]],{i,Length[weightDescend]}];
weightD={weight,lvl->level};
If[!MemberQ[dynkLbls,weightD],AppendTo[dynkLbls,weightD];];
If[!MemberQ[weightVecs,weightN],AppendTo[weightVecs,weightN];];
For[i=1,i<=Length[weight],i++,For[j=weight[[i]],j>0,j--,HighestWeightProcedure[weight-j cartanM[[i]],cartanM,SRTs];];];
Return[{SortBy[dynkLbls, Last],SortBy[weightVecs, Last]}];)];

getOrbits::usage=
"getOrbits[weights_,trafoM_]:
Find the orbits of the weights under the braid map
Arguments:
	*) weights_: The weights for which the orbits shall be computed
	*) trafoM_: The transformation matrix associated with the braid
Returns:
	Nothing, output is printed only.
"
getOrbits[weights_,trafoM_]:=Module[{i,weightsTransformed,currWeight,currWeightT,currWeightCycle,leftWeights},( 
weightsTransformed=Table[trafoM.weights[[i]],{i,Length[weights]}];
If[!compareSets[weights,weightsTransformed],Print["The braid action is not an automorphism on the weight space. The following weights are mapped outside of the original weight space:", Complement[weights,weightsTransformed]];
Return[];
];
leftWeights=weights;
While[Length[leftWeights]>0,
currWeight=leftWeights[[1]];
currWeightCycle={currWeight};
currWeightT=trafoM.currWeight;
For[i=1,i<=100,i++,
If[currWeightT==currWeight,Print["Orbit of length ",i,": ",currWeightCycle];leftWeights=Complement[leftWeights,currWeightCycle];Break[];];
AppendTo[currWeightCycle,currWeightT];
currWeightT=trafoM.currWeightT;
];
];
)];


(* ::Subsection::Closed:: *)
(*Junction Functions*)


getJunctions::usage=
"getJunctions[intersectionValue_,SRTs_,dynkLbl_,iMat_,cycles_]:
This function computes all junctions that have the given Dynkin label and self-intersection.
Arguments:
	*) intersectionValue_: The \"length\" or self-intersection of the highest weights for which the alogorithm searches (in N=2 this is fixed from the BPS condition)
	*) SRTs_: A set of simple roots of the algebra to which the Dynkin label belongs
	*) dynkLbl_: The Dynkin label we are interested in, i.e. for which we want to find the string junctions
	*) iMat_: The intersection matrix with respect to which we take the inner product of string junctions
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given
Returns:
	A set of junctions that have the specified length and Dynkin label.
"
getJunctions[intersectionValue_,SRTs_,dynkLbl_,iMat_,cycles_]:=Module[{genJ,a,i,eqnSys,ares,allJs},( 
genJ=Table[a[i],{i,Length[iMat]}];
eqnSys={genJ.iMat.genJ==intersectionValue,getDynkLbl[SRTs,genJ,iMat]==dynkLbl};
(*ares=Reduce[eqnSys,Integers]/.removeAnd/.putArrow/.removeOr;*)
ares=FindInstance[eqnSys,genJ,Integers,10000];
If[Length[ares]==0,Return[{}]];
If[ArrayDepth[ares]==1,ares={ares}];
allJs=Table[genJ/.ares[[i]],{i,Length[ares]}];
Return[Table[{allJs[[i]],getAsymptoticCharge[cycles,allJs[[i]]]},{i,Length[allJs]}]];
)];

getAsymptoticCharge::usage=
"getAsymptoticCharge[cycles_,junction_]:
This function computes the asymptotic charge of a junction.
Arguments:
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given
	*) junction_: The junction whose asymptotic charge shall be computed
Returns:
	The asymptotic charge of the junction.
"
getAsymptoticCharge[cycles_,junction_]:=Return[Sum[cycles[[i]] junction[[i]],{i,Length[junction]}]];

getJunctionsByAsympCharge::usage=
"getJunctionsByAsympCharge[intersectionValue_,acharge_,iMat_,cycles_]:
This function returns a list of junctions which have the specified asymptotic charge and self-intersection.
Arguments:
	*) intersectionValue_: The \"length\" or self-intersection of the highest weights for which the alogorithm searches (in N=2 this is fixed from the BPS condition)
	*) acharge_: The asymptotic charge we are interested in, i.e. for which we want to find the string junctions
	*) iMat_: The intersection matrix with respect to which we take the inner product of string junctions
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given

Returns:
	A set of junctions with the specified asymptotic charge and self-intersection.
"
getJunctionsByAsympCharge[intersectionValue_,acharge_,iMat_,cycles_]:=Module[{genJ,a,i,eqnSys,ares,allJs},( 
genJ=Table[a[i],{i,Length[iMat]}];
eqnSys={genJ.iMat.genJ==intersectionValue,getAsymptoticCharge[cycles,genJ]==acharge};
ares=Reduce[eqnSys,Integers]/.removeAnd/.putArrow/.removeOr;
If[Length[ares]==0,Return[{}]];
If[ArrayDepth[ares]==1,ares={ares}];
allJs=Table[genJ/.ares[[i]],{i,Length[ares]}];
Return[allJs];
)];

getPermuationMatrix::usage=
"getPermuationMatrix[a_,b_,cycles_]:
This function returns the permutation matrix induced by the braid corresponding to the (3a,2b) torus knot or link.
Arguments:
	*) a_: The first parameter of the torus knot
	*) b_: The second parameter of the torus knot
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given
Returns:
	The permutation matrix induced by the torus knot/link.
"
getPermuationMatrix[a_,b_,cycles_]:=Module[{},( 
If[MemberQ[cycles, pi2],
(*in the f-tube*)
Return[Table[If[Mod[i,3a]==Mod[j+2b,3 a],1,0],{i,3a},{j,3a}]];,
(*in the g-tube*)
Return[Table[If[Mod[i,2b]==Mod[j+3a,2b],1,0],{i,2b},{j,2b}]];
];
)];

getIntersectionMatrix::usage=
"getIntersectionMatrix[cycles_,startPoint_]:
This function returns the intersection matrix for the specified vanishing cycles. This depends on an ordering of the cycles, which is specified by startPoint, which gives the cone of the second base point.
Arguments:
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given
	*) startPoint_: The cone in which the second base point lies. If omitted this defaults to 1. Note that the braid also moves the second base point
Returns:
	The intersection matrix with respect to the cycle basis.
"
getIntersectionMatrix[cycles_,startPoint_]:=Module[{U,j,k},( 
U=-IdentityMatrix[Length[cycles]];
For[j=startPoint,j<=startPoint+Length[cycles]-1,j++,For[k=startPoint,k<=j-1,k++,U[[Mod[j,Length[cycles],1],Mod[k,Length[cycles],1]]]=cycles[[Mod[k,Length[cycles],1]]].{{0,1},{-1,0}}.cycles[[Mod[j,Length[cycles],1]]]];];
Return[1/2 (U+Transpose[U])];
)];
getIntersectionMatrix[cycles_]:=Return[getIntersectionMatrix[cycles,1]];

selfIntersect::usage=
"selfIntersect[J_,cycles_, intM_]:
This function computes the self-intersection of a junction J in a cycle basis cycles_ w.r.t. the intersection matrix intM_.
Arguments:
	*) J_: Junction vector
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given
	*) intM_: The intersection matrix with respect to which the intersection product is defined
Returns:
	The value of the self-intersection
"
selfIntersect[J_,cycles_, intM_]:=(Return[-2+GCD@@getAsymptoticCharge[cycles,J]]);

intersect::usage=
"intersect[J1_,J2_,intM_]:
This function computes the intersection of a junction J1 with a junction J2_, i.e. J1.J2 w.r.t. the intersection matrix intM_.
Arguments:
	*) J1_: First junction vector
	*) J2_: Second junction vector
	*) intM_: The intersection matrix with respect to which the intersection product is defined
Returns:
	The value of the intersection product J1.J2
"
intersect[J1_,J2_,intM_]:=Return[J1.intM.J2];

getCycleSign::usage=
"getCycleSign[a_,b_,cycles_]:
This function computes the sing change induced by the braid map induced by the (3a,2b) torus knot/link w.r.t. the inverse of the anti-clockwise cycle map
Arguments:
	*) a_: First parameter of the torus knot/link
	*) b_: Second parameter of the torus knot/link
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given
Returns:
	A matrix that encodes the sign flips on the junction vectors induced by the braid map.	
"
getCycleSign[a_,b_,cycles_]:=Module[{i,j},( 
If[a>=4 || b>=6 ,Print["Not implemented for a>=4 or b>=6."];Return[IdentityMatrix[Length[cycles]]]];
If[MemberQ[cycles, pi2],
(*in the f-tube*)
Return[Table[KroneckerDelta[i,j](-1)^(b),{i,Length[cycles]},{j,Length[cycles]}]]
,
(*in the g-tube*)
Return[Table[KroneckerDelta[i,j]If[Mod[i,2]==0,(-1)^(Floor[a/2]),(-1)^(Floor[(a+1)/2])],{i,Length[cycles]},{j,Length[cycles]}]]
]
)];

getActionOnSimpleRoots::usage=
"getActionOnSimpleRoots[SRTs_,SRTsTransformed_]:
This function computes the map between the simple roots of SRT_ and SRTsTransformed_. Note that this gives the map on the level of the simple roots themselves, not on the level of the root junction vector entries (that map is obtained from the braid action).
Arguments:
	*) SRTs_: A set of simple roots
	*) SRTsTransformed_: The transformed set of simple roots, i.e. the simple roots obtained after applying the braid map to the simple root junctions of SRTs_
Returns:
	The induced map on the level of the simple roots (not on the level of the junction vector entries).
"
getActionOnSimpleRoots[SRTs_,SRTsTransformed_]:=Module[{i,a,res,action},( 
action={};
For[i=1,i<=Length[SRTs],i++,
res=Solve[SRTsTransformed[[i]]==Sum[a[i] SRTs[[i]],{i,Length[SRTs]}]];
If[Length[res]!=1,Print[Style["Something is wrong with the simple root set!",Red]];Return[{{}}];];
AppendTo[action,Table[a[i],{i,Length[SRTs]}]/.res[[1]]];
];
Return[action];
)];

getInvariantRootCombos::usage=
"getInvariantRootCombos[SRTTrafoM_]:
This function computes the set of simple roots that are left invariant by SRTTrafoM_ (this matrix can be obtained from the function getActionOnSimpleRoots).
Arguments:
	*) SRTTrafoM_: The transformation matrix induced by the braid on the level of the simple roots
Returns:
	The eigenvectors of the transformation matrix with eigenvalues 1, i.e. the coefficients specifying the linear combination that leads to invariant roots.
"
getInvariantRootCombos[SRTTrafoM_]:=Module[{eigSys,eigVV,i,j},( 
eigSys=Eigensystem[SRTTrafoM];
eigVV={};
For[i=1,i<=Length[eigSys[[1]]],i++,If[eigSys[[1,i]]==1,AppendTo[eigVV,eigSys[[2,i]]]]];
(*
Print[Eigenvalues[SRTTrafoM]];
Print[NullSpace[(IdentityMatrix[Length[SRTs]]-SRTTrafoM)]];
Print[eigVV];
*)
Print["Rank: ",Length[NullSpace[(IdentityMatrix[Length[SRTs]]-SRTTrafoM)]],", Eigenvalues are: ",FullSimplify[eigSys[[1]]]];
Print["Invariant simple root combos: ",Table[eigVV[[i]].Table[\[Alpha][j],{j,Length[SRTTrafoM]}],{i,Length[eigVV]}]];
Return[eigVV];
)];

getJP::usage=
"getJP[trafoM_,cycles_]:
This function illustrates the map of the junction vector entries that is induced by trafoM_ and shows how the asymptotic charges are mapped.
Arguments:
	*) trafoM_: The transformation matrix induced by the braid on the level of the junction vector entries
	*) cycles_: A basis for the vanishing cycles with respect to which the junction vectors are given
Returns:
	Noting. Output is printed only.
"
getJP[trafoM_,cycles_]:=(Print["Map on the junction vector entries:"];Print[Table[j[i],{i,Length[trafoM]}], " -> ",trafoM.Table[j[i],{i,Length[trafoM]}]];Print["Map on the asymptotic charges:"];Print[getAsymptoticCharge[cycles,Table[j[i],{i,Length[trafoM]}]], " -> ",getAsymptoticCharge[cycles,trafoM.Table[j[i],{i,Length[trafoM]}]]];);
