%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%             ASU CSE 259 Logic in CS           %%
%%             Project Submission File           %%
%%                   thmpv.py                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% setting the binding priority for the logic connectives; the lower the tighter.
:-op(700,xfy,=>).
:-op(650,xfy,->).
:-op(600,xfy,v).
:-op(500,xfy,^).
:-op(450,fy,~).

%
% type 'run([<Premises as a list>], [<A formula as the conclusion>]). E.g., run([p ^ q], [p])' to start
%

run(Premises, Conclusion):-
    write(Premises => Conclusion),
    deduce(Premises => Conclusion).

deduce(X):-
    prove(X), !,
    write('\n\nWe can derive the conclusion from the premises.\n').
deduce(X):-
    write('\n=\tCannot be proved.'),
    write('\n\nWe cannot derive the conclusion from the premises.\n\nAn interpretation of the signature where this does not hold:'),
    reduce(X).

% predicate to delete an element X from a list L.
del(X,[X|Tail],Tail).
del(X,[H|Tl1],[H|Tl2]):-
    del(X,Tl1,Tl2).

% remove duplicate formulas in a list
rmvDup([], []).
rmvDup([H|Tail], [H|Tail1]):-
    \+member(H, Tail),
    rmvDup(Tail, Tail1).
rmvDup([H|Tail], Tail1):-
    member(H, Tail),
    rmvDup(Tail, Tail1).

% exampe rule: negation
prove(L => R):-
    member(~X,L),
    del(~X,L,NewL),
    nl,write('=\t'),write(NewL => [X|R]),
    write('\t (by negation/left)'),
    prove(NewL => [X|R]).
prove(L => R):-
    member(~X,R),
    del(~X,R,NewR),
    nl,write('=\t'),write([X|L] => NewR),
    write('\t (by negation/right)'),
    prove([X|L] => NewR).

% exampe rule: left conjunction
% non-branching rules
prove(L => R):-
    member(A ^ B,L),
    del(A ^ B,L,NewL),
    nl,write('=\t'),write([A,B|NewL] => R),
    write('\t (by and/left)'),
    prove([A,B|NewL] => R).

%%%%%%%%%%%%%%%% YOUR CODE STARTS %%%%%%%%%%%%%%%%

% Implement all other non-branching rules below by following Wang's algorithm

% The Right Disjunction
prove(L => R) :-
	member(A v B, R), 		               			% Checks if A v B located on right
	del( A v B, R, NewR), 			      			% Removes A v B from right
	nl,write('=\t'),write( L => [A,B|NewR]),       			% Prints new formula with v replaced by comma
	write('\t (by or/right)'), 		      			% Prints rule used
	prove(L => [A,B|NewR]). 		       			% Proves new formula

% Right Implication
prove(L => R) :-
	member(A -> B, R), 						% Checks if A -> B on right
	del( A -> B, R, NewR), 						% Removes A -> B from the right
	nl,write('=\t'),write( [A|L] => [B|NewR]), 			% Prints new formula with A moved to left and B on right
	write('\t (by arrow/right)'), 					% Prints rule used
	prove([A|L] => [B|NewR]). 					% Proves new formula

% Implement all branching rules below by following Wang's algorithm

% The Left Disjunction
prove(L => R) :-
	member(A v B, L), 					% Checks if A v B located on left
	del(A v B, L, NewL), 				        % Removes A v B from left
	nl,write('=\t'),write( [A|NewL] => R ),		        % Prints first branch A added to left
	write('\t (by or/left) (1)'),				% Prints rule used 
	prove([A|NewL] => R ),					% Proves first branch
	nl,write('=\t'),write( [B|NewL] => R),			% Prints second branch B added to left
	write('\t (by or/left) (2)'),				% Prints rule used
	prove([B|NewL] => R ).					% Proves second branch
	
% right conjunction
prove(L => R) :-
	member(A ^ B, R),					% Checks if A ^ B is on right 
	del(A ^ B, R, NewR),					% Removes A ^ B from right 
	nl,write('=\t'),write( L => [A|NewR] ),			% Prints first branch A added to right 
	write('\t (by and/left) (1)'),				% Prints rule used
	prove(L => [A|NewR] ),					% Proves first branch 
	nl,write('=\t'),write( L => [B|NewR]),			% Prints second branch B added to right 
	write('\t (by and/left) (2)'),				% Prints rule used
	prove(L => [B|NewR] ).					% Proves second branch 

% left implication
prove(L => R) :-
	member(A -> B, L),					% Checks if A -> B is on left 
	del( A -> B, L, NewL),					% Removes A -> B from left
	nl,write('=\t'),write( [B|NewL] => R),			% Prints first branch with B added to left 
	write('\t (by arrow/left) (1)'),			% Prints rule used
	prove([B|NewL] => [A|R]),				% Proves first branch
	nl,write('=\t'),write( NewL => [A|R]),			% Prints second branch A added to right 
	write('\t (by arrow/left) (2)'),			% Prints rule used
	prove(NewL => [A,R]).					% Proves second branch 

%%%%%%%%%%%%%%%% YOUR CODE ENDS %%%%%%%%%%%%%%%%

% rule for checking shared atom or formula
prove(L => R):-
    member(X,L),
    member(X,R),
    nl,write('=\tDone (sharing a/f)').

% reduces expression so you can print out what the false stuff is
reduce(L => R):-
    member(~X,L),
    del(~X,L,NewL),
    reduce(NewL => [X|R]).      %negation left
reduce(L => R):-
    member(~X,R),
    del(~X,R,NewR),
    reduce([X|L] => NewR).      %negation right
reduce(L => R):-
    member(A ^ B,L),
    del(A ^ B,L,NewL),
    reduce([A,B|NewL] => R).    %and/left
reduce(L => R):-
    member(A v B,R),
    del(A v B,R,NewR),
    reduce(L => [A,B|NewR]).    %or/right
reduce(L => R):-
    member(A -> B,R),
    del(A -> B,R,NewR),
    reduce([A|L] => [B|NewR]).  %arrow/right
reduce(L => R):-
    member(A ^ B,R),
    del(A ^ B,R,NewR),
    reduce(L => [A|NewR]),
    reduce(L => [B|NewR]).      %and/right
reduce(L => R):-
    member(A v B,L),
    del(A v B,L,NewL),
    reduce([A|NewL] => R),
    reduce([B|NewL] => R).      %or/left
reduce(L => R):-
    member(A -> B,L),
    del(A -> B,L,NewL),
    reduce([B|NewL] => R),
    reduce(NewL => [A|R]).      %arrow/left
reduce(L => R):-
    member(X,L),
    member(X,R).
reduce(L => R):-
    rmvDup(L, NewL),
    rmvDup(R, NewR),
    write('\nSetting '),write(NewL),
    write(' as True, and '),write(NewR),write(' as False.').
