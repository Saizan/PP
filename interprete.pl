:- set_prolog_flag(occurs_check, true).
:- op(500, yfx, $).
:- op(600, xfx, /).

first((X:Y), Xs) :- memberchk((X:Y0), Xs), Y0 = Y.

type(C, var(X), T) :- (first(X:T0, C) -> instantiate(T0, T) ; axiom(X, T)).
type(C, lam(X,E), A -> B) :- type([X:mono(A)|C], E, B).
type(C, E0 $ E1, B) :- type(C, E0, A -> B), type(C, E1, A).
type(C, let(X = E0,E1), T) :- 
    type([X:mono(A0)|C], E0, A0), generalize(C, A0, A),
    type([X:A|C], E1, T).
type(C, letN(Xs,E), T) :- typeN(C, Xs, C1), type(C1, E, T).
type(C, case(E,Clauses), T) :- 
    type(C, E, A),
    typeClauses(C, Clauses, A, T), \+ A = (_ -> _).

generalize(C, T, poly(Vs,T)) :- term_variables(C, Vs).

instantiate(poly(Vs,T0), T) :- copy_term((Vs,T0), (Vs,T)).
instantiate(mono(T), T).

typePat(C, con(Con,Vs), T, C1) :- axiom(Con, T0), typeVars(Vs, T0, T, C1, C).

typeVars([], T, T) --> [].
typeVars([var(X)|Vars], A -> T0, T) --> typeVars(Vars, T0, T), [X:mono(A)].

typeClause(C, PatType, BodyType, Pat -> Body) :- 
    typePat(C, Pat, PatType, C1), 
    type(C1, Body, BodyType). 

typeClauses(C, Clauses, PatType, BodyType) :- maplist(typeClause(C,PatType,BodyType), Clauses).

typeN(C0, Xs, C) :- typeN(C0, C1, Xs, C1, C).
typeN(C, IC, [X = E|Xs], [X:mono(A)|Ms], [X:XT|Ps]) :- 
    generalize(C, A, XT),
    typeN(C, IC, Xs, Ms, Ps),
    type(IC, E, A).
typeN(C,_IC, [], C, C).

axiom(unit , unit                   ).
axiom(true , bool                   ).
axiom(false, bool                   ).
axiom(zero , nat                    ).
axiom(suc  , nat -> nat             ).
axiom(pair , A -> B -> (A,B)        ).
axiom(inl  , A -> A + _B            ).
axiom(inr  , B -> _A + B            ).
axiom(nil  , list(_A)               ).
axiom(cons , A -> list(A) -> list(A)).

is_intro(Type) :- var(Type), !, false.
is_intro(_ -> Type) :- is_intro(Type).
is_intro(Type) :- \+ Type = (_ -> _).

:- forall(axiom(_, Type), is_intro(Type)).
:- findall(Name, axiom(Name,_), Names0),
   list_to_ord_set(Names0, Names),
   same_length(Names0, Names).

alphabetize([], _).
alphabetize([X|Xs], N) :- atom_codes(X, [N]), N1 is N+1, alphabetize(Xs,N1).
alphabetize(Xs) :- atom_codes(a,[N]), alphabetize(Xs,N).



axiomBody(Type, Name, Vars, Body, []) :- \+ Type = (_ -> _), Body = con(Name,Vars).
axiomBody(_ -> Type, Name, Vars, lam(X,Body), [var(X)|Xs]) :- axiomBody(Type, Name, Vars, Body, Xs). 
axiomBody(Name, Type, Body) :- axiomBody(Type, Name, Vars, Body, Vars), term_variables(Body, Xs), alphabetize(Xs).
axiomBody(Name, Body) :- axiom(Name, Type),axiomBody(Name, Type, Body).

eval(Expr / Env, Value) --> eval(Expr, Env, Value).

eval(var(X), Env, Value) --> 
    (  {first((X:Ref), Env)} 
    -> lookup(Ref:Closure), eval(Closure, Value), update(Ref, Value)
    ;  {axiomBody(X, Body), Value = Body / []}
    ). 
eval(lam(X,B), Env, lam(X,B) / Env) --> [].
eval(Expr0 $ Expr1, Env, Value) --> 
    eval(Expr0 / Env, lam(X,B) / LEnv),
    alloca(Expr1 / Env, Ref),
    eval(B / [(X:Ref)|LEnv], Value).
eval(let(X = Expr0,Expr1), Env, Value) --> 
    {NewEnv = [(X:Ref)|Env]},
    alloca(Expr0 / NewEnv, Ref),
    eval(Expr1 / NewEnv, Value).
eval(letN(Binds,Expr), Env, Value) --> allocaMany(Env, Binds, NewEnv), eval(Expr / NewEnv, Value).
eval(con(Con,Vars), Env, con(Con,Vars) / Env) --> [].
eval(case(Expr,Clauses), Env, Value) --> 
    eval(Expr / Env, Scrutinee),
    {match(Scrutinee, Clauses / Env, Match)},
    eval(Match, Value).

match(con(Con,Vars) / Env, [con(Con1,Vars1)->Body|Clauses] / Env1, Match) :- !,
    (  Con = Con1
    -> matchEnv(Vars, Env, Vars1, Env1, NewEnv1), Match = Body / NewEnv1
    ;  match(con(Con,Vars) / Env, Clauses / Env1, Match)
    ).

matchEnv([], _, [], Env, Env).
matchEnv([var(X)|Vs], Env, [var(Y)|Vs1], Env1, Env2) :- first((X:Ref), Env),matchEnv(Vs, Env, Vs1, [Y:Ref|Env1], Env2).

buildEnv_loop([]) --> [].
buildEnv_loop([X = _|Xs]) --> [X:_], buildEnv_loop(Xs).

buildEnv(Env, Xs, Env1) :- buildEnv_loop(Xs, Env1, Env).

allocaMany(Env0, Xs, Env) --> {buildEnv(Env0, Xs, Env)}, allocaMany(Env, Xs).
allocaMany(Env, [X = E|Xs]) --> {first((X:Ref), Env)}, alloca(E / Env, Ref), allocaMany(Env, Xs).
allocaMany(_, []) --> [].


alloca(C, Ref, heap(Ref,List), heap(Next,[Ref:C|List])) :- Next is Ref + 1.

lookup(Binding, H, H) :- H = heap(_,Bindings), first(Binding, Bindings).

update(Ref, Closure, heap(N,L0), heap(N,L)) :- 
    append(Xs,[Ref:_|Ys],L0) 
    -> append(Xs,[Ref:Closure|Ys],L)
    ;  L0 = L.

deep_eval(E / Env) --> 
    {E = con(_,Vs)}
    -> deep_eval_list(Vs / Env)
    ; [].

deep_eval_list(E / Env) --> deep_eval_list(E, Env).
deep_eval_list([], _Env) --> [].
deep_eval_list([X|Xs], Env) --> eval(X / Env, R), deep_eval(R), deep_eval_list(Xs / Env).

deep_eval(E, R) --> eval(E, R), deep_eval(R).

:- findall(V,first(id:V,[x:3,id:1,id:2]),Vs), Vs = [1].
:- \+ first(id:2,[x:3,id:1,id:2]).

stlc(C, var(X), T) :- first(X:T, C).
stlc(C, lam(X,E), A -> B) :- stlc([X:A|C], E, B).
stlc(C, E0 $ E1, B) :- stlc(C, E0, A -> B), stlc(C, E1, A).


ident(I) --> [i(I)].

binding(X = E) --> ident(X), [=], expr(E).
bindings([B|Bs]) --> binding(B), [;], bindings(Bs).
bindings([]) --> [].

many1(P, [X|Xs]) --> call(P,X), many(P, Xs).
many(P, Xs) --> many1(P, Xs) ; {Xs=[]}.

var(var(X)) --> ident(X).

pattern(con(Con,Vs)) --> many1(var, [var(Con)|Vs]).

clause(P -> E) --> pattern(P), [.], expr(E).
clauses([C|Cs]) --> clause(C), [;], clauses(Cs).
clauses([]) --> [].

expr(lam(X,E)) --> [\], ident(X), [.], expr(E).
expr(let(B,E)) --> [let], binding(B), [in], expr(E).
expr(lenN(Bs,E)) --> [let], bindings(Bs), [in], expr(E).
expr(case(E,Cs)) --> [case], expr(E), [of], clauses(Cs).
expr(E) --> spine(E).

term(var(X)) --> ident(X).
term(E) --> ['('], expr(E), [')'].

fold([Tm|Tms], F, Tree, G $ _) :- fold(Tms, F $ Tm, Tree, G).
fold([], Tree, Tree, _).

fold([X|Xs], E) :- fold(Xs, X, E, E).

spine(E) --> {var(E)} -> many1(term,Tms), {fold(Tms,E)} ; {fold(Tms,E)}, many1(term,Tms).

parse(E, S) :- lex(Ts, S, ""), expr(E0, Ts, []), desugar(E0, E).

parseBinds(Bs, S) :- lex(Ts, S, ""), bindings(Bs0, Ts, ""), desugar(Bs0, Bs).

desugar(var(X), E) :- !, 
    (  integer(X) 
    -> desugar_nat(X, E)
    ;  E = var(X)).
desugar(X, Y) :- X =.. [F|Xs], same_length(Xs, Ys), Y =.. [F|Ys], maplist(desugar, Xs, Ys).

desugar_nat(0, var(zero)) :- !.
desugar_nat(N, var(suc) $ E) :- N1 is N-1, desugar_nat(N1, E).


greedy(Ty, Xs) --> greedy1(Ty, Xs) -> [] ; {Xs = []}.
greedy1(Ty, [X|Xs]) --> [X], {code_type(X, Ty)}, greedy(Ty, Xs).

spaces --> greedy(space,_).

lexToken1(Tok) --> [Code], {member(Code, "();.\\="), atom_codes(Tok, [Code])}.
lexToken1(Tok) --> greedy1(alpha, Codes), {atom_codes(A, Codes)}, {member(A, [let,in,case,of]) -> Tok = A ; Tok = i(A)}.
lexToken1(Tok) --> greedy1(digit, Codes), {number_codes(A, Codes), Tok = i(A)}.

lexToken(Tok) --> lexToken1(Tok), ! ,spaces.
  
lex(Tokens) --> spaces, many(lexToken, Tokens).

showToken(Tok) --> {atomic(Tok) -> A = Tok ; i(A) = Tok},{atom_codes(A, Codes)},Codes.

showSpace0(Tok, _) --> {member(Tok, [let,in,=,'.',;,case,of])}," ".
showSpace0(')', Tok) --> {member(Tok, [')','.',;])} -> [] ; " ".
showSpace0('(', _) --> [].
showSpace0(\, _) --> [].
showSpace0(i(_), Tok) --> {member(Tok, [')','.',;])} -> [] ; " ".

showSpace([], _) --> [].
showSpace([Tok1|_], Tok) --> showSpace0(Tok, Tok1).

show([]) --> [].
show([Tok|Tokens]) --> showToken(Tok), showSpace(Tokens,Tok), show(Tokens).

pprint(E, Codes) :- once(expr(E, Tokens, [])), show(Tokens, Codes, "").

:- E = let(x=lam(y, var(y)), lam(h, var(foo)$var(x))), pprint(E,S), S = "let x = \\y. y in \\h. foo x" .
:- E = var(foo)$var(bar)$var(baz)$var('Q'), pprint(E,S), S = "foo bar baz Q".


translate(con(zero,[]), var(0)) :- !.
translate(con(suc,[V]), E) :- !, translate(V, Arg),
    (  Arg = var(N),integer(N)
    -> E = var(N1), N1 is N + 1
    ; E = con(suc,[Arg])).
translate(con(K,Vs), E) :- !, maplist(translate, Vs, Es), fold([var(K)|Es], E).
translate(case(E,Cls), case(E1,Cls1)) :- !, translate(E, E1), maplist(translateClause, Cls, Cls1).
translate(X, Y) :- X =.. [F|Xs], same_length(Xs, Ys), Y =.. [F|Ys], maplist(translate, Xs, Ys).

translateClause(Pat -> Cl, Pat -> Cl1) :- translate(Cl, Cl1).

addEnv(Env, E, E / Env).

maplist_dcg([], _P, []) --> [].
maplist_dcg([X|Xs], P, [Y|Ys], S, T) :- call(P,X,Y,S,S1), maplist_dcg(Xs, P, Ys, S1, T).

inline(var(X) / Env, R) --> {first((X:Ref), Env)}, !, lookup(Ref:C), inline(C, R).
inline(con(K,Vs) / Env, con(K,Rs)) --> !, {maplist(addEnv(Env), Vs, Vs1)},maplist_dcg(Vs1, inline, Rs).
inline(lam(_,_) / _Env, var('$function')) --> !, [].
inline(E / Env, R) --> {E =.. [F|Xs], same_length(Xs, Ys), R =.. [F|Ys], maplist(addEnv(Env), Xs, Xs1)}, maplist_dcg(Xs1, inline, Ys).

pretty(X:Type0, X:TypeR) :- instantiate(Type0, Type), term_variables(Type, Xs), alphabetize(Xs),
    (Xs = [] -> TypeR = Type ; TypeR = forall(Xs,Type)).


write_codes([]).
write_codes([X|Xs]) :- put_code(X), write_codes(Xs).

writeln(L) :- write_codes(L), nl.

readln(L) :- write_codes("> "), current_stream(0, read, Stdin), read_line_to_codes(Stdin, L).


or_throw(P) :- call(P) -> true ; throw(error(P)).
or_throw(P,S,T) :- call(P,S,T) -> true ; throw(error(P)).

evalio((C,Env), Line) --> 
    {or_throw(parse(E, Line)),
     or_throw(type(C, E, Type0)),
     pretty(_:poly(C, Type0), _:Type),
     write(Type),nl
    }, 
    or_throw(deep_eval(E / Env, R0)), 
    inline(R0, R),
    {translate(R, RE),
     pprint(RE, S),
     writeln(S)
    }.

prefix(Bs, CE, Pr) :- same_length(Bs,Pr), append(Pr, _, CE). 

letio(Line, (C0,Env0), (C,Env)) --> 
    {or_throw(parseBinds(Binds, Line)),
     or_throw(typeN(C0, Binds, C)),
     prefix(Binds, C, BindsTypes0),
     maplist(pretty, BindsTypes0, BindsTypes),
     write(BindsTypes),nl
    }, 
    allocaMany(Env0, Binds, Env).

debug((C,Env),H) :-
    write_codes("context: "),write(C),nl,
    write_codes("env:     "),write(Env),nl,
    write_codes("heap:    "),write(H),nl.
 
print_error(parse(_,_)) :- !, writeln("parse error.").
print_error(parseBinds(_,_)) :- !, writeln("parse error.").
print_error(type(_,_,_)) :- !, writeln("type error.").
print_error(typeN(_,_,_)) :- !, writeln("type error.").
print_error(deep_eval(_,_)) :- !, writeln("runtime error.").
print_error(E) :- write(E),nl.  

ep(Cmd, REnv0, REnv, H0, H) :-
 catch(
  ( Cmd = ""
  -> H0 = H, REnv0 = REnv
  ; Cmd = ":exit"
  -> throw(exit)
  ; Cmd = ":debug"
  -> debug(REnv0,H0), REnv0 = REnv, H0 = H
  ; append(":let", Line, Cmd)
  -> letio(Line, REnv0, REnv, H0, H)
  ; append(":load", File, Cmd)
  -> load_file(File, REnv0, REnv, H0, H)
  ; REnv0 = REnv, evalio(REnv, Cmd, H0, H)
  ), error(E), (H0 = H, REnv0 = REnv, print_error(E))).

load_file(FileCs, REnv0, REnv, H0, H) :- 
    atom_codes(File0, FileCs),
    normalize_space(atom(File), File0),
    read_file_to_codes(File, Cs, []),
    splitCmds(Cmds, Cs),
    load_loop(Cmds, REnv0, REnv, H0, H).

splitCmds(Cmds, [X|Xs]) :- 
    ":" = [X] 
    -> Cmds = [[],[X|Cmd]|Cmds1], splitCmds([Cmd|Cmds1], Xs)
    ; splitCmds([Cmd|Cmds1], Xs), Cmds = [[X|Cmd]|Cmds1].
splitCmds([[]], []).

load_loop([], REnv, REnv, H, H).
load_loop([Cmd|Cmds], REnv0, REnv, H0, H) :- ep(Cmd, REnv0, REnv1, H0, H1), load_loop(Cmds, REnv1, REnv, H1, H).
    
rep(REnv0, REnv, H0, H) :- readln(Cmd), ep(Cmd, REnv0, REnv, H0, H).

repl(REnv0, H0) :- rep(REnv0, REnv, H0, H), repl(REnv, H).

repl :- catch(repl(([],[]), heap(0,[])), exit, true).
