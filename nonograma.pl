

% Ejercicio 1

matriz(F, C, M) :-
	%Asegura las filas que va a tener la matriz
	length(M, F),
	%Las Posiciones de M tienen Filas de C posiciones C/U
	maplist(fila(C), M).

fila(C, FILA) :- length(FILA, C).

% Ejercicio 2


%Mientras N sea > 0 el Head de la lista es X
replicar(_,0,[]).
replicar(X, N, [X|YS]) :-  
	N > 0,
	N2 is N-1,
	replicar(X,N2,YS).

% Ejercicio 3

transponer([[]|_], []).
transponer(M,[Fila|MT]):-
	transponerfila(M, Fila, Res),
	%Res es M con una columna menos
	transponer(Res, MT).

transponerfila([],[],[]).
%Va vaciando la matriz M a la vez que unifica la columna de M con la fila de MT
transponerfila([[X|XS]|M], [X|YS], [XS|MT]) :- transponerfila(M, YS, MT).

% Predicado dado armarNono/3
armarNono(RF, RC, nono(M, RS)) :-
	length(RF, F),
	length(RC, C),
	matriz(F, C, M),
	transponer(M, Mt),
	zipR(RF, M, RSFilas),
	zipR(RC, Mt, RSColumnas),
	append(RSFilas, RSColumnas, RS).

zipR([], [], []).
zipR([R|RT], [L|LT], [r(R, L)|T]) :-
	zipR(RT, LT, T).

% Ejercicio 4


%Si no tiene restricciones llena con o
pintadasValidas(r([],L)) :- length(L,C),replicar(o,C,L).
pintadasValidas(r([X|R], L)) :- 
	length(L,N),
	sumlist([X|R], Sum),
	length([X|R], K),
	%Usa largo de L,  la sumatoria de Res y su largo para tener en cuenta todos los blancos entre pintadas
	MaxIni is N - Sum - K + 1,  
	between(0, MaxIni, X1),
	%Genera todos  los comienzos poniendo de 0 a MaxIni o´s
	replicar(o,X1,L0),
	Espacios is N - X1,
	%Llama al aux con cada una para obtener todas las pintadas posibles
	pintadasAux([X|R], Espacios, LPintada),
	append(L0, LPintada, L).

%Caso base una restricción, muy util para evitar repetidos
%Simplemente recibe una lista y una restricción, pone las x y completa con o´s
pintadasAux([X], Espacios, L) :- 
    replicar(x, X, Lpintada),	 
    EspaciosRestantes is Espacios - X,
    replicar(o, EspaciosRestantes, Lresto),
    append(Lpintada, Lresto, L).

pintadasAux([X|XS], Espacios, L):-
	%Pone tantas x como pida la primera restricción
	replicar(x, X, Lpintada), 
	sumlist(XS, Sum),      
	length(XS, OentreRest),	
	%Calcula cuantos o´s puede poner(muy similar a maxIni)
	MaxOs is Espacios - X -  Sum + OentreRest,   
	MaxOs >= 0,
	between(1,MaxOs, CantO),
	replicar(o, CantO, BloqueOs),
	EspaciosSiguiente is Espacios - X - CantO,
	%Usa la misma lógica que en la principal y genera las cantidades de o´s
	%Solo que aca tiene que generar el resto de restricciones
	pintadasAux(XS, EspaciosSiguiente, LRec),
	%luego junta la pintada actual con las o´s y el resultado con la llamada recursiva
	append(Lpintada, BloqueOs, LAct),
	append(LAct, LRec, L).


% Ejercicio 5
resolverNaive(nono(_,Celdas)) :-
	%Todas las combinaciones de pintadas validas posibles, por eso "naive"
	maplist(pintadasValidas, Celdas).

% Ejercicio 6


pintarObligatorias(r(Res,Celdas)) :-
  findall(Celdas ,pintadasValidas(r(Res, Celdas)), TodasPintadas),
 %Genera todas las formas posibles de pintar Celdas para combinarlas
  combinar(TodasPintadas, Celdas).

combinar([],[]).
%Si tengo una sola fila mi combinación es esa fila
combinar([X], X).
combinar([X,Y|TodasPintadas], Celdas):-
  %Si tengo dos o mas, combino celda a celda y guardo en un acumulador hasta tener una sola
  maplist(combinarCelda, X, Y , SolParcial),
  combinar([SolParcial|TodasPintadas], Celdas).



% Predicado dado combinarCelda/3
combinarCelda(A, B, _) :-
	var(A),
	var(B).
combinarCelda(A, B, _) :-
	nonvar(A),
	var(B).
combinarCelda(A, B, _) :-
	var(A),
	nonvar(B).
combinarCelda(A, B, A) :-
	nonvar(A),
	nonvar(B),
	A = B.
combinarCelda(A, B, _) :-
	nonvar(A),
	nonvar(B),
	A \== B.

% Ejercicio 7
deducir1Pasada(nono(_,Celdas)) :-
    %Pinto las obligatorias de cada celda
	maplist(pintarObligatorias, Celdas).

% Predicado dado
cantidadVariablesLibres(T, N) :-
	term_variables(T, LV),
	length(LV, N).


% Predicado dado
deducirVariasPasadas(NN) :-
	NN = nono(M,_),
	cantidadVariablesLibres(M, VI), % VI = cantidad de celdas sin instanciar en M en este punto
	deducir1Pasada(NN),
	cantidadVariablesLibres(M, VF), % VF = cantidad de celdas sin instanciar en M en este punto
	deducirVariasPasadasCont(NN, VI, VF).

% Predicado dado
deducirVariasPasadasCont(_, A, A). % Si VI = VF entonces no hubo más cambios y frenamos.
deducirVariasPasadasCont(NN, A, B) :- A =\= B, deducirVariasPasadas(NN).

% Ejercicio 8
restriccionConMenosLibres(nono(_,L),r(Res, Celdas)) :- 
%No hay ninguna variables mas chica en L que esta
%Y con celdas libres!
member(r(Res, Celdas), L),

cantidadVariablesLibres(Celdas, X),
X > 0,

not((
	member(r(_, Celdas2), L),
	cantidadVariablesLibres(Celdas2, Z),
	Z > 0,
	Z < X
	)).
% Ejercicio 9


resolverDeduciendo(NN) :-
	%Si lo lleno deduciendo corta
	deducirVariasPasadas(NN),
	nonoCompleto(NN).

resolverDeduciendo(NN) :-
	%Sino deduce lo que puede y toma una de las restricciones con menos libres
	deducirVariasPasadas(NN),
	restriccionConMenosLibres(NN,R),
	!,%Muy importante sino puedo tomar todas las restricciones y se dispara el nro combinatorio
	pintadasValidas(R),
	resolverDeduciendo(NN).
	

%Si tiene todas las celdas instanciadas es un nono ya resuelto	
nonoCompleto(nono(_, Res)) :-
	listaTotalInstanciada(Res).

listaTotalInstanciada([]).
listaTotalInstanciada([r(_,Celdas)|XS]):-
	cantidadVariablesLibres(Celdas, N),
	N == 0,
	listaTotalInstanciada(XS).

% Ejercicio 10
solucionUnica(NN) :-
	findall(NN, resolverDeduciendo(NN), Soluciones),
	%Si calculo todas las soluciones y tiene una sola es unica trivialmente
	length(Soluciones, K), 
	K == 1.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                              %
%    Ejemplos de nonogramas    %
%        NO MODIFICAR          %
%    pero se pueden agregar    %
%                              %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Fáciles
nn(0, NN) :-
	armarNono([[1], [2]], [[], [2], [1]], NN).
nn(1, NN) :-
	armarNono([[4], [2, 1], [2, 1], [1, 1], [1]], [[4], [3], [1], [2], [3]], NN).
nn(2, NN) :-
	armarNono([[4], [3, 1], [1, 1], [1], [1, 1]], [[4], [2], [2], [1], [3, 1]], NN).
nn(3, NN) :-
	armarNono([[2, 1], [4], [3, 1], [3], [3, 3], [2, 1], [2, 1], [4], [4, 4], [4, 2]], [[1, 2, 1], [1, 1, 2, 2], [2, 3], [1, 3, 3], [1, 1, 1, 1], [2, 1, 1], [1, 1, 2], [2, 1, 1, 2], [1, 1, 1], [1]], NN).
nn(4, NN) :-
	armarNono([[1, 1], [5], [5], [3], [1]], [[2], [4], [4], [4], [2]], NN).
nn(5, NN) :-
	armarNono([[], [1, 1], [], [1, 1], [3]], [[1], [1, 1], [1], [1, 1], [1]], NN).
nn(6, NN) :-
	armarNono([[5], [1], [1], [1], [5]], [[1, 1], [2, 2], [1, 1, 1], [1, 1], [1, 1]], NN).
nn(7, NN) :-
	armarNono([[1, 1], [4], [1, 3, 1], [5, 1], [3, 2], [4, 2], [5, 1], [6, 1], [2, 3, 2], [2, 6]], [[2, 1], [1, 2, 3], [9], [7, 1], [4, 5], [5], [4], [2, 1], [1, 2, 2], [4]], NN).
nn(8, NN) :-
	armarNono([[5], [1, 1], [1, 1, 1], [5], [7], [8, 1], [1, 8], [1, 7], [2, 5], [7]], [[4], [2, 2, 2], [1, 4, 1], [1, 5, 1], [1, 8], [1, 7], [1, 7], [2, 6], [3], [3]], NN).
nn(9, NN) :-
	armarNono([[4], [1, 3], [2, 2], [1, 1, 1], [3]], [[3], [1, 1, 1], [2, 2], [3, 1], [4]], NN).
nn(10, NN) :-
	armarNono([[1], [1], [1], [1, 1], [1, 1]], [[1, 1], [1, 1], [1], [1], [1]], NN).
nn(11, NN) :-
	armarNono([[1, 1, 1, 1], [3, 3], [1, 1], [1, 1, 1, 1], [8], [6], [10], [6], [2, 4, 2], [1, 1]], [[2, 1, 2], [4, 1, 1], [2, 4], [6], [5], [5], [6], [2, 4], [4, 1, 1], [2, 1, 2]], NN).
nn(12, NN) :-
	armarNono([[9], [1, 1, 1, 1], [10], [2, 1, 1], [1, 1, 1, 1], [1, 10], [1, 1, 1], [1, 1, 1], [1, 1, 1, 1, 1], [1, 9], [1, 2, 1, 1, 2], [2, 1, 1, 1, 1], [2, 1, 3, 1], [3, 1], [10]], [[], [9], [2, 2], [3, 1, 2], [1, 2, 1, 2], [3, 11], [1, 1, 1, 2, 1], [1, 1, 1, 1, 1, 1], [3, 1, 3, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 3, 1, 1], [3, 1, 1, 1, 1], [1, 1, 2, 1], [11], []], NN).
nn(13, NN) :-
	armarNono([[2], [1, 1], [1, 1], [1, 1], [1], [], [2], [1, 1], [1, 1], [1, 1], [1]], [[1], [1, 3], [3, 1, 1], [1, 1, 3], [3]], NN).
nn(14, NN) :-
	armarNono([[1, 1], [1, 1], [1, 1], [2]], [[2], [1, 1], [1, 1], [1, 1]], NN).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                              %
%    Predicados auxiliares     %
%        NO MODIFICAR          %
%                              %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! completar(+S)
%
% Indica que se debe completar el predicado. Siempre falla.
completar(S) :-
	write("COMPLETAR: "),
	write(S),
	nl,
	fail.

%! mostrarNono(+NN)
%
% Muestra una estructura nono(...) en pantalla
% Las celdas x (pintadas) se muestran como ██.
% Las o (no pintasdas) se muestran como ░░.
% Las no instanciadas se muestran como ¿?.
mostrarNono(nono(M, _)) :-
	mostrarMatriz(M).

%! mostrarMatriz(+M)
%
% Muestra una matriz. Solo funciona si las celdas
% son valores x, o, o no instanciados.
mostrarMatriz(M) :-
	M = [F|_],
	length(F, Cols),
	mostrarBorde('╔', Cols, '╗'),
	maplist(mostrarFila, M),
	mostrarBorde('╚', Cols, '╝').

mostrarBorde(I, N, F) :-
	write(I),
	stringRepeat('══', N, S),
	write(S),
	write(F),
	nl.

stringRepeat(_, 0, '').
stringRepeat(Str, N, R) :-
	N > 0,
	Nm1 is N - 1,
	stringRepeat(Str, Nm1, Rm1),
	string_concat(Str, Rm1, R).

%! mostrarFila(+M)
%
% Muestra una lista (fila o columna). Solo funciona si las celdas
% son valores x, o, o no instanciados.
mostrarFila(Fila) :-
	write('║'),
	maplist(mostrarCelda, Fila),
	write('║'),
	nl.

mostrarCelda(C) :-
	nonvar(C),
	C = x,
	write('██').
mostrarCelda(C) :-
	nonvar(C),
	C = o,
	write('░░').
mostrarCelda(C) :-
	var(C),
	write('¿?').
