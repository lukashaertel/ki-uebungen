% The usable hours in the day
day(9, 20).

% Known events, with their durations
event(geldautomat, 1).
event((einkaufen; ki_vorlesung; ki_uebung), 2).
event(grillfeier, 3).

% Dependencies between events
dependency(grillfeier, einkaufen).
dependency(einkaufen, geldautomat).
dependency(ki_uebung, ki_vorlesung).

% Known start times
starttime(ki_vorlesung, 10; ki_uebung, 17).	
% The endtime is the start time plus the duration
endtime(X, S + D) :-
	starttime(X, S), event(X, D).

% The hours of a day that are occupied by an event
occupied(X, S .. (E - 1)) :-
	starttime(X, S), endtime(X, E).

% For a dependency from X to Y, X needs to happen after Y has ended
:-	dependency(X, Y), starttime(X, S), endtime(Y, E), S < E.

% An event may not happen outside of the hours of a day
:-	starttime(_, X), day(Y, _), X < Y.
:-	endtime(_, X), day(_, Y), X > Y.

% Two different events may not overlap
:-	occupied(X, T), occupied(Y, T), X != Y.

% Starttime of an event can be any time of the day, but only one assignment
{ starttime(X, Y) : Y = S .. (E - 1) } == 1 :-
	event(X, _),
	day(S, E).

#show starttime/2.