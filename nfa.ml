open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let check_transition transition starting_state symbol = 
  fold_left(fun default elem -> match elem with 
  | (a, None, b) -> if a = starting_state && symbol = None then default@[b]
  else default
  | (a, Some x, b) -> if a = starting_state && symbol = Some x then default@[b]
  else default) [] transition

let get_value x = match x with
| Some a -> a
| None -> failwith "Can't get value for None"

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  if s != None && not (elem (get_value s) (nfa.sigma)) then []
  else fold_left(fun default elem -> union default (check_transition nfa.delta elem s)) [] qs

let rec e_helper nfa starting_states =
let transition = move nfa starting_states None in 
if eq (union starting_states transition) starting_states then starting_states
else e_helper nfa (union starting_states transition)

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list = e_helper nfa qs

let rec accept_helper nfa start_state char_lst =
match char_lst with
| [] -> if intersection start_state nfa.fs != [] then true else false
| a::b ->  if move nfa (e_closure nfa start_state) (Some a) = [] then false
else accept_helper nfa (e_closure nfa (move nfa (e_closure nfa start_state) (Some a))) b

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  if s = "" then (intersection (e_closure nfa [nfa.q0]) nfa.fs) != []
  else accept_helper nfa [nfa.q0] (explode s)

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  fold_left(fun default elem -> union default [e_closure nfa (move nfa qs (Some elem) ) ]) [] nfa.sigma


let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  fold_left(fun default elem -> default@[(qs, Some elem, e_closure nfa (move nfa qs (Some elem)))]) [] nfa.sigma
  

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  if (intersection qs nfa.fs) != [] then [qs] else []


let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
 match work with
 | [] -> dfa
 | a::b -> let unvisited = diff (new_states nfa a) (dfa.qs) in 
 let built_dfa = {
  sigma = nfa.sigma;
  qs = union (new_states nfa a) dfa.qs;
  q0 = e_closure nfa [nfa.q0];
  fs = union dfa.fs (new_finals nfa a);
  delta = union dfa.delta (new_trans nfa a);
 } in nfa_to_dfa_step nfa built_dfa (union b unvisited)



let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let dfa = {
    sigma = nfa.sigma;
    qs = [e_closure nfa [nfa.q0]];
    q0 = e_closure nfa [nfa.q0];
    fs = [];
    delta = [];
    } in nfa_to_dfa_step nfa dfa [dfa.q0]
   
