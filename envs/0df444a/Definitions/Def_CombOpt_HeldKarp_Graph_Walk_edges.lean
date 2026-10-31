-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_Walk_edges
-- name    : CombOpt_HeldKarp_Graph_Walk_edges
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:30.854324+00:00
-- url     : https://prove2.me/theorems/6571d61e-517c-4163-a9b0-ce618eb6a111
-- title:
--   Edge terms of a path
-- statement:
--   For a path $P = v_0, e_1, v_1, \dots, e_k, v_k$, the list of its **edge terms** is $[e_1,\dots,e_k]$, in order and with repetitions.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_Walk

namespace CombOpt.HeldKarp

/-- **The edge terms of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10
(PDF p. 19): the edge terms e_1, …, e_k of a path v_0, e_1, v_1, …, e_k, v_k.

`p.edges` is the list `[e_1, …, e_k]`, in order and with repetitions. -/
def Graph.Walk.edges {V E : Type*} {G : Graph V E} : {u v : V} → G.Walk u v → List E
  | _, _, .nil _ => []
  | _, _, .cons e _ p => e :: p.edges

end CombOpt.HeldKarp


