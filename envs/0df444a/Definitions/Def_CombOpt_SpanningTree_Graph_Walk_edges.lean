-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_Walk_edges
-- name    : CombOpt_SpanningTree_Graph_Walk_edges
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:46.748832+00:00
-- url     : https://prove2.me/theorems/f367745e-7665-40b9-bfa0-dcf5e1bf8680
-- title:
--   Edge terms of a path
-- statement:
--   For a path $P = v_0, e_1, v_1, \dots, e_k, v_k$, the list of its **edge terms** is $[e_1,\dots,e_k]$, in order and with repetitions. Its length $k$ is the **length** of $P$.
--
--   The path is **edge-simple** when this list has no repetition.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_Walk

namespace CombOpt.SpanningTree

/-- **The edge terms of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): the edge terms e_1, …, e_k of a path v_0, e_1, v_1, …, e_k, v_k;
"The length of P is k, the number of edge-terms of P."

`p.edges` is the list `[e_1, …, e_k]`, in order and with repetitions; its length is the length
of the path. -/
def Graph.Walk.edges {V E : Type*} {G : Graph V E} : {u v : V} → G.Walk u v → List E
  | _, _, .nil _ => []
  | _, _, .cons e _ p => e :: p.edges

end CombOpt.SpanningTree


