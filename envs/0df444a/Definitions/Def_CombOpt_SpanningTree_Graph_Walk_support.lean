-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_Walk_support
-- name    : CombOpt_SpanningTree_Graph_Walk_support
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:58.026806+00:00
-- url     : https://prove2.me/theorems/c2cd5283-92a4-4df1-a078-1a36e6e7f6c9
-- title:
--   Node terms of a path
-- statement:
--   For a path $P = v_0, e_1, v_1, \dots, e_k, v_k$, the list of its **node terms** is $[v_0, v_1,\dots,v_k]$, in order and with repetitions.
--
--   The path is **simple** when this list has no repetition.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_Walk

namespace CombOpt.SpanningTree

/-- **The node terms of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): the node terms v_0, v_1, …, v_k of a path
v_0, e_1, v_1, …, e_k, v_k; the path is *simple* "if v_0, …, v_k are distinct".

`p.support` is the list `[v_0, v_1, …, v_k]`, in order and with repetitions; it has one more
entry than `p.edges`. -/
def Graph.Walk.support {V E : Type*} {G : Graph V E} : {u v : V} → G.Walk u v → List V
  | u, _, .nil _ => [u]
  | u, _, .cons _ _ p => u :: p.support

end CombOpt.SpanningTree


