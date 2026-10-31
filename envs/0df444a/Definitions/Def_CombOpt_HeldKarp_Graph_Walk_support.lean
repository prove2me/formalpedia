-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_Walk_support
-- name    : CombOpt_HeldKarp_Graph_Walk_support
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:25.557841+00:00
-- url     : https://prove2.me/theorems/9326fe7e-fb1f-4d80-aed3-35628c56eb8d
-- title:
--   Node terms of a path
-- statement:
--   For a path $P = v_0, e_1, v_1, \dots, e_k, v_k$, the list of its **node terms** is $[v_0, v_1,\dots,v_k]$, in order and with repetitions.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_Walk

namespace CombOpt.HeldKarp

/-- **The node terms of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10
(PDF p. 19): the node terms v_0, v_1, …, v_k of a path v_0, e_1, v_1, …, e_k, v_k.

`p.support` is the list `[v_0, v_1, …, v_k]`, in order and with repetitions; it has one more entry
than `p.edges`. -/
def Graph.Walk.support {V E : Type*} {G : Graph V E} : {u v : V} → G.Walk u v → List V
  | u, _, .nil _ => [u]
  | u, _, .cons _ _ p => u :: p.support

end CombOpt.HeldKarp


