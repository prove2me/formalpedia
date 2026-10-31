-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_IsCircuit
-- name    : CombOpt_HeldKarp_Graph_IsCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:29.603988+00:00
-- url     : https://prove2.me/theorems/5255ff3b-2fe8-413e-bd83-eed909f005e8
-- title:
--   Circuit
-- statement:
--   A closed path $v_0, e_1, v_1, \dots, e_k, v_k$ (so $v_k=v_0$) is a **circuit** if its edges $e_1,\dots,e_k$ are distinct, its nodes $v_0,\dots,v_{k-1}$ are distinct, and $k\ge 1$.
--
--   A loop is a circuit of length $1$ and two parallel edges form a circuit of length $2$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_Walk_edges
import Definitions.Def_CombOpt_HeldKarp_Graph_Walk_support

namespace CombOpt.HeldKarp

/-- **A circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10
(PDF p. 19): a path P = v_0, e_1, v_1, …, e_k, v_k "is closed if v_0 = v_k; it is edge-simple if
e_1, …, e_k are distinct; … it is a circuit if it is edge-simple and closed, v_0, …, v_{k−1} are
distinct, and k ≥ 1."

For a closed path `p` from `v` to `v`, `G.IsCircuit p` holds when its edges are distinct, its nodes
`v_0, …, v_{k−1}` (the support without its last entry) are distinct, and it has at least one edge.

**Formalization Note.** Closedness is the type `G.Walk v v`. A loop is a circuit of length 1 and two
parallel edges form a circuit of length 2, as the book's definition gives. -/
def Graph.IsCircuit {V E : Type*} (G : Graph V E) {v : V} (p : G.Walk v v) : Prop :=
  p.edges.Nodup ∧ p.support.dropLast.Nodup ∧ 1 ≤ p.edges.length

end CombOpt.HeldKarp


