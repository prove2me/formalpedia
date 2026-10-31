-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_IsCircuit
-- name    : CombOpt_SpanningTree_Graph_IsCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:09.755725+00:00
-- url     : https://prove2.me/theorems/c761a4a0-430a-4f04-9ed3-56f4d130591a
-- title:
--   Circuit
-- statement:
--   A closed path $P = v_0, e_1, v_1, \dots, e_k, v_k$ (so $v_k = v_0$) is a **circuit** if
--
--   1. it is edge-simple: $e_1,\dots,e_k$ are distinct;
--   2. $v_0,\dots,v_{k-1}$ are distinct;
--   3. $k\ge 1$.
--
--   A loop is a circuit of length $1$, and two parallel edges form a circuit of length $2$.
--
--   **Formalization Note** Closedness is built into the type: the predicate is defined on paths from $v$ to $v$. Condition 2 says that the node list with its last entry removed has no repetition.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_Walk_edges
import Definitions.Def_CombOpt_SpanningTree_Graph_Walk_support

namespace CombOpt.SpanningTree

/-- **A circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): a path P = v_0, e_1, v_1, …, e_k, v_k "is closed if v_0 = v_k; it
is edge-simple if e_1, …, e_k are distinct; … it is a circuit if it is edge-simple and closed,
v_0, …, v_{k−1} are distinct, and k ≥ 1."

For a closed path `p` from `v` to `v`: `G.IsCircuit p` holds when its edges are distinct, its
nodes `v_0, …, v_{k−1}` (the support without its last entry `v_k = v_0`) are distinct, and it has
at least one edge.

**Formalization Note.** Closedness is the type `G.Walk v v`. A loop is a circuit of length 1 and
two parallel edges form a circuit of length 2, as the book's definition gives. -/
def Graph.IsCircuit {V E : Type*} (G : Graph V E) {v : V} (p : G.Walk v v) : Prop :=
  p.edges.Nodup ∧ p.support.dropLast.Nodup ∧ 1 ≤ p.edges.length

end CombOpt.SpanningTree


