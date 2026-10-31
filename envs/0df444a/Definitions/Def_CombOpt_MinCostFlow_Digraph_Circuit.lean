-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit
-- name    : CombOpt_MinCostFlow_Digraph_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:04.626081+00:00
-- url     : https://prove2.me/theorems/7ea2a39c-3820-43a2-aa39-1deb7097d807
-- title:
--   Circuit of a digraph, with arc orientations
-- statement:
--   A **path** in a digraph is a sequence $v_0,e_1,v_1,\dots,e_k,v_k$ of nodes and arcs in which the ends of $e_i$ are $v_{i-1}$ and $v_i$; directions are ignored. It is a **circuit** if it is closed ($v_0=v_k$), its arcs $e_1,\dots,e_k$ are distinct, the nodes $v_0,\dots,v_{k-1}$ are distinct, and $k\ge1$. An arc $e_i$ is **forward** if it goes from $v_{i-1}$ to $v_i$ and **reverse** if it goes from $v_i$ to $v_{i-1}$.
--
--   A circuit here records its length $k$, its nodes, its arcs and, for each arc, whether it is traversed forward.
--
--   **Formalization Note** For an arc that is not a loop, the orientation is determined by the node sequence. A loop may be recorded as forward or as reverse; the book's wording makes a loop always forward. This only matters for Theorem 4.2, where it is declared as a correction.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19); §2.2, p. 19 (PDF p. 28)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

namespace CombOpt.MinCostFlow

/-- **A circuit of a digraph, with the orientation of each arc.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): a path P : v_0, e_1, v_1, …, e_k, v_k (the ends of e_i are
v_{i−1} and v_i) "is a *circuit* if it is edge-simple and closed, v_0, …, v_{k−1} are distinct,
and k ≥ 1"; §2.2, p. 19 (PDF p. 28): paths of a digraph are paths of the underlying graph, and
"an arc e_i of a path P … is *forward* if t(e_i) = v_{i−1} and h(e_i) = v_i, and is *reverse*
otherwise".

A `G.Circuit` consists of a length `k ≥ 1`, nodes `node 0, …, node k` with `node 0 = node k` and
`node 0, …, node (k−1)` distinct, pairwise distinct arcs `arc 0, …, arc (k−1)`, and a flag
`forward i`: if it is `true`, `arc i` goes from `node i` to `node (i+1)`; if `false`, it goes from
`node (i+1)` to `node i`.

**Formalization Note.** Indices start at `0` (the book's `e_i` is `arc (i−1)`). For an arc that
is not a loop the flag is determined by the node sequence and agrees with the book's
forward/reverse. For a loop both flags are allowed, i.e. a loop may be traversed in reverse; under
the book's literal wording a loop is always forward. This matters only for Theorem 4.2, where it is
recorded as a correction. -/
structure Digraph.Circuit {V E : Type*} (G : Digraph V E) where
  /-- The number `k ≥ 1` of arcs. -/
  length : ℕ
  one_le_length : 1 ≤ length
  /-- The node sequence `v_0, …, v_k`. -/
  node : Fin (length + 1) → V
  /-- The arc sequence `e_1, …, e_k` (indexed from `0`). -/
  arc : Fin length → E
  /-- Whether each arc is traversed forward (tail to head). -/
  forward : Fin length → Bool
  closed : node 0 = node (Fin.last length)
  arc_injective : Function.Injective arc
  node_injective : ∀ i j : Fin (length + 1), (i : ℕ) < length → (j : ℕ) < length →
    node i = node j → i = j
  incident : ∀ i : Fin length,
    (forward i = true → G.tail (arc i) = node i.castSucc ∧ G.head (arc i) = node i.succ) ∧
    (forward i = false → G.head (arc i) = node i.castSucc ∧ G.tail (arc i) = node i.succ)

end CombOpt.MinCostFlow


