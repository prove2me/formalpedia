-- Prove2me | Definitions.Def_VDCyclePack_Represents
-- name    : VDCyclePack_Represents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:22.847043+00:00
-- url     : https://prove2.me/theorems/14df26f2-44e2-4b3c-b961-d7a5d7a16e99
-- title:
--   A vertex list represents a cycle of an encoded graph
-- statement:
--   A list $l=(v_1,\dots,v_k)$ of vertex indices **represents** the cycle $C$ of the encoded graph if some cycle walk of the graph visits $v_1,\dots,v_k$ in this order after its base point (and returns to it), and $C$ is the subgraph traced by this walk.
--
--   This is how algorithms read and write cycles.
--
--   **Formalization Note** The list determines the cycle; every rotation and the reversal of $l$ represent the same $C$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.1, p.11, and Theorem 4.2, p.12

import Mathlib
import Definitions.Def_VDCyclePack_GraphInst_toGraph

namespace VDCyclePack

/-- **A vertex list represents a cycle of an encoded graph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 4.1, p.11 ("an explicit list of polynomially many cycles"), Theorem 4.2, p.12
("an explicitly given family of cycles").

`Represents I l C` says there is a cycle walk `p` of `I.toGraph` whose vertices after the base point,
in order, are the entries of `l` (as numbers), and `C` is the subgraph traced by `p`.

**Formalization Note.** A cycle is output and input as its cyclic vertex sequence. The list
determines the walk, hence the subgraph `C`; every rotation and reversal of `l` represents the same
`C`. -/
def Represents (I : GraphInst) (l : List ℕ) (C : I.toGraph.Subgraph) : Prop :=
  ∃ (v : Fin I.n) (p : I.toGraph.Walk v v), p.IsCycle ∧ p.support.tail.map Fin.val = l ∧
    p.toSubgraph = C

end VDCyclePack


