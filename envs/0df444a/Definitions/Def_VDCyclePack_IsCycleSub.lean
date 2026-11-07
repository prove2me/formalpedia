-- Prove2me | Definitions.Def_VDCyclePack_IsCycleSub
-- name    : VDCyclePack_IsCycleSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:14.816179+00:00
-- url     : https://prove2.me/theorems/4ba4f7bf-7e6c-422d-90de-fb0bc1343e6b
-- title:
--   Cycle of a graph, identified with its subgraph
-- statement:
--   Let $G$ be a simple graph. A subgraph $C$ of $G$ is a **cycle** if it is the subgraph traced by a closed walk $v_0v_1\cdots v_{k-1}v_0$ of $G$ with $k\ge 3$ edges, no repeated edge and no repeated vertex other than the base point. As on p.9, a cycle is identified with its subgraph, independently of its starting vertex and orientation. Its **length** is $|C|=|V(C)|=|E(C)|\ge 3$.
--
--   Every object of the mission (fractional packings, cycle packings, contacts, candidates) is built on this notion.
--
--   **Formalization Note** A cycle is `p.toSubgraph` for a walk `p` with `p.IsCycle`. Rotations and the reversal of the walk trace the same subgraph, so each cycle of the paper is exactly one `C`.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.9

import Mathlib

namespace VDCyclePack

/-- **A cycle of a graph, identified with its subgraph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.9: "Paths and cycles are simple. We identify a cycle with its
subgraph, independently of its starting vertex and orientation. Its length is
|C| = |V (C)| = |E(C)|, which is at least three in a simple graph."

`IsCycleSub C` holds when the subgraph `C` of `G` is the subgraph traced by a closed walk of `G`
that is a cycle (`SimpleGraph.Walk.IsCycle`: at least three edges, no repeated edge and no
repeated vertex other than the base point).

**Formalization Note.** A cycle is the subgraph `p.toSubgraph` of a cycle walk `p`. Walks with
another base point or the other orientation trace the same subgraph, so each cycle of the paper
is exactly one `C`. Its length `|C|` is `C.verts.ncard`. -/
def IsCycleSub {V : Type*} {G : SimpleGraph V} (C : G.Subgraph) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph = C

end VDCyclePack


