-- Prove2me | Definitions.Def_VDCyclePack_GraphInst_toGraph
-- name    : VDCyclePack_GraphInst_toGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:50.774183+00:00
-- url     : https://prove2.me/theorems/cb4d1634-b382-4497-a08c-4b1e87f47549
-- title:
--   The simple graph of an encoded instance
-- statement:
--   The simple graph on $\{0,\dots,n-1\}$ in which $i\ne j$ are adjacent when $(i,j)$ or $(j,i)$ is a listed pair.
--
--   **Formalization Note** Mathlib's `SimpleGraph.fromRel`, which symmetrizes and drops loops; pairs with an index $\ge n$ name no vertex.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_VDCyclePack_GraphInst

namespace VDCyclePack

/-- **The simple graph of an encoded instance.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 1.1, p.3 ("a finite simple undirected graph G").

`I.toGraph` is the simple graph on `Fin I.n` in which `i ≠ j` are adjacent when `(i, j)` or `(j, i)`
is in the edge list.

**Formalization Note.** `SimpleGraph.fromRel` symmetrizes and removes loops; out-of-range pairs
name no vertex and are ignored. -/
def GraphInst.toGraph (I : GraphInst) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel fun i j => (i.val, j.val) ∈ I.edges

end VDCyclePack


