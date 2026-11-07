-- Prove2me | Definitions.Def_SparseDisc_IsBlock
-- name    : SparseDisc_IsBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:09.059357+00:00
-- url     : https://prove2.me/theorems/39f57caa-4ce6-46fa-87cd-72b45283b916
-- title:
--   Block of a graph
-- statement:
--   A **block** of a graph $H$ is a maximal 2-connected subgraph or a bridge. Here a block is identified with its vertex set $W$: $W$ induces an edge or a 2-connected graph, and no strictly larger vertex set does.
--
--   **Formalization Note** Maximal 2-connected subgraphs are induced, and so is a bridge; an edge lying on a cycle is not maximal, since the cycle's vertex set is 2-connected. Isolated vertices, which form blocks without edges, carry no degree and are not represented.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 1.1, p.4: 'Here the blocks are the maximal 2-connected subgraphs and the bridges'

import Mathlib
import Definitions.Def_SparseDisc_IsBlockCandidate

namespace SparseDisc

/-- `IsBlock H W`: `H[W]` is a **block** of `H` with at least two vertices — a maximal 2-connected
subgraph or a bridge (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.4).

**Formalization Note** A block is identified with its vertex set `W`; maximal 2-connected
subgraphs are induced, and so is a bridge. `W` is ⊆-maximal among sets inducing an edge or a
2-connected graph: a non-bridge edge lies in a cycle and so is not maximal. Isolated vertices
(blocks with one vertex and no edge) carry no degree and are not represented. -/
def IsBlock {V : Type} [DecidableEq V] (H : SimpleGraph V) (W : Finset V) : Prop :=
  IsBlockCandidate H W ∧ ∀ W' : Finset V, W ⊆ W' → IsBlockCandidate H W' → W' = W

end SparseDisc


