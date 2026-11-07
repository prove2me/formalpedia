-- Prove2me | Definitions.Def_SparseDisc_IsSubdivision
-- name    : SparseDisc_IsSubdivision
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:29.680249+00:00
-- url     : https://prove2.me/theorems/5fc5a61d-0c41-4762-b00c-b161da0ba0d8
-- title:
--   Pattern obtained by subdividing every edge
-- statement:
--   A graph $H$ is **obtained by subdividing every edge** if it is isomorphic to a subdivision $S_k(G_0)$ of some simple graph $G_0$ in which every edge is subdivided at least once.
--
--   **Formalization Note** Each edge may be subdivided one or more times. This covers both readings of the page's phrase: every edge subdivided exactly once ($k \equiv 0$) and every edge subdivided at least once.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9(b), p.5

import Mathlib
import Definitions.Def_SparseDisc_subdivide

namespace SparseDisc

/-- `IsSubdivision H`: `H` is (isomorphic to) a graph obtained from some simple graph by
subdividing every edge, each edge at least once (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Theorem 1.9(b), p.5:
"patterns obtained by subdividing every edge").

**Formalization Note** Every edge `e` of the original graph `G₀` is replaced by a path through
`k(e) + 1 ≥ 1` new vertices (`subdivide G₀ k`). This covers both readings of the page's phrase:
subdividing every edge exactly once (`k ≡ 0`) and subdividing every edge one or more times. -/
def IsSubdivision {V : Type} (H : SimpleGraph V) : Prop :=
  ∃ (W : Type) (G₀ : SimpleGraph W) (k : G₀.edgeSet → ℕ), Nonempty (H ≃g subdivide G₀ k)

end SparseDisc


