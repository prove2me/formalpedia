-- Prove2me | Definitions.Def_NearestDSM_bipGraph
-- name    : NearestDSM_bipGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:33.297038+00:00
-- url     : https://prove2.me/theorems/c1cadcd2-edf1-4e8f-adc4-f6e2b58dc351
-- title:
--   The bipartite row–column graph of a matrix
-- statement:
--   To every matrix $X\in\mathbb R^{m\times n}$ one associates a bipartite graph $G=(V,E)$ whose node set is split into $V_1$, the rows of $X$, and $V_2$, the columns of $X$. Row $i$ and column $j$ are joined by an edge exactly when
--   $$
--   X_{ij}\ne 0 .
--   $$
--   There are no edges between two rows or between two columns.
--
--   Connectivity of this graph governs the nonsingularity of $V(M)$ (Lemma 2.3) and the vertices of the equivalence classes (Theorem 3.10).
--
--   **Formalization Note** The node set is the disjoint union of the row and column index types: `Sum.inl a` is row $a$, `Sum.inr b` is column $b$.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, §2.1, p.7

import Mathlib

namespace NearestDSM

/-- The bipartite graph of a matrix, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, §2.1, p.7: "For every matrix
X ∈ ℝ^{m×n} we associate a bipartite graph G = (V, E) with node set divided into two V1, V2
corresponding to the rows and columns of X, respectively. The edges (i, j) ∈ E correspond to
nonzero entries of X".

**Formalization Note.** The node set is `m ⊕ k`: `Sum.inl a` is row `a`, `Sum.inr b` is column
`b`. Row `a` and column `b` are adjacent iff `M a b ≠ 0`; there are no row–row or column–column
edges. -/
def bipGraph {m k : Type*} (M : Matrix m k ℝ) : SimpleGraph (m ⊕ k) :=
  SimpleGraph.fromRel fun u v => ∃ a b, u = Sum.inl a ∧ v = Sum.inr b ∧ M a b ≠ 0

end NearestDSM


