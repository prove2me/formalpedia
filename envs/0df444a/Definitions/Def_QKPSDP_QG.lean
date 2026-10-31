-- Prove2me | Definitions.Def_QKPSDP_QG
-- name    : QKPSDP_QG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:49.426804+00:00
-- url     : https://prove2.me/theorems/574d3cd6-75b1-446e-b3d0-97c84b06c6a1
-- title:
--   The matrices $\mathcal Q(G)$ with the sparsity pattern of a graph
-- statement:
--   For a simple undirected graph $G$ on the vertex set $[n]$,
--
--   $$
--   \mathcal Q(G) := \{ A \in \mathbb S^n : \forall i \neq j,\ A_{ij} \neq 0 \iff ij \in E(G) \}. \qquad (18)
--   $$
--
--   These are the symmetric matrices whose off-diagonal sparsity pattern is the adjacency pattern of $G$; the diagonal is free.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (18), p.10

import Mathlib

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (18), p.10: for a simple undirected graph `G` on `[n]`,
`Q(G) := { A ∈ Sⁿ : ∀ i ≠ j, A_ij ≠ 0 ⇔ ij ∈ E(G) }`, the symmetric matrices whose off-diagonal
sparsity pattern is that of `G`.

**Formalization Note** `G` is `SimpleGraph (Fin n)`; `ij ∈ E(G)` is `G.Adj i j`; `A ∈ Sⁿ` is
`A.IsSymm`. The diagonal is unconstrained, as on the page. -/
def QG {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsSymm ∧ ∀ i j, i ≠ j → (A i j ≠ 0 ↔ G.Adj i j)}

end QKPSDP


