-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_cholFactor
-- name    : MatrixLeeSidford_Supplement_cholFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:11:07.865198+00:00
-- url     : https://prove2.me/theorems/7f90a453-e85f-4fea-9556-b870bb442e6f
-- title:
--   Cholesky factor $L=\operatorname{chol}(G)$, $G=LL^\top$
-- statement:
--   For a positive definite $m\times m$ matrix $G$, its **Cholesky factor** $L=\operatorname{chol}(G)$ is the lower triangular matrix with positive diagonal entries such that
--   $$
--   G=LL^\top .
--   $$
--   It enters the stationarity matrix $R$ and the gradient matrix $M$ of Definition 8.1 and the damped inverse update (8.2) of the weight.
--
--   **Formalization Note** The factor is selected by choice among the lower triangular matrices with positive diagonal and $LL^\top=G$; it exists (and is unique) when $G\succ0$. On an input with no such factor the value is the junk matrix $0$; every use in this mission is at a positive definite $G$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 8.1, p.53; Algorithm 8, line 2, p.82

import Mathlib

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **Cholesky factor** `L = chol(G)` of a positive definite `G`: the lower triangular matrix
with positive diagonal and `G = L Lᵀ` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 8.1, p.53, "For G ≻ 0 with Cholesky
factor L"; Algorithm 8, line 2, p.82, "L = chol(G)").

**Formalization Note** Defined by choice: if some `L` is lower triangular (`L i j = 0` for
`i < j`), has positive diagonal and satisfies `L * Lᵀ = G`, `cholFactor G` is one such `L`
(it is unique, a theorem not used here); otherwise it is the junk value `0`. Every use in this
mission is at a positive definite `G`, where the factor exists. -/
noncomputable def cholFactor {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  open Classical in
  if h : ∃ L : Matrix (Fin m) (Fin m) ℝ,
      (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ L * Lᵀ = G then
    h.choose
  else 0

end MatrixLeeSidford.Supplement


