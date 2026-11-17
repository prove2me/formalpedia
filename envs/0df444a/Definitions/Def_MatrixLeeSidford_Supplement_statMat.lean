-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_statMat
-- name    : MatrixLeeSidford_Supplement_statMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:12:39.293254+00:00
-- url     : https://prove2.me/theorems/9893ec3a-dbcf-4904-b3aa-228514efb70a
-- title:
--   Stationarity matrix $R_G(y)=L^\top L_y^*(L_y(G)^{s-1})L$
-- statement:
--   Let $y$ be feasible, $G\succ0$ a weight with Cholesky factor $L$, and let $L_y(G)=\sum_{i,j}G_{ij}B_iB_j$ and its trace adjoint $L_y^*(W)_{ij}=\frac12\operatorname{tr}[W(B_iB_j+B_jB_i)]$ be the maps of Definition 4.3 at $y$. The **stationarity matrix** at the query state $(y,G)$ is the $m\times m$ matrix
--   $$
--   R=R_G(y):=L^\top\,L_y^*\big(L_y(G)^{s-1}\big)\,L .
--   $$
--   At the optimal weight stationarity gives $R_{G_*(y)}(y)=I$; the algorithm's G-steps drive an estimate of $R$ toward $I$.
--
--   **Formalization Note** $L$ is the Cholesky factor of $G$, as printed; $s-1$ is a natural-number exponent ($s\ge2$ in Part II).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 8.1, p.53

import Mathlib
import Definitions.Def_MatrixLeeSidford_Lmap
import Definitions.Def_MatrixLeeSidford_Ladj
import Definitions.Def_MatrixLeeSidford_slack
import Definitions.Def_MatrixLeeSidford_Supplement_cholFactor

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **stationarity matrix** `R = R_G(y) := Lᵀ L_y^*(L_y(G)^{s−1}) L` at a query state `(y, G)`, where
`L` is the Cholesky factor of `G` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 8.1, p.53).

**Formalization Note** `L_y = Lmap A (S(y))` and `L_y^* = Ladj A (S(y))` are the published maps at the
slack `S(y)`; `L` is `cholFactor G`; the power `s − 1` is a natural-number matrix power (Part II has
`s ≥ 2`). -/
noncomputable def statMat {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (y : EuclideanSpace ℝ (Fin m))
    (G : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (cholFactor G)ᵀ * Ladj A (slack A C y) ((Lmap A (slack A C y) G) ^ (s - 1)) * cholFactor G

end MatrixLeeSidford.Supplement


