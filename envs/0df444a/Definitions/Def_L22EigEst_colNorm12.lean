-- Prove2me | Definitions.Def_L22EigEst_colNorm12
-- name    : L22EigEst_colNorm12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:15:22.484395+00:00
-- url     : https://prove2.me/theorems/e9f19bb9-c7fe-4bff-9375-50e64db48fc9
-- title:
--   The $1\to2$ norm $\|B\|_{1\to2}$ (maximum column norm)
-- statement:
--   For a real $n\times n$ matrix $B$,
--
--   $$\|B\|_{1\to2}=\max_{j}\Big(\sum_i B_{ij}^2\Big)^{1/2},$$
--
--   the largest Euclidean norm of a column. It is the operator norm from $\ell_1$ to $\ell_2$. In the Rudelson–Vershynin bound (Theorem 10) and in Lemmas 4.10 and 4.11 it measures the largest sampled column.
--
--   **Formalization Note** For $n=0$ the value is $0$.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), p.17 and Theorem 10, p.36

import Mathlib

namespace L22EigEst

/-- **The `1 → 2` norm** `‖B‖_{1→2}`: the maximum Euclidean norm of a column,
`max_j √(∑_i B_ij²)`. Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), p.17
("∥H_L S⊺∥²_{1→2} the maximum squared norm of the sampled columns") and Theorem 10, p.36 ("∥AS⊺∥_{1→2}
is the maximum column norm of AS⊺").

**Formalization Note.** A supremum over the finite column index; for `n = 0` it is `0`. -/
noncomputable def colNorm12 {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ j : Fin n, Real.sqrt (∑ i, B i j ^ 2)

end L22EigEst


