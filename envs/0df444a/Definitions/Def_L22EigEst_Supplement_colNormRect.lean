-- Prove2me | Definitions.Def_L22EigEst_Supplement_colNormRect
-- name    : L22EigEst_Supplement_colNormRect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:36:42.071202+00:00
-- url     : https://prove2.me/theorems/ea540275-eebb-4c9d-8f12-d3d0776f70d4
-- title:
--   The $1\to2$ norm $\|B\|_{1\to2}$ of a rectangular matrix (maximum column norm)
-- statement:
--   For a real $d\times n$ matrix $B$,
--
--   $$\|B\|_{1\to2}=\max_{j\in[n]}\Big(\sum_{i=1}^d B_{ij}^2\Big)^{1/2},$$
--
--   the largest Euclidean norm of a column of $B$. It is the operator norm from $\ell_1^n$ to $\ell_2^d$. In Theorem 10 it is applied to $AS^\intercal$, whose unsampled columns are zero, so it measures the largest rescaled sampled column.
--
--   **Formalization Note** A supremum over the finite column index; for $n=0$ the value is $0$. For $d=n$ it coincides by definition with the base mission's square `L22EigEst.colNorm12`.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Theorem 10, p.36 ("∥AS⊺∥1→2 is the maximum column norm of AS⊺")

import Mathlib

namespace L22EigEst.Supplement

/-- **The `1 → 2` norm of a rectangular matrix**, `‖B‖_{1→2} = max_j √(∑_i B_ij²)`, the maximum
Euclidean norm of a column of `B ∈ ℝ^{d×n}`.
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), Theorem 10, p.36:
"∥AS⊺∥1→2 is the maximum column norm of AS⊺".

**Formalization Note.** A supremum over the finite column index `Fin n`; for `n = 0` it is `0`. For
`d = n` it is, by definition, the base mission's square `L22EigEst.colNorm12`. -/
noncomputable def colNormRect {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℝ) : ℝ :=
  ⨆ j : Fin n, Real.sqrt (∑ i, B i j ^ 2)

end L22EigEst.Supplement


