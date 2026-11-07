-- Prove2me | Definitions.Def_FreeSpencer_lift
-- name    : FreeSpencer_lift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:59.28226+00:00
-- url     : https://prove2.me/theorems/c27ccd7d-e6c7-4784-95de-d6a9c1de5886
-- title:
--   The signed blocks $\hat A_i$ and the center $H(x)$
-- statement:
--   The signed block matrix $\hat A=\mathrm{diag}(A,-A)$ of order $D=2m$, the family $\hat A_1,\dots,\hat A_n$, and the center
--   $$H(x)=\sum_i x_i\hat A_i,$$
--   so that $\lambda_{\max}(H(x))=\|\sum_i x_iA_i\|$.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.18

import Mathlib

namespace FreeSpencer

/-- The signed block matrix `Â = diag(A, -A)`, of order `D = 2m`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.18. -/
def lift {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks A 0 0 (-A)

/-- The family `Â₁, …, Âₙ`. -/
def liftFam {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) :
    Fin n → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  fun i => lift (A i)

/-- The center `H(x) = ∑ᵢ xᵢ Âᵢ`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.18. -/
noncomputable def center {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  ∑ i, x i • lift (A i)

end FreeSpencer


