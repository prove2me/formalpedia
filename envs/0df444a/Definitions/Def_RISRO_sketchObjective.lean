-- Prove2me | Definitions.Def_RISRO_sketchObjective
-- name    : RISRO_sketchObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:31:01.038535+00:00
-- url     : https://prove2.me/theorems/77a641c7-0181-4330-a6c7-991389a27bb6
-- title:
--   The sketched least squares objective (5)
-- statement:
--   Given frames $U,U_\perp$ and $V,V_\perp$, the importance-sketched covariate maps of display (4) are
--
--   $$
--   [\mathcal A_B(\cdot)]_i=\langle\cdot,U^\top A_iV\rangle,\quad [\mathcal A_{D_1}(\cdot)]_i=\langle\cdot,U_\perp^\top A_iV\rangle,\quad [\mathcal A_{D_2}(\cdot)]_i=\langle\cdot,U^\top A_iV_\perp\rangle ,
--   $$
--
--   and the objective of problem (5) is, for $B\in\mathbb R^{r\times r}$, $D_1\in\mathbb R^{(p_1-r)\times r}$, $D_2\in\mathbb R^{(p_2-r)\times r}$,
--
--   $$
--   \bigl\|y-\mathcal A_B(B)-\mathcal A_{D_1}(D_1)-\mathcal A_{D_2}(D_2^\top)\bigr\|_2^2 .
--   $$
--
--   **Formalization Note.** The Euclidean norm of $\mathbb R^n$ is written out as a sum of squares.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Algorithm 1, steps 3-4, displays (4)-(5), p.6

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The objective of the dimension-reduced least squares problem (5),
`‖y - A_B(B) - A_{D₁}(D₁) - A_{D₂}(D₂ᵀ)‖₂²`, with the importance-sketched covariate maps (4):
`[A_B(·)]_i = ⟨·, Uᵀ A_i V⟩`, `[A_{D₁}(·)]_i = ⟨·, U_⊥ᵀ A_i V⟩`, `[A_{D₂}(·)]_i = ⟨·, Uᵀ A_i V_⊥⟩`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Algorithm 1, steps 3–4, displays (4)–(5), p.6.

Formalization Note: the Euclidean norm of `ℝⁿ` is written out as a sum of squares. -/
def sketchObjective {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (D₁ : Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (D₂ : Matrix (Fin (p₂ - r)) (Fin r) ℝ) : ℝ :=
  ∑ i, (y i - traceInner B (Uᵀ * A i * V) - traceInner D₁ (Ucᵀ * A i * V)
    - traceInner D₂ᵀ (Uᵀ * A i * Vc)) ^ 2

end RISRO


