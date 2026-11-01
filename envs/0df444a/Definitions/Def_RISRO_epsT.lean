-- Prove2me | Definitions.Def_RISRO_epsT
-- name    : RISRO_epsT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:49.807099+00:00
-- url     : https://prove2.me/theorems/adcf5e8c-519a-4980-8c60-b85f76c23d7d
-- title:
--   The residual $\epsilon^t$ of the regression model (6)
-- statement:
--   Given a target $\bar X$ and $\bar\epsilon=y-\mathcal A(\bar X)$, the residual of the sketched regression model is
--
--   $$
--   \epsilon^t=\mathcal A\bigl(P_{U_\perp}\bar XP_{V_\perp}\bigr)+\bar\epsilon,\qquad P_{U_\perp}=U_\perp U_\perp^\top,\quad P_{V_\perp}=V_\perp V_\perp^\top .
--   $$
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, display (6), p.7

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The residual `ϵ^t := A(P_{U_⊥} X̄ P_{V_⊥}) + ϵ̄` of the regression model (6), where
`ϵ̄ = y - A(X̄)`, `P_{U_⊥} = U_⊥ U_⊥ᵀ` and `P_{V_⊥} = V_⊥ V_⊥ᵀ`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, display (6), p.7. -/
def epsT {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (Xbar : Matrix (Fin p₁) (Fin p₂) ℝ)
    (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ) : Fin n → ℝ :=
  observationOp A (Uc * Ucᵀ * Xbar * (Vc * Vcᵀ)) + (y - observationOp A Xbar)

end RISRO


