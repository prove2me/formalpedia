-- Prove2me | Definitions.Def_RISRO_Lop
-- name    : RISRO_Lop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:31:44.292924+00:00
-- url     : https://prove2.me/theorems/61119227-9bb9-4c69-8874-e228a2f48b96
-- title:
--   The operator $\mathcal L_t$
-- statement:
--   Given a frame $U,U_\perp$ of $\mathbb R^{p_1}$ and a frame $V,V_\perp$ of $\mathbb R^{p_2}$, the operator $\mathcal L_t$ of display (9) maps a triple $W=(W_0,W_1,W_2)$ to
--
--   $$
--   \mathcal L_t(W)=[U\ U_\perp]\begin{bmatrix} W_0 & W_2\\ W_1 & 0\end{bmatrix}[V\ V_\perp]^\top
--   =UW_0V^\top+U_\perp W_1V^\top+UW_2V_\perp^\top .
--   $$
--
--   Its image is the set of matrices the least squares step of RISRO searches over.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, display (9), p.7

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The operator `L_t` of (9): `[W₀ W₂; W₁ 0] ↦ [U U_⊥] [W₀ W₂; W₁ 0] [V V_⊥]ᵀ`, written out as
`U W₀ Vᵀ + U_⊥ W₁ Vᵀ + U W₂ V_⊥ᵀ`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, display (9), p.7. -/
def Lop {p₁ p₂ r : ℕ} (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (W : Triple p₁ p₂ r) : Matrix (Fin p₁) (Fin p₂) ℝ :=
  U * W.1 * Vᵀ + Uc * W.2.1 * Vᵀ + U * W.2.2 * Vcᵀ

end RISRO


