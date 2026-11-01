-- Prove2me | Definitions.Def_RISRO_LopAdj
-- name    : RISRO_LopAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:31:43.438107+00:00
-- url     : https://prove2.me/theorems/b1fd3b0c-b863-4862-a381-1f46b064b0ce
-- title:
--   The adjoint $\mathcal L_t^*$
-- statement:
--   The adjoint of $\mathcal L_t$ sends $M\in\mathbb R^{p_1\times p_2}$ to
--
--   $$
--   \mathcal L_t^*(M)=\begin{bmatrix} U^\top MV & U^\top MV_\perp\\ U_\perp^\top MV & 0\end{bmatrix},
--   $$
--
--   recorded as the triple $(U^\top MV,\ U_\perp^\top MV,\ U^\top MV_\perp)$.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, p.8, displayed after (9)

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The adjoint `L_t^*(M) = [Uᵀ M V, Uᵀ M V_⊥; U_⊥ᵀ M V, 0]`, as the triple
`(Uᵀ M V, U_⊥ᵀ M V, Uᵀ M V_⊥)`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, p.8 (displayed after (9)). -/
def LopAdj {p₁ p₂ r : ℕ} (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (M : Matrix (Fin p₁) (Fin p₂) ℝ) : Triple p₁ p₂ r :=
  (Uᵀ * M * V, Ucᵀ * M * V, Uᵀ * M * Vc)

end RISRO


