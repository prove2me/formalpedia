-- Prove2me | Definitions.Def_RISRO_IsErrorTriple
-- name    : RISRO_IsErrorTriple
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:33:48.031161+00:00
-- url     : https://prove2.me/theorems/643e46ca-a76e-4b0c-b087-2bd26ae5ae78
-- title:
--   $w=(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t$
-- statement:
--   A triple $w$ is the **approximation error** of the $t$-th step when
--
--   $$
--   \mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t(w)=\mathcal L_t^*\mathcal A^*\epsilon^t .
--   $$
--
--   When $\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t$ is invertible on $\mathrm{Ran}(\mathcal L_t^*)$ there is exactly one such $w$, namely $(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t$, the right side of (11). Lemma 2 gives this invertibility under the $2r$-RIP.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, displays (11)-(12), p.8

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple
import Definitions.Def_RISRO_normalOp
import Definitions.Def_RISRO_LopAdj
import Definitions.Def_RISRO_epsT

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- `w = (L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t`, stated as the equation
`L_t^* A^* A L_t (w) = L_t^* A^* ϵ^t`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, displays (11)–(12), p.8.

Formalization Note: when `normalOp` is bijective (a hypothesis of Lemma 1, and a consequence of
`ripConst A (2 * r) < 1` by Lemma 2) exactly one `w` satisfies this equation, and it is the page's
`(L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t`. -/
def IsErrorTriple {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (Xbar : Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (w : Triple p₁ p₂ r) : Prop :=
  normalOp A U Uc V Vc w =
    LopAdj U Uc V Vc (observationOpAdjoint A (epsT A y Xbar Uc Vc))

end RISRO


