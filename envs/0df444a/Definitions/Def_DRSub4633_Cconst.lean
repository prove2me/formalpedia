-- Prove2me | Definitions.Def_DRSub4633_Cconst
-- name    : DRSub4633_Cconst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:07:23.931992+00:00
-- url     : https://prove2.me/theorems/e52e3d2c-bd5d-4303-b67f-930f630c6bef
-- title:
--   The constant term $C(t)$
-- statement:
--   $$C(t)=\Lambda(q_m)y(t)-bS_0(t)-\vartheta(q_1)E(t)-\sum_{i=1}^{m-1}[\vartheta(q_{i+1})-\vartheta(q_i)]Y_i(t).$$
--   It is the centered intercept of the large-coordinate comparison (31).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.5, Eq. (32), p.16

import Mathlib
import Definitions.Def_DRSub4633_Ypath
import Definitions.Def_DRSub4633_S0path
import Definitions.Def_DRSub4633_LamFun
import Definitions.Def_DRSub4633_varthetaFun
import Definitions.Def_DRSub4633_qAt
import Definitions.Def_DRSub4633_mLarge
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The constant term `C(t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.5, Eq. (32), p.16:
`C(t) = Λ(q_m)y(t) − bS₀(t) − ϑ(q₁)E(t) − ∑_(i=1)^(m−1) [ϑ(qᵢ₊₁) − ϑ(qᵢ)]Yᵢ(t)`. -/
noncomputable def Cconst {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : ℝ :=
  LamFun (qAt x (mLarge x)) * Ypath f x (mLarge x) t - bPar * S0path f x t
    - varthetaFun (qAt x 1) * Ypath f x 0 t
    - ∑ i ∈ Finset.Ico 1 (mLarge x),
        (varthetaFun (qAt x (i + 1)) - varthetaFun (qAt x i)) * Ypath f x i t

end DRSub4633


