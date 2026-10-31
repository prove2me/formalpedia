-- Prove2me | Definitions.Def_AlgoTransparency_beta1
-- name    : AlgoTransparency_beta1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:58.8375+00:00
-- url     : https://prove2.me/theorems/30d0ccd1-2b02-4162-9231-e1b852b11a27
-- title:
--   Threshold $\beta_1$ of eq. (13)
-- statement:
--   The threshold
--
--   $$
--   \beta_1=\lambda\theta(\alpha-R)-(1-\lambda)(1-\theta)R+R-\theta\alpha .
--   $$
--
--   In region $C_1$ the firm prefers the transparent algorithm exactly when $\beta>\beta_1$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (13), p.23 (PDF 24)

import Mathlib
import Definitions.Def_AlgoTransparency_Params

namespace AlgoTransparency

/-- **The threshold `β1`** of Wang, Huang, Jasin & Singh, arXiv:2008.09283v1, eq. (13), p.23
(PDF 24): `β1 = λθ(α − R) − (1 − λ)(1 − θ)R + R − θα`. In region C1 the firm prefers transparency
iff `β > β1`. -/
def beta1 (p : Params) : ℝ :=
  p.lam * p.θ * (p.α - p.R) - (1 - p.lam) * (1 - p.θ) * p.R + p.R - p.θ * p.α

end AlgoTransparency


