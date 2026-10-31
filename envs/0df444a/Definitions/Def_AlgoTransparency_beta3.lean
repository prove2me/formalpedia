-- Prove2me | Definitions.Def_AlgoTransparency_beta3
-- name    : AlgoTransparency_beta3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:44.52964+00:00
-- url     : https://prove2.me/theorems/6fb2d3c3-c40a-4cd2-a3db-651d16067c1f
-- title:
--   Threshold $\beta_3$ of eq. (15)
-- statement:
--   The threshold
--
--   $$
--   \beta_3=\frac{\lambda\theta\alpha-\theta\alpha-2\lambda\theta R+\theta R+\lambda R}{\lambda-2\theta\lambda+\theta} .
--   $$
--
--   The paper shows that it equals the upper bound $\bar\beta$ of Assumption 3.
--
--   **Formalization Note** The denominator equals $\theta(1-\lambda)+(1-\theta)\lambda$, positive under the standing assumptions.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (15), p.23 (PDF 24)

import Mathlib
import Definitions.Def_AlgoTransparency_Params

namespace AlgoTransparency

/-- **The threshold `β3`** of Wang, Huang, Jasin & Singh, arXiv:2008.09283v1, eq. (15), p.23
(PDF 24): `β3 = (λθα − θα − 2λθR + θR + λR)/(λ − 2θλ + θ)`.

**Formalization Note.** The denominator equals `θ(1 − λ) + (1 − θ)λ`, which is positive under the
standing assumptions. -/
noncomputable def beta3 (p : Params) : ℝ :=
  (p.lam * p.θ * p.α - p.θ * p.α - 2 * p.lam * p.θ * p.R + p.θ * p.R + p.lam * p.R) /
    (p.lam - 2 * p.θ * p.lam + p.θ)

end AlgoTransparency


