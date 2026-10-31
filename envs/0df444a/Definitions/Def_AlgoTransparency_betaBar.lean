-- Prove2me | Definitions.Def_AlgoTransparency_betaBar
-- name    : AlgoTransparency_betaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:58.112915+00:00
-- url     : https://prove2.me/theorems/c65d2f4b-416e-44a1-9add-1b4c865f132b
-- title:
--   Upper bound $\bar\beta$ of Assumption 3
-- statement:
--   The upper bound of Assumption 3,
--
--   $$
--   \bar\beta=R-\frac{\theta(1-\lambda)\alpha}{\theta(1-\lambda)+(1-\theta)\lambda} .
--   $$
--
--   Assumption 3 requires $\beta<\bar\beta$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, Assumption 3, p.16 (PDF 17)

import Mathlib
import Definitions.Def_AlgoTransparency_Params

namespace AlgoTransparency

/-- **The upper bound `β̄` of Assumption 3** of Wang, Huang, Jasin & Singh, arXiv:2008.09283v1,
p.16 (PDF 17): `β̄ = R − θ(1 − λ)α/(θ(1 − λ) + (1 − θ)λ)`. Assumption 3 requires `β < β̄`.

**Formalization Note.** The denominator is positive under the standing assumptions. -/
noncomputable def betaBar (p : Params) : ℝ :=
  p.R - p.θ * (1 - p.lam) * p.α / (p.θ * (1 - p.lam) + (1 - p.θ) * p.lam)

end AlgoTransparency


