-- Prove2me | Definitions.Def_KashUpgrade_typeInterior
-- name    : KashUpgrade_typeInterior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:05.669679+00:00
-- url     : https://prove2.me/theorems/2336f1fe-87db-414a-a9c4-512dc6238bbd
-- title:
--   The interior $(0,\zeta)$ of the support
-- statement:
--   The open interval $(0,\zeta)$, on which the density of the customer type is positive and differentiable and on which the virtual valuation is defined.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Assumption 2, p.13

import Mathlib

namespace KashUpgrade

/-- **The interior `(0, ζ)` of the support.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Assumption 2, p.13. -/
def typeInterior (ζ : ENNReal) : Set ℝ :=
  {θ | 0 < θ ∧ ENNReal.ofReal θ < ζ}

end KashUpgrade


