-- Prove2me | Definitions.Def_KashUpgrade_typeCdf
-- name    : KashUpgrade_typeCdf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:06.578978+00:00
-- url     : https://prove2.me/theorems/76a1cdde-ca9c-4157-bd3c-207b9f5b1835
-- title:
--   The c.d.f. $F$ of the customer type
-- statement:
--   The cumulative distribution function of the customer type with density $f$:
--   $$
--   F(\theta)=\int_{u\le\theta} f(u)\,du .
--   $$
--   It is used throughout as the probability $1-F(\theta)$ that a customer's type exceeds $\theta$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), §3, p.9

import Mathlib

namespace KashUpgrade

/-- **The c.d.f. of the customer type.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), §3, p.9: `F` is the c.d.f. of the
density `f`, so `F θ = ∫_{u ≤ θ} f u du`. -/
noncomputable def typeCdf (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ u in Set.Iic θ, f u

end KashUpgrade


