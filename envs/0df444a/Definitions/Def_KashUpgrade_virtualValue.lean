-- Prove2me | Definitions.Def_KashUpgrade_virtualValue
-- name    : KashUpgrade_virtualValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:12.831879+00:00
-- url     : https://prove2.me/theorems/ed645d78-aa2a-424d-b4d7-ab3f86b531e3
-- title:
--   The virtual valuation $v$
-- statement:
--   The virtual valuation function
--   $$
--   v(\theta):=\theta-\frac{1-F(\theta)}{f(\theta)} .
--   $$
--   Under Assumption 2 it is strictly increasing on the support.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), §4.1, p.13

import Mathlib
import Definitions.Def_KashUpgrade_typeCdf

namespace KashUpgrade

/-- **The virtual valuation.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), §4.1, p.13: `v θ := θ - (1 - F θ) / f θ`. -/
noncomputable def virtualValue (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  θ - (1 - typeCdf f θ) / f θ

end KashUpgrade


