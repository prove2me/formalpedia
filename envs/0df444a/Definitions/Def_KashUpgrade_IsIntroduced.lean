-- Prove2me | Definitions.Def_KashUpgrade_IsIntroduced
-- name    : KashUpgrade_IsIntroduced
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:03.500555+00:00
-- url     : https://prove2.me/theorems/5852dc4a-49ab-4d76-8ce9-660290e910c3
-- title:
--   Class $i$ exists in the schedule
-- statement:
--   Technology class $i$ exists in the schedule if $i\le J$. Class $0$ encodes opting out and always exists.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (1), p.10

import Mathlib
import Definitions.Def_KashUpgrade_Schedule

namespace KashUpgrade

/-- **Technology class `i` exists in the schedule.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (1), p.10. Class `0` (opting out) always
exists. -/
def IsIntroduced (S : Schedule) (i : ℕ) : Prop :=
  (i : ℕ∞) ≤ S.J

end KashUpgrade


