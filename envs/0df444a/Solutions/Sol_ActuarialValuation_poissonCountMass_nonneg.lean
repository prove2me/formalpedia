-- Prove2me | solution 1 for ActuarialValuation.poissonCountMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T11:45:48.560443+00:00
-- url     : https://prove2.me/submissions/8fcd8757-c4ed-4adb-99c0-b31cf2856ba2

import Mathlib
import Definitions.Def_actuarial_poissonCountMass

open ActuarialValuation

theorem solution (rate : ℝ) (n : ℕ) (hr : 0 ≤ rate) : 0 ≤ poissonCountMass rate n := by
  unfold poissonCountMass
  positivity
