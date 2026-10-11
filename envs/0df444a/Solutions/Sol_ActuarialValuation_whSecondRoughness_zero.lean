-- Prove2me | solution 1 for ActuarialValuation.whSecondRoughness_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:09:18.17118+00:00
-- url     : https://prove2.me/submissions/134d1f2c-963f-499c-ad47-41e18061d4a5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondRoughness
open ActuarialValuation

theorem solution(g : ℕ → ℝ) : whSecondRoughness g 0 = 0 := by
  simp [whSecondRoughness]
