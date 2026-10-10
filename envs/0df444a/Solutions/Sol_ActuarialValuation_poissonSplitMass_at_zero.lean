-- Prove2me | solution 1 for ActuarialValuation.poissonSplitMass_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:32:13.601525+00:00
-- url     : https://prove2.me/submissions/9c78dd61-ab4d-4f85-9456-856703ad6719

import Mathlib
import Definitions.Def_actuarial_poissonSplitJointMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (selection : ℝ) (a b : ℕ) (h : 0 < a + b) :
    poissonSplitJointMass 0 selection a b = 0 := by
  have hne : a + b ≠ 0 := Nat.ne_of_gt h
  dsimp [poissonSplitJointMass, poissonCountMass]
  rw [zero_pow hne]
  simp
