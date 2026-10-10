-- Prove2me | solution 1 for ActuarialValuation.cm1LifeSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:02.579515+00:00
-- url     : https://prove2.me/submissions/96991857-6b70-47f5-b6f1-6775e991853b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x : ℕ) (hl : l x ≠ 0) : cm1LifeSurvival l x 0 = 1 := by
  simp [cm1LifeSurvival, hl]
