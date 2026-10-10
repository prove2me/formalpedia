-- Prove2me | solution 1 for ActuarialValuation.cm1LifeMortality_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:30.978036+00:00
-- url     : https://prove2.me/submissions/4f5f948d-9274-4c5f-b933-fb16d71f7122

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeMortality
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x : ℕ) (hl : l x ≠ 0) : cm1LifeMortality l x 0 = 0 := by
  simp [cm1LifeMortality, cm1LifeSurvival, hl]
