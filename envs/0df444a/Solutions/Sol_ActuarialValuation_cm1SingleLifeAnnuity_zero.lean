-- Prove2me | solution 1 for ActuarialValuation.cm1SingleLifeAnnuity_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:22.592535+00:00
-- url     : https://prove2.me/submissions/5e1872a4-8653-4911-b81a-405bc19122be

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount survival : ℕ → ℝ) : cm1SingleLifeAnnuity discount survival 0 = 0 := by
  simp [cm1SingleLifeAnnuity]
