-- Prove2me | solution 1 for ActuarialValuation.cm1SingleLifeAnnuity_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:01.890029+00:00
-- url     : https://prove2.me/submissions/a6080f3b-1d89-4015-b797-d3715dc522ed

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount survival : ℕ → ℝ) (n : ℕ) : cm1SingleLifeAnnuity discount survival (n+1) = cm1SingleLifeAnnuity discount survival n + discount n * survival n := by
  simp [cm1SingleLifeAnnuity, Finset.sum_range_succ]
