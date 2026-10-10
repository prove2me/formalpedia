-- Prove2me | solution 1 for ActuarialValuation.cm1UDDFractionalSurvival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:19.578115+00:00
-- url     : https://prove2.me/submissions/8b1e0553-86e0-44dc-b004-31d337615385

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1UDDFractionalSurvival
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p s : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ cm1UDDFractionalSurvival p s := by
  unfold cm1UDDFractionalSurvival
  have h : p * (1-s) ≤ 1-s := by
    simpa using (mul_le_mul_of_nonneg_right hp1 (sub_nonneg.mpr hs1))
  linarith
