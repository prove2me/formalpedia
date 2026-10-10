-- Prove2me | solution 1 for ActuarialValuation.cm1IndependentJointSurvival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:06.096035+00:00
-- url     : https://prove2.me/submissions/a33463b5-0b7d-4e7a-b6a9-fc4cf7150bc1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1IndependentJointSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pX pY : ℕ → ℝ) (t : ℕ) (hx : 0 ≤ pX t) (hy : 0 ≤ pY t) : 0 ≤ cm1IndependentJointSurvival pX pY t := by
  unfold cm1IndependentJointSurvival
  exact mul_nonneg hx hy
