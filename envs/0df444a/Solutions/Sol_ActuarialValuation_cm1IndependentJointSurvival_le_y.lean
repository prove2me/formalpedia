-- Prove2me | solution 1 for ActuarialValuation.cm1IndependentJointSurvival_le_y
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:04.264985+00:00
-- url     : https://prove2.me/submissions/ad98b357-0088-4927-b156-0f853f999234

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1IndependentJointSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pX pY : ℕ → ℝ) (t : ℕ) (hx : pX t ≤ 1) (hy : 0 ≤ pY t) : cm1IndependentJointSurvival pX pY t ≤ pY t := by
  unfold cm1IndependentJointSurvival
  simpa using (mul_le_mul_of_nonneg_right hx hy)
