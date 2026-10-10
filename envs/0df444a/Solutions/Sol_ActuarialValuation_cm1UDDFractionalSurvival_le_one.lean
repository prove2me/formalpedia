-- Prove2me | solution 1 for ActuarialValuation.cm1UDDFractionalSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:32:21.249209+00:00
-- url     : https://prove2.me/submissions/164937b1-8879-455e-b0c9-58cd5fe56e7e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1UDDFractionalSurvival
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p s : ℝ) (hp : p ≤ 1) (hs : 0 ≤ s) : cm1UDDFractionalSurvival p s ≤ 1 := by
  unfold cm1UDDFractionalSurvival
  have h : 0 ≤ s * (1 - p) :=
    mul_nonneg hs (sub_nonneg.mpr hp)
  linarith
