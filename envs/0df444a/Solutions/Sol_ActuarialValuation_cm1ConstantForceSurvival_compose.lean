-- Prove2me | solution 1 for ActuarialValuation.cm1ConstantForceSurvival_compose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:16.37984+00:00
-- url     : https://prove2.me/submissions/b1a0d968-c35f-434f-b519-7d21e84d29cf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ConstantForceSurvival
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ s t : ℝ) : cm1ConstantForceSurvival μ (s+t) = cm1ConstantForceSurvival μ s * cm1ConstantForceSurvival μ t := by
  unfold cm1ConstantForceSurvival
  rw [show -μ * (s+t) = -μ*s + -μ*t by ring, Real.exp_add]
