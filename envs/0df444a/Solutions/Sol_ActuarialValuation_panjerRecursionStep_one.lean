-- Prove2me | solution 1 for ActuarialValuation.panjerRecursionStep_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:33:39.401727+00:00
-- url     : https://prove2.me/submissions/4bc9df1d-6739-4c43-a529-5a0aa1b02719

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g : ℕ → ℝ) : panjerRecursionStep lambda f g 1 = lambda / 2 * (f 1 * g 1 + 2 * f 2 * g 0) := by
  simp [panjerRecursionStep, panjerWeightedSeverity, Finset.sum_range_succ]
  ring
  all_goals simp
