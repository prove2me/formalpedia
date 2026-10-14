-- Prove2me | solution 1 for ActuarialValuation.panjerRecursionStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:29:12.945923+00:00
-- url     : https://prove2.me/submissions/3283a332-7129-48a0-94a1-d94a71f67cfb

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g : ℕ → ℝ) : panjerRecursionStep lambda f g 0 = lambda * f 1 * g 0 := by
  simp [panjerRecursionStep, panjerWeightedSeverity]
  ring
