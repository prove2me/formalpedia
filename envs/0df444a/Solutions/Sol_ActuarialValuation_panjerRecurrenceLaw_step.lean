-- Prove2me | solution 1 for ActuarialValuation.panjerRecurrenceLaw_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:55.168773+00:00
-- url     : https://prove2.me/submissions/07a7fffd-6700-4ca0-9637-199834eb96fc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep
import Definitions.Def_actuarial_panjerRecurrenceLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g : ℕ → ℝ) (h : panjerRecurrenceLaw lambda f g) (k : ℕ) : g (k+1) = panjerRecursionStep lambda f g k := by
  exact h.2 k
