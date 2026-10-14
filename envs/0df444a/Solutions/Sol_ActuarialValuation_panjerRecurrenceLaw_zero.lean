-- Prove2me | solution 1 for ActuarialValuation.panjerRecurrenceLaw_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:44.525345+00:00
-- url     : https://prove2.me/submissions/5f888f4b-4c00-4bf2-b4d7-95256524ffab

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecurrenceLaw
import Definitions.Def_actuarial_panjerPoissonZero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g : ℕ → ℝ) (h : panjerRecurrenceLaw lambda f g) : g 0 = panjerPoissonZero lambda := by
  simpa only [panjerPoissonZero] using h.1
