-- Prove2me | solution 1 for ActuarialValuation.ctEuler_diag_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:00.552443+00:00
-- url     : https://prove2.me/submissions/6c06fa2e-046d-4951-bb8f-dd523855fa31

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRateOut
import Definitions.Def_actuarial_ctEuler

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i : Fin 3) (hs : h*ctRateOut r i ≤ 1) : 0 ≤ ctEuler r h i i := by
  simp only [ctEuler, ctGenerator, ↓reduceIte]
  linarith
