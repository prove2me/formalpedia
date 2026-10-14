-- Prove2me | solution 1 for ActuarialValuation.ctGenerator_diag_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:32:34.883879+00:00
-- url     : https://prove2.me/submissions/a1e02452-4751-4748-8fba-0c8d39866998

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctGenerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (h : ∀ j, 0 ≤ r i j) : ctGenerator r i i ≤ 0 := by
  simp only [ctGenerator, ↓reduceIte]
  apply neg_nonpos.mpr
  unfold ctRateOut
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact le_refl _
  · exact h j
