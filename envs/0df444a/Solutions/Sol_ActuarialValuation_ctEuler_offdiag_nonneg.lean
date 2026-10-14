-- Prove2me | solution 1 for ActuarialValuation.ctEuler_offdiag_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:12.702929+00:00
-- url     : https://prove2.me/submissions/dfeaf4a9-81ff-41b0-809c-1044b17ccb72

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctEuler

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i j : Fin 3) (hij : i ≠ j) (hr : 0 ≤ r i j) (hh : 0 ≤ h) : 0 ≤ ctEuler r h i j := by
  simp [ctEuler, ctGenerator, hij]
  exact mul_nonneg hh hr
