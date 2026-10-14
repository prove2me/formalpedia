-- Prove2me | solution 1 for ActuarialValuation.cxRiskDenom_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:39:39.378203+00:00
-- url     : https://prove2.me/submissions/9633465f-5778-4098-9018-6fc5280dc79b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskDenom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (r1 r2 : Finset (Fin n)) (z : Fin n → ℝ) (h : r1⊆r2) : cxRiskDenom beta r1 z≤cxRiskDenom beta r2 z := by
  unfold cxRiskDenom
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro j hj hjnot
  unfold cxRelativeRisk
  exact (Real.exp_pos _).le
