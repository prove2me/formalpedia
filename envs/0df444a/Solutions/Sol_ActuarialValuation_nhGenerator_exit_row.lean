-- Prove2me | solution 1 for ActuarialValuation.nhGenerator_exit_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:33:47.830561+00:00
-- url     : https://prove2.me/submissions/66d5cc80-1384-43a4-8b3e-b05fcba8f402

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhGenerator

import Mathlib.Algebra.BigOperators.Fin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p t : ℝ) (i : Fin 3) (hi : i≠0) : (∑ j : Fin 3, nhGenerator a b p t i j)=0 := by
  simp only [Fin.sum_univ_three]
  fin_cases i <;> simp_all [nhGenerator]
