-- Prove2me | solution 1 for ActuarialValuation.nhTransition_row_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:04:07.949199+00:00
-- url     : https://prove2.me/submissions/58fe2be4-410c-4251-9e78-3cc57edaf519

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition
open ActuarialValuation

theorem solution(a b p s t : ℝ) (i : Fin 3) : (∑ j : Fin 3, nhTransition a b p s t i j)=1 := by
  fin_cases i <;> simp [Fin.sum_univ_three, nhTransition, nhExitOne, nhExitTwo] <;> ring
