-- Prove2me | solution 1 for ActuarialValuation.nhTransition_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:43:30.334935+00:00
-- url     : https://prove2.me/submissions/6dbf2c7c-354f-4765-b558-f75fe1c84817

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition
import Definitions.Def_actuarial_nhCompose

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p s u t : ℝ) (i j : Fin 3) : nhTransition a b p s t i j=nhCompose (nhTransition a b p s u) (nhTransition a b p u t) i j := by
  have hsurv : nhSurvival a b s t =
      nhSurvival a b s u * nhSurvival a b u t := by
    unfold nhSurvival
    rw [← Real.exp_add]
    congr 1
    ring
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i <;> fin_cases j <;>
    simp [nhCompose, Fin.sum_univ_three, nhTransition,
      nhExitOne, nhExitTwo, h01, h02, h10, h12, h20, h21,
      hsurv] <;> ring
