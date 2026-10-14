-- Prove2me | solution 1 for ActuarialValuation.nhTransition_alive_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:34:29.974621+00:00
-- url     : https://prove2.me/submissions/ebc18461-4529-42c2-badc-a7425203ae45

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p s t : ℝ) : (∑ j : Fin 3, nhTransition a b p s t 0 j)=1 := by
  simp only [Fin.sum_univ_three]
  simp [nhTransition, nhExitOne, nhExitTwo]
  ring
