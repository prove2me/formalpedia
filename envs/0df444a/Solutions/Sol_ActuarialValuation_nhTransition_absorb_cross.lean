-- Prove2me | solution 1 for ActuarialValuation.nhTransition_absorb_cross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:38:57.296112+00:00
-- url     : https://prove2.me/submissions/f51ec087-84e1-4cfa-8a83-14a16e5a69a4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition

import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p s t : ℝ) : nhTransition a b p s t 1 2=0 ∧ nhTransition a b p s t 2 1=0 := by
  constructor
  · simp [nhTransition, show (1 : Fin 3) ≠ (0 : Fin 3) by decide,
      show (1 : Fin 3) ≠ (2 : Fin 3) by decide]
  · simp [nhTransition, show (2 : Fin 3) ≠ (0 : Fin 3) by decide,
      show (2 : Fin 3) ≠ (1 : Fin 3) by decide]
