-- Prove2me | solution 1 for ActuarialValuation.nhGenerator_alive_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:33:35.584152+00:00
-- url     : https://prove2.me/submissions/be6bf25e-74ab-48cc-b0b3-01ff4c573cc0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhGenerator

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p t : ℝ) : (∑ j : Fin 3, nhGenerator a b p t 0 j)=0 := by
  simp only [Fin.sum_univ_three]
  simp [nhGenerator]
  ring
