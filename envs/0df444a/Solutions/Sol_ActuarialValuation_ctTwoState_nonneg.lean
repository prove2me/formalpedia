-- Prove2me | solution 1 for ActuarialValuation.ctTwoState_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:16:54.568013+00:00
-- url     : https://prove2.me/submissions/c730f85a-1485-4cbf-90ff-fdacd7cadd3d

import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctTwoState

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu t : ℝ) (hmu : 0 ≤ mu) (ht : 0 ≤ t) (i j : Fin 2) : 0 ≤ ctTwoState mu t i j := by
  have hmul : 0 ≤ mu * t := mul_nonneg hmu ht
  have hexp : Real.exp (-(mu * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr hmul
  have halive : 0 ≤ ctAlive mu t := by
    unfold ctAlive
    exact (Real.exp_pos _).le
  have hdead : 0 ≤ ctDead mu t := by
    unfold ctDead ctAlive
    apply sub_nonneg.mpr
    simpa only [neg_mul] using hexp
  fin_cases i <;> fin_cases j <;> simp [ctTwoState, halive, hdead]
