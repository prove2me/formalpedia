-- Prove2me | solution 1 for ActuarialValuation.ctTwoState_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:16:45.670185+00:00
-- url     : https://prove2.me/submissions/48b8f9b1-9580-4b7d-a8cb-1bad1fc965c7

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctTwoState
import Definitions.Def_actuarial_ctTwoStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu s t : ℝ) (i j : Fin 2) : ctTwoState mu (s+t) i j = ctTwoStep (ctTwoState mu s) (ctTwoState mu t) i j := by
  have hsurv : ctAlive mu (s+t) = ctAlive mu s * ctAlive mu t := by
    unfold ctAlive
    have hexp : -(mu * (s+t)) = -(mu*s) + -(mu*t) := by ring
    simp only [neg_mul]
    rw [hexp, Real.exp_add]
  fin_cases i <;> fin_cases j
  all_goals simp [ctTwoStep, Fin.sum_univ_two, ctTwoState, ctDead, hsurv] <;> ring
