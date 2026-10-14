-- Prove2me | solution 1 for ActuarialValuation.ctTwoState_alive_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:06:25.904016+00:00
-- url     : https://prove2.me/submissions/f25d1c48-2e78-4049-8fe1-084b30b7cdc4

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctTwoState

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu t : ℝ) : (∑ j : Fin 2, ctTwoState mu t 0 j) = 1 := by
  simp [Fin.sum_univ_two, ctTwoState, ctDead]
