-- Prove2me | solution 1 for ActuarialValuation.ctBackward_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:24:14.317504+00:00
-- url     : https://prove2.me/submissions/f494df78-ce60-4f47-9dc7-40f7d4e14c2e

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctBackward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (i : Fin 3) (k : ℝ) : ctBackward q (fun j => k*v j) i = k*ctBackward q v i := by
  unfold ctBackward
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring
