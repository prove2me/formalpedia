-- Prove2me | solution 1 for ActuarialValuation.lcDriftIndex_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:32.670459+00:00
-- url     : https://prove2.me/submissions/4987dd08-55bd-4d78-b106-6e26d748340a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcDriftIndex

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial drift : ℝ) (n : ℕ) :
    lcDriftIndex initial drift (n+1) = lcDriftIndex initial drift n + drift := by
  simp [lcDriftIndex, Nat.cast_add, mul_add, add_mul]
  ring
