-- Prove2me | solution 1 for ActuarialValuation.lcDriftIndex_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:34.149991+00:00
-- url     : https://prove2.me/submissions/c53d7326-78a1-4efe-a3d6-271106934987

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcDriftIndex

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial drift : ℝ) (m n : ℕ) :
    lcDriftIndex initial drift (m+n) =
      lcDriftIndex (lcDriftIndex initial drift m) drift n := by
  simp [lcDriftIndex, Nat.cast_add, add_mul, mul_add]
  ring
