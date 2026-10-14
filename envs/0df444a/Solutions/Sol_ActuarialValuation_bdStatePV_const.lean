-- Prove2me | solution 1 for ActuarialValuation.bdStatePV_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:53.605172+00:00
-- url     : https://prove2.me/submissions/8b9b1550-e3c0-46eb-a25b-9a1f5f879289

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV
import Definitions.Def_actuarial_bdStateZeroBond

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p discount : Fin m → ℝ) (a : ℝ) : bdStatePV p discount (fun _ => a) = a * bdStateZeroBond p discount := by
  unfold bdStateZeroBond bdStatePV
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring
