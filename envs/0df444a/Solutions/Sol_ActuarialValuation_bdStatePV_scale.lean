-- Prove2me | solution 1 for ActuarialValuation.bdStatePV_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:43.081351+00:00
-- url     : https://prove2.me/submissions/3d3be35b-14e5-48a0-8d1d-bc27ba402be3

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p discount X : Fin m → ℝ) (a : ℝ) : bdStatePV p discount (fun ω => a*X ω) = a*bdStatePV p discount X := by
  unfold bdStatePV
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring
