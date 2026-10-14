-- Prove2me | solution 1 for ActuarialValuation.ruMean_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:12:41.449009+00:00
-- url     : https://prove2.me/submissions/dd86873f-a115-400c-a0ff-f6733301c400

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X : Fin m → ℝ) (a : ℝ) :
    ruMean p (fun ω => a * X ω) = a * ruMean p X := by
  unfold ruMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring
