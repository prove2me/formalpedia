-- Prove2me | solution 1 for ActuarialAnnuities.survival_terminal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:27:42.796374+00:00
-- url     : https://prove2.me/submissions/d0e9140b-9315-43aa-8dd3-744157cd9c4b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
open ActuarialAnnuities

theorem solution(h t : ℕ) (p : ℕ → ℝ) (ht : h < t) : bSurvival h p t = 0 := by
  unfold bSurvival
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  unfold bAlive
  rw [if_neg (by omega)]
  ring
