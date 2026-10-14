-- Prove2me | solution 1 for ActuarialAnnuities.due_arrears_boundary
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:55:50.934999+00:00
-- url     : https://prove2.me/submissions/1a5cdb11-5215-4c1b-8512-28bbe82e3c12

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bLevel
open ActuarialAnnuities

theorem solution(h : ℕ) (v : ℝ) (p : ℕ → ℝ) (hp : bTotal h p = 1) : bExpectedPV h 0 h 0 0 v (bLevel 1) p-bExpectedPV h 0 h 0 1 v (bLevel 1) p = 1-v^h*bSurvival h p h := by
  have key : ∀ d : ℕ, bExpectedPV h 0 h 0 d v (bLevel 1) p = ∑ j ∈ Finset.range h, v ^ (j + d) * ∑ k ∈ Finset.range (h + 1), p k * bAlive k (j + d) := by
    intro d
    unfold bExpectedPV bPathPV bEntitlement bLevel
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    apply Finset.sum_congr rfl
    intro k _
    rw [if_pos ⟨Nat.zero_le j, by omega⟩, if_neg (by omega)]
    ring
  rw [key, key, ← Finset.sum_sub_distrib]
  simp only [add_zero]
  have tel := Finset.sum_range_sub' (fun j => v ^ j * ∑ k ∈ Finset.range (h + 1), p k * bAlive k j) h
  rw [tel]
  unfold bSurvival
  unfold bTotal at hp
  simp [bAlive, hp]
