-- Prove2me | solution 1 for ActuarialAnnuities.assurance_annuity_complement
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:05:16.244408+00:00
-- url     : https://prove2.me/submissions/eddf6c31-0084-46e0-85b5-2533a86c406b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bLevel
import Definitions.Def_actuarial_bAssurancePV
open ActuarialAnnuities

theorem solution(h : ℕ) (v : ℝ) (p : ℕ → ℝ) : bAssurancePV h v p + (1-v)*bSurvivalPV h 0 h 0 0 v (bLevel 1) p = bTotal h p - v^h*p h := by
  have hS : ∀ j, j < h → bSurvival h p j = bSurvival h p (j + 1) + p j := by
    intro j hj
    unfold bSurvival
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    have hc : ∀ k ∈ Finset.range (h + 1), p k * bAlive k j - p k * bAlive k (j + 1) = if k = j then p k else 0 := by
      intro k _
      unfold bAlive
      split_ifs <;> first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl hc]
    simp <;> omega
  have hSh : bSurvival h p h = p h := by
    unfold bSurvival bAlive
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk => by rw [Finset.mem_range] at hk; rw [if_neg (by omega)]; ring)]
    simp
  have hS0 : bSurvival h p 0 = bTotal h p := by
    unfold bSurvival bTotal bAlive
    simp
  unfold bSurvivalPV bAssurancePV bLevel
  have hsum : ∀ j ∈ Finset.range h, (if 0 ≤ j ∧ j < 0 + h then 1 * v ^ (j + 0) * (if j < 0 + 0 then bSurvival h p 0 else bSurvival h p (j + 0)) else 0) = v ^ j * bSurvival h p j := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp [hj]
  rw [Finset.sum_congr rfl hsum]
  have tel := Finset.sum_range_sub' (fun j => v ^ j * bSurvival h p j) h
  beta_reduce at tel
  have hsplit : ∀ j ∈ Finset.range h, v ^ j * bSurvival h p j - v ^ (j + 1) * bSurvival h p (j + 1) = (1 - v) * (v ^ j * bSurvival h p j) + p j * v ^ (j + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hS j hj]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hS0, hSh, pow_zero, one_mul] at tel
  linarith [tel]
