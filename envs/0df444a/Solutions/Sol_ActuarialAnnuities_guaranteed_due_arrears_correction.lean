-- Prove2me | solution 1 for ActuarialAnnuities.guaranteed_due_arrears_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:48:01.632636+00:00
-- url     : https://prove2.me/submissions/a0c65c24-30df-4aa7-9ab4-7d8d3847dff5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bLevel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h g : ℕ) (v : ℝ) (p : ℕ → ℝ)
    (hg : g ≤ h) (hp : bTotal h p = 1) :
    bSurvivalPV h 0 h g 0 v (bLevel 1) p -
      bSurvivalPV h 0 h g 1 v (bLevel 1) p =
    1-v^h*bSurvival h p h+v^g*(bSurvival h p g-1) := by
  classical
  let S : ℕ → ℝ := fun t => bSurvival h p t
  let D : ℕ → ℝ := fun j =>
    v^j * (if j < g then S 0 else S j)
  let A : ℕ → ℝ := fun j =>
    v^(j+1) * (if j < g then S 0 else S (j+1))
  let F : ℕ → ℝ := fun j => D j - A j
  have hdue : bSurvivalPV h 0 h g 0 v (bLevel 1) p =
      ∑ j ∈ Finset.range h, D j := by
    unfold bSurvivalPV
    apply Finset.sum_congr rfl
    intro j hj
    have hjh : j < h := Finset.mem_range.mp hj
    simp [D, S, bLevel, hjh]
  have harrears : bSurvivalPV h 0 h g 1 v (bLevel 1) p =
      ∑ j ∈ Finset.range h, A j := by
    unfold bSurvivalPV
    apply Finset.sum_congr rfl
    intro j hj
    have hjh : j < h := Finset.mem_range.mp hj
    simp [A, S, bLevel, hjh]
  have htel (N : ℕ) (Q : ℕ → ℝ) :
      (∑ j ∈ Finset.range N, (Q j - Q (j+1))) = Q 0 - Q N := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hbefore : (∑ j ∈ Finset.range g, F j) =
      S 0 - v^g * S 0 := by
    have hrange : (∑ j ∈ Finset.range g, F j) =
        (∑ j ∈ Finset.range g,
          (v^j * S 0 - v^(j+1) * S 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjg : j < g := Finset.mem_range.mp hj
      simp [F, D, A, hjg]
    rw [hrange]
    simpa using htel g (fun j => v^j * S 0)
  have hafter : (∑ k ∈ Finset.range (h-g), F (g+k)) =
      v^g * S g - v^h * S h := by
    have hrange : (∑ k ∈ Finset.range (h-g), F (g+k)) =
        (∑ k ∈ Finset.range (h-g),
          (v^(g+k) * S (g+k) -
            v^(g+k+1) * S (g+k+1))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hnot : ¬ g+k < g := by omega
      simp [F, D, A, hnot]
    rw [hrange]
    have ht := htel (h-g) (fun k => v^(g+k) * S (g+k))
    simpa only [Nat.add_sub_of_le hg, add_assoc, Nat.add_zero] using ht
  have hS0 : S 0 = 1 := by
    simpa [S, bSurvival, bTotal, bAlive] using hp
  have hsplit : (∑ j ∈ Finset.range h, F j) =
      (∑ j ∈ Finset.range g, F j) +
        (∑ k ∈ Finset.range (h-g), F (g+k)) := by
    conv_lhs => rw [show h = g+(h-g) by omega, Finset.sum_range_add]
  calc
    bSurvivalPV h 0 h g 0 v (bLevel 1) p -
        bSurvivalPV h 0 h g 1 v (bLevel 1) p =
        ∑ j ∈ Finset.range h, F j := by
          rw [hdue, harrears, ← Finset.sum_sub_distrib]
    _ = (∑ j ∈ Finset.range g, F j) +
        (∑ k ∈ Finset.range (h-g), F (g+k)) := hsplit
    _ = (S 0 - v^g * S 0) + (v^g * S g - v^h * S h) := by
          rw [hbefore, hafter]
    _ = 1-v^h*bSurvival h p h+v^g*(bSurvival h p g-1) := by
          rw [hS0]
          dsimp [S]
          ring
