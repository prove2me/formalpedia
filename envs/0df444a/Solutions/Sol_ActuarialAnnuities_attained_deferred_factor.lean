-- Prove2me | solution 1 for ActuarialAnnuities.attained_deferred_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:40:46.734833+00:00
-- url     : https://prove2.me/submissions/9677984f-0fb3-4800-9080-87acede86807

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bAttainedConditionalPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h a n delta : ℕ) (v : ℝ) (b p : ℕ → ℝ)
    (ha : a+n ≤ h) (hs : 0 < bSurvival h p a) :
    bSurvivalPV h a n 0 delta v b p =
      v^a * bSurvival h p a *
        bAttainedConditionalPV h a n delta v b p := by
  classical
  let f : ℕ → ℝ := fun j =>
    b j * v^(j+delta) * bSurvival h p (j+delta)
  let G : ℕ → ℝ := fun j =>
    if a ≤ j ∧ j < a+n then f j else 0
  have hshape : bSurvivalPV h a n 0 delta v b p =
      ∑ j ∈ Finset.range h, G j := by
    unfold bSurvivalPV
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpay : a ≤ j ∧ j < a+n
    · have hfalse : ¬ j < a+0 := by omega
      simp [G, f, hpay, hfalse]
    · simp [G, hpay]
  have htail : (∑ k ∈ Finset.range (h-(a+n)), G (a+n+k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hnot : ¬ (a ≤ a+n+k ∧ a+n+k < a+n) := by omega
    simp [G, hnot]
  have hhead : (∑ j ∈ Finset.range a, G j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt : j < a := Finset.mem_range.mp hj
    have hnot : ¬ (a ≤ j ∧ j < a+n) := by omega
    simp [G, hnot]
  have hmid : (∑ k ∈ Finset.range n, G (a+k)) =
      (∑ k ∈ Finset.range n, f (a+k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hpay : a ≤ a+k ∧ a+k < a+n := by omega
    simp [G, hpay]
  have hsplit :
      (∑ j ∈ Finset.range h, G j) =
        ∑ k ∈ Finset.range n, f (a+k) := by
    have hh : h = a+n+(h-(a+n)) := by omega
    calc
      (∑ j ∈ Finset.range h, G j) =
          (∑ j ∈ Finset.range (a+n), G j) +
            (∑ k ∈ Finset.range (h-(a+n)), G (a+n+k)) := by
              conv_lhs => rw [hh, Finset.sum_range_add]
      _ = ∑ j ∈ Finset.range (a+n), G j := by rw [htail, add_zero]
      _ = (∑ j ∈ Finset.range a, G j) +
            (∑ k ∈ Finset.range n, G (a+k)) := by
              rw [Finset.sum_range_add]
      _ = ∑ k ∈ Finset.range n, f (a+k) := by
              rw [hhead, zero_add, hmid]
  have hs0 : bSurvival h p a ≠ 0 := ne_of_gt hs
  calc
    bSurvivalPV h a n 0 delta v b p =
        ∑ k ∈ Finset.range n, f (a+k) := hshape.trans hsplit
    _ = v^a * bSurvival h p a *
          bAttainedConditionalPV h a n delta v b p := by
      unfold bAttainedConditionalPV
      rw [mul_comm (v^a * bSurvival h p a)
        (∑ k ∈ Finset.range n,
          b (a+k) * v^(k+delta) *
            (bSurvival h p (a+k+delta) / bSurvival h p a)),
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f]
      rw [show a+k+delta = a+(k+delta) by omega, pow_add]
      field_simp [hs0]
