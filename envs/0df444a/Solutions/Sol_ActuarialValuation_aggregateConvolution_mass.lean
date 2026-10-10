-- Prove2me | solution 1 for ActuarialValuation.aggregateConvolution_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:28:19.398983+00:00
-- url     : https://prove2.me/submissions/86fc0ee8-f63e-4ae4-8d40-0a6e5666d033

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
import Definitions.Def_actuarial_aggregateFiniteMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

private theorem p2m_triangular_sum (f g : ℕ → ℝ) (N : ℕ) :
    (∑ s ∈ Finset.range (N + 1),
      ∑ k ∈ Finset.range (s + 1), f k * g (s - k)) =
    ∑ k ∈ Finset.range (N + 1),
      f k * (∑ j ∈ Finset.range (N + 1 - k), g j) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hstep :
          (∑ k ∈ Finset.range (N + 1),
            f k * (∑ j ∈ Finset.range (N + 2 - k), g j)) =
          (∑ k ∈ Finset.range (N + 1),
            f k * (∑ j ∈ Finset.range (N + 1 - k), g j)) +
          (∑ k ∈ Finset.range (N + 1), f k * g (N + 1 - k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hkle : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hn : N + 2 - k = (N + 1 - k) + 1 := by omega
        rw [hn, Finset.sum_range_succ]
        ring
      calc
        (∑ s ∈ Finset.range (N + 2),
          ∑ k ∈ Finset.range (s + 1), f k * g (s - k)) =
          (∑ s ∈ Finset.range (N + 1),
            ∑ k ∈ Finset.range (s + 1), f k * g (s - k)) +
          (∑ k ∈ Finset.range (N + 2), f k * g (N + 1 - k)) := by
            rw [Finset.sum_range_succ]
        _ = (∑ k ∈ Finset.range (N + 1),
            f k * (∑ j ∈ Finset.range (N + 1 - k), g j)) +
          (∑ k ∈ Finset.range (N + 2), f k * g (N + 1 - k)) := by
            rw [ih]
        _ = (∑ k ∈ Finset.range (N + 1),
            f k * (∑ j ∈ Finset.range (N + 2 - k), g j)) +
            f (N + 1) * g 0 := by
              have hlast :
                  (∑ k ∈ Finset.range (N + 2), f k * g (N + 1 - k)) =
                  (∑ k ∈ Finset.range (N + 1), f k * g (N + 1 - k)) +
                    f (N + 1) * g 0 := by
                    simpa using (Finset.sum_range_succ
                      (fun k => f k * g (N + 1 - k)) (N + 1))
              rw [hlast, hstep]
              ring
        _ = (∑ k ∈ Finset.range (N + 2),
            f k * (∑ j ∈ Finset.range (N + 2 - k), g j)) := by
              simpa using (Finset.sum_range_succ
                (fun k => f k *
                  (∑ j ∈ Finset.range (N + 2 - k), g j)) (N + 1)).symm

theorem solution (f g : ℕ → ℝ) (B C : ℕ)
    (hf : ∀ k, B < k → f k = 0)
    (hg : ∀ k, C < k → g k = 0) :
    aggregateFiniteMass (aggregateConvolution f g) (B + C) =
      aggregateFiniteMass f B * aggregateFiniteMass g C := by
  unfold aggregateFiniteMass aggregateConvolution
  rw [p2m_triangular_sum f g (B + C)]
  have hcut :
      (∑ k ∈ Finset.range (B + C + 1),
        f k * (∑ j ∈ Finset.range (B + C + 1 - k), g j)) =
      ∑ k ∈ Finset.range (B + 1),
        f k * (∑ j ∈ Finset.range (B + C + 1 - k), g j) := by
    let F : ℕ → ℝ := fun k =>
      f k * (∑ j ∈ Finset.range (B + C + 1 - k), g j)
    change (∑ k ∈ Finset.range (B + C + 1), F k) =
      ∑ k ∈ Finset.range (B + 1), F k
    have hn : B + C + 1 = (B + 1) + C := by omega
    rw [hn, Finset.sum_range_add]
    have ht : (∑ k ∈ Finset.range C, F (B + 1 + k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      change f (B + 1 + k) *
        (∑ j ∈ Finset.range (B + C + 1 - (B + 1 + k)), g j) = 0
      rw [hf (B + 1 + k) (by omega), zero_mul]
    rw [ht, add_zero]
  rw [hcut]
  calc
    (∑ k ∈ Finset.range (B + 1),
      f k * (∑ j ∈ Finset.range (B + C + 1 - k), g j)) =
      (∑ k ∈ Finset.range (B + 1),
        f k * (∑ j ∈ Finset.range (C + 1), g j)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkle : k ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hn : B + C + 1 - k = (C + 1) + (B - k) := by omega
          rw [hn, Finset.sum_range_add]
          have ht : (∑ j ∈ Finset.range (B - k), g (C + 1 + j)) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            exact hg (C + 1 + j) (by omega)
          rw [ht, add_zero]
    _ = (∑ k ∈ Finset.range (B + 1), f k) *
        (∑ j ∈ Finset.range (C + 1), g j) := by
          rw [Finset.sum_mul]
