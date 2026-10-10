-- Prove2me | solution 1 for ActuarialValuation.aggregateConvolution_assoc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:35:20.817324+00:00
-- url     : https://prove2.me/submissions/25b2a1fc-97ae-4aa8-8052-10b1659d4e71

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

private theorem p2m_triangle_reindex (F : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ t ∈ Finset.range (N + 1),
       ∑ i ∈ Finset.range (t + 1), F i (t - i)) =
    ∑ i ∈ Finset.range (N + 1),
       ∑ j ∈ Finset.range (N + 1 - i), F i j := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hstep :
          (∑ i ∈ Finset.range (N + 1),
            ∑ j ∈ Finset.range (N + 2 - i), F i j) =
          (∑ i ∈ Finset.range (N + 1),
            ∑ j ∈ Finset.range (N + 1 - i), F i j) +
          (∑ i ∈ Finset.range (N + 1), F i (N + 1 - i)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hle : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hn : N + 2 - i = (N + 1 - i) + 1 := by omega
        rw [hn, Finset.sum_range_succ]
      calc
        (∑ t ∈ Finset.range (N + 2),
          ∑ i ∈ Finset.range (t + 1), F i (t - i)) =
          (∑ t ∈ Finset.range (N + 1),
            ∑ i ∈ Finset.range (t + 1), F i (t - i)) +
          (∑ i ∈ Finset.range (N + 2), F i (N + 1 - i)) := by
            rw [Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range (N + 1),
          ∑ j ∈ Finset.range (N + 1 - i), F i j) +
          (∑ i ∈ Finset.range (N + 2), F i (N + 1 - i)) := by
            rw [ih]
        _ = (∑ i ∈ Finset.range (N + 1),
            ∑ j ∈ Finset.range (N + 2 - i), F i j) +
            F (N + 1) 0 := by
              have hlast :
                  (∑ i ∈ Finset.range (N + 2), F i (N + 1 - i)) =
                  (∑ i ∈ Finset.range (N + 1), F i (N + 1 - i)) +
                    F (N + 1) 0 := by
                    simpa using (Finset.sum_range_succ
                      (fun i => F i (N + 1 - i)) (N + 1))
              rw [hlast, hstep]
              abel
        _ = (∑ i ∈ Finset.range (N + 2),
          ∑ j ∈ Finset.range (N + 2 - i), F i j) := by
            simpa using (Finset.sum_range_succ
              (fun i => ∑ j ∈ Finset.range (N + 2 - i), F i j)
              (N + 1)).symm

theorem solution (f g h : ℕ → ℝ) (s : ℕ) :
    aggregateConvolution (aggregateConvolution f g) h s =
      aggregateConvolution f (aggregateConvolution g h) s := by
  change
    (∑ t ∈ Finset.range (s + 1),
      (∑ i ∈ Finset.range (t + 1), f i * g (t - i)) * h (s - t)) =
    (∑ i ∈ Finset.range (s + 1),
      f i * (∑ j ∈ Finset.range (s - i + 1), g j * h (s - i - j)))
  calc
    (∑ t ∈ Finset.range (s + 1),
      (∑ i ∈ Finset.range (t + 1), f i * g (t - i)) * h (s - t)) =
      ∑ t ∈ Finset.range (s + 1),
        ∑ i ∈ Finset.range (t + 1), f i * g (t - i) * h (s - t) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_mul]
    _ = ∑ t ∈ Finset.range (s + 1),
          ∑ i ∈ Finset.range (t + 1),
            f i * (g (t - i) * h (s - (i + (t - i)))) := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro i hi
          have hle : i ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have heq : i + (t - i) = t := Nat.add_sub_of_le hle
          rw [heq]
          ring
    _ = ∑ i ∈ Finset.range (s + 1),
          ∑ j ∈ Finset.range (s + 1 - i),
            f i * (g j * h (s - (i + j))) :=
          p2m_triangle_reindex
            (fun i j => f i * (g j * h (s - (i + j)))) s
    _ = ∑ i ∈ Finset.range (s + 1),
          f i * (∑ j ∈ Finset.range (s - i + 1), g j * h (s - i - j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hle : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hn : s + 1 - i = (s - i) + 1 := by omega
          rw [hn, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hs : s - (i + j) = s - i - j := by omega
          rw [hs]
