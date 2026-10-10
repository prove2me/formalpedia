-- Prove2me | solution 1 for ActuarialValuation.aggregateConvolution_comm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:13:42.260977+00:00
-- url     : https://prove2.me/submissions/5d9bbd4a-6c0c-4aa2-b3ae-684e5ccc3f29

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g : ℕ → ℝ) (s : ℕ) :
    aggregateConvolution f g s = aggregateConvolution g f s := by
  unfold aggregateConvolution
  calc
    (∑ k ∈ Finset.range (s + 1), f k * g (s - k)) =
        ∑ k ∈ Finset.range (s + 1),
          f (s - k) * g (s - (s - k)) := by
            simpa using (Finset.sum_range_reflect
              (fun k => f k * g (s - k)) (s + 1)).symm
    _ = ∑ k ∈ Finset.range (s + 1), g k * f (s - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Nat.sub_sub_self hks]
      ring
