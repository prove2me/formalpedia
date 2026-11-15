-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_innovation_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:54:59.465648+00:00
-- url     : https://prove2.me/submissions/6429db65-d8ca-4a27-8950-08da06761475

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_covariance_row_innovation
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open scoped BigOperators

theorem solution
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) → ℝ) :
    (∑ j : Fin (n + 2),
      (V * a ^ Nat.dist (n + 1) j.val -
        a * (V * a ^ Nat.dist n j.val)) * z j) =
      V * (1 - a ^ 2) * z (Fin.last (n + 1)) := by
  classical
  calc
    (∑ j : Fin (n + 2),
      (V * a ^ Nat.dist (n + 1) j.val -
        a * (V * a ^ Nat.dist n j.val)) * z j) =
      ∑ j : Fin (n + 2),
        (if j.val = n + 1 then V * (1 - a ^ 2) else 0) * z j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [AppliedSDE.SarkkaSolin.ar1_covariance_row_innovation n a V j]
    _ = V * (1 - a ^ 2) * z (Fin.last (n + 1)) := by
      rw [Finset.sum_eq_single (Fin.last (n + 1))]
      · simp
      · intro j hj hne
        have hval : j.val ≠ n + 1 := by
          intro h
          apply hne
          apply Fin.ext
          simpa using h
        simp [hval]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
