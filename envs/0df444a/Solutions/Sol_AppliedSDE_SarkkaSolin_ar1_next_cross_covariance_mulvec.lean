-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_next_cross_covariance_mulvec
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:51:02.846098+00:00
-- url     : https://prove2.me/submissions/6def61c8-f50c-4738-a375-1c8ac0128a45

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_last_covariance_propagates
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open scoped BigOperators

theorem solution
    (n : ℕ) (a V : ℝ) (z : Fin (n + 1) → ℝ) :
    (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) =
    a * (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist n j.val) * z j) := by
  calc
    (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) =
      ∑ j : Fin (n + 1),
        a * ((V * a ^ Nat.dist n j.val) * z j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [AppliedSDE.SarkkaSolin.ar1_last_covariance_propagates n a V j]
      ring
    _ = a * (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist n j.val) * z j) := by
      rw [Finset.mul_sum]
