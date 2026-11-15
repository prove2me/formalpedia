-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_covariance_mulvec_innovation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:57:40.097465+00:00
-- url     : https://prove2.me/submissions/9b13dd9a-fdb8-4fc0-a559-ad6e4c2a1a7c

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_innovation_weighted_sum
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open scoped BigOperators

theorem solution
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) → ℝ) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    (K.mulVec z) (Fin.last (n + 1)) -
      a * (K.mulVec z) ((Fin.last n).castSucc) =
        V * (1 - a ^ 2) * z (Fin.last (n + 1)) := by
  change
    (∑ j : Fin (n + 2),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) -
      a * (∑ j : Fin (n + 2),
        (V * a ^ Nat.dist n j.val) * z j) =
      V * (1 - a ^ 2) * z (Fin.last (n + 1))
  calc
    (∑ j : Fin (n + 2),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) -
        a * (∑ j : Fin (n + 2),
          (V * a ^ Nat.dist n j.val) * z j) =
      ∑ j : Fin (n + 2),
        (V * a ^ Nat.dist (n + 1) j.val -
          a * (V * a ^ Nat.dist n j.val)) * z j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = V * (1 - a ^ 2) * z (Fin.last (n + 1)) :=
      AppliedSDE.SarkkaSolin.ar1_innovation_weighted_sum n a V z
