-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_gp_batch_next_state_predicted_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:07:25.444201+00:00
-- url     : https://prove2.me/submissions/31cb647c-4f33-4d40-86f0-76b4e8397c27

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_next_cross_covariance_mulvec
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped BigOperators Matrix

theorem solution
    (n : ℕ) (a V r : ℝ)
    (y : Fin (n + 1) → ℝ) :
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    let z := (K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹ |>.mulVec y
    (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) =
      a * (K.mulVec z) (Fin.last n) := by
  let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => V * a ^ Nat.dist i.val j.val
  let z : Fin (n + 1) → ℝ :=
    (K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹ |>.mulVec y
  change (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) =
    a * (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist n j.val) * z j)
  exact AppliedSDE.SarkkaSolin.ar1_next_cross_covariance_mulvec n a V z
