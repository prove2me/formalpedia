-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_last_covariance_propagates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:14:36.125634+00:00
-- url     : https://prove2.me/submissions/0744a7a3-5c48-4811-ac5c-751973df0004

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (n : ℕ) (a V : ℝ) (i : Fin (n + 1)) :
    V * a ^ Nat.dist (n + 1) i.val =
      a * (V * a ^ Nat.dist n i.val) := by
  have hi : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
  have hdist :
      Nat.dist (n + 1) i.val = Nat.dist n i.val + 1 := by
    rw [Nat.dist_eq_sub_of_le_right (Nat.le_succ_of_le hi),
      Nat.dist_eq_sub_of_le_right hi]
    omega
  rw [hdist, pow_succ]
  ring