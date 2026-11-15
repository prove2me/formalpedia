-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_covariance_row_innovation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:52:24.321072+00:00
-- url     : https://prove2.me/submissions/e313dc68-7ac2-44d3-be1b-dce487217cb4

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (n : ℕ) (a V : ℝ) (i : Fin (n + 2)) :
    V * a ^ Nat.dist (n + 1) i.val -
      a * (V * a ^ Nat.dist n i.val) =
    if i.val = n + 1 then V * (1 - a ^ 2) else 0 := by
  by_cases hi : i.val = n + 1
  · rw [if_pos hi, hi]
    have hzero : Nat.dist (n + 1) (n + 1) = 0 := by simp
    have hone : Nat.dist n (n + 1) = 1 := by
      rw [Nat.dist_comm n (n + 1),
        Nat.dist_eq_sub_of_le_right (Nat.le_succ n)]
      omega
    rw [hzero, hone]
    ring
  · rw [if_neg hi]
    have hle : i.val ≤ n := by
      have hlt := i.isLt
      omega
    have hdist :
        Nat.dist (n + 1) i.val = Nat.dist n i.val + 1 := by
      rw [Nat.dist_eq_sub_of_le_right (Nat.le_succ_of_le hle),
        Nat.dist_eq_sub_of_le_right hle]
      omega
    rw [hdist, pow_succ]
    ring