-- Prove2me | solution 2 for AppliedSDE.SarkkaSolin.ar1_covariance_row_innovation
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-14T08:39:15.001587+00:00
-- url     : https://prove2.me/submissions/3b7beb3d-a9e5-4c6c-9842-8e0e7daa8c71

import Mathlib

theorem solution
    (n : ℕ) (a V : ℝ) (i : Fin (n + 2)) :
    V * a ^ Nat.dist (n + 1) i.val -
      a * (V * a ^ Nat.dist n i.val) =
    if i.val = n + 1 then V * (1 - a ^ 2) else 0 := by
  have hi : i.val ≤ n + 1 := by omega
  rcases eq_or_ne i.val (n + 1) with h | h
  · rw [h]
    have h1 : Nat.dist (n + 1) (n + 1) = 0 := Nat.dist_self _
    have h2 : Nat.dist n (n + 1) = 1 := by
      rw [Nat.dist_eq_sub_of_le (by omega : n ≤ n + 1)]
      omega
    rw [h1, h2, if_pos rfl]
    ring
  · have hle : i.val ≤ n := by omega
    have h1 : Nat.dist (n + 1) i.val = n + 1 - i.val := Nat.dist_eq_sub_of_le_right hi
    have h2 : Nat.dist n i.val = n - i.val := Nat.dist_eq_sub_of_le_right hle
    have h3 : n + 1 - i.val = n - i.val + 1 := by omega
    rw [h1, h2, h3, if_neg h, pow_succ]
    ring
