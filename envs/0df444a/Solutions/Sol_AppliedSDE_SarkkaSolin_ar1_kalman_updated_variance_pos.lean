-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_kalman_updated_variance_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:50:54.715912+00:00
-- url     : https://prove2.me/submissions/b661e7c7-34fa-4d33-b99c-92911d6e4fde

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (P : Fin (n + 1) → ℝ)
    (hP0 : P 0 = V * r / (V + r))
    (hPrec : ∀ k : Fin n,
      P k.succ =
        (a ^ 2 * P k.castSucc + V * (1 - a ^ 2)) * r /
          (a ^ 2 * P k.castSucc + V * (1 - a ^ 2) + r)) :
    ∀ k : Fin (n + 1), 0 < P k := by
  have ha2 : a ^ 2 < 1 := by nlinarith
  have hnoise : 0 < V * (1 - a ^ 2) := by
    apply mul_pos hV
    linarith
  intro k
  induction k using Fin.inductionOn with
  | zero =>
      rw [hP0]
      exact div_pos (mul_pos hV hr) (add_pos hV hr)
  | succ k ih =>
      rw [hPrec k]
      have hp : 0 ≤ a ^ 2 * P k.castSucc :=
        mul_nonneg (sq_nonneg a) (le_of_lt ih)
      have hpred : 0 < a ^ 2 * P k.castSucc + V * (1 - a ^ 2) :=
        add_pos_of_nonneg_of_pos hp hnoise
      exact div_pos (mul_pos hpred hr) (add_pos hpred hr)
