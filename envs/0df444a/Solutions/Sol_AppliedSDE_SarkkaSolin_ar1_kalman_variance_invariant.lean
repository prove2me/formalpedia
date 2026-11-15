-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_kalman_variance_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:56:05.600714+00:00
-- url     : https://prove2.me/submissions/effabb8a-44d7-4d17-bb0c-47f25f83ca49

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_variance_update_bounded
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
    ∀ k : Fin (n + 1), 0 < P k ∧ P k ≤ V := by
  intro k
  induction k using Fin.inductionOn with
  | zero =>
      rw [hP0]
      have hden : 0 < V + r := add_pos hV hr
      constructor
      · exact div_pos (mul_pos hV hr) hden
      · apply (div_le_iff₀ hden).2
        nlinarith [sq_nonneg V]
  | succ k ih =>
      rcases ih with ⟨hp, hPV⟩
      have hb :=
        AppliedSDE.SarkkaSolin.ar1_kalman_variance_update_bounded
          a V r (P k.castSucc) ha ha1 hV hr hp.le hPV
      dsimp at hb
      rw [hPrec k]
      exact ⟨hb.2.1, hb.2.2⟩
