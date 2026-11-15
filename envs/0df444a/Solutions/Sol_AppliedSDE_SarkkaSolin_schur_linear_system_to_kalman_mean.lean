-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_linear_system_to_kalman_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:25:41.037767+00:00
-- url     : https://prove2.me/submissions/1ed1c973-b69a-4b5c-90d5-eb4eb3d342de

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_scalar_elimination
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (n : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (u b x : Fin n → ℝ) (w q r v : ℝ)
    (hq : 0 < q) (hr : 0 < r)
    (hx : x = A (u - w • b))
    (hrow : l x + (q + r + l (A b)) * w = v) :
    l (A u) + q * w =
      l (A u) + q / (q + r) * (v - l (A u)) := by
  have hqr : q + r ≠ 0 := ne_of_gt (add_pos hq hr)
  have hS : (q + r + l (A b)) - l (A b) ≠ 0 := by
    simpa only [add_sub_cancel_right] using hqr
  have hw :=
    AppliedSDE.SarkkaSolin.schur_block_scalar_elimination
      n A l u b x w (q + r + l (A b)) v hx hrow hS
  have hw' : w = (v - l (A u)) / (q + r) := by
    simpa only [add_sub_cancel_right] using hw
  rw [hw']
  ring
