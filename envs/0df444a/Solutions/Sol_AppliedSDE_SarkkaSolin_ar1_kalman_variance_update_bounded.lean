-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_kalman_variance_update_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:04:18.154249+00:00
-- url     : https://prove2.me/submissions/727c2efa-d835-4e01-844c-a74274c10502

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (a V r P : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (hP0 : 0 ≤ P) (hPV : P ≤ V) :
    let predicted : ℝ := a ^ 2 * P + V * (1 - a ^ 2)
    0 < predicted ∧
      0 < predicted * r / (predicted + r) ∧
      predicted * r / (predicted + r) ≤ V := by
  let predicted : ℝ := a ^ 2 * P + V * (1 - a ^ 2)
  change 0 < predicted ∧
    0 < predicted * r / (predicted + r) ∧
    predicted * r / (predicted + r) ≤ V
  have ha2 : a ^ 2 < 1 := by nlinarith [sq_nonneg (1 - a)]
  have hterm1 : 0 ≤ a ^ 2 * P :=
    mul_nonneg (sq_nonneg a) hP0
  have hterm2 : 0 < V * (1 - a ^ 2) :=
    mul_pos hV (sub_pos.mpr ha2)
  have hp : 0 < predicted := by
    dsimp [predicted]
    linarith
  have hple : predicted ≤ V := by
    have h := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hPV)
    dsimp [predicted]
    nlinarith
  have hdenom : 0 < predicted + r := add_pos hp hr
  have hup : 0 < predicted * r / (predicted + r) :=
    div_pos (mul_pos hp hr) hdenom
  have hle : predicted * r / (predicted + r) ≤ predicted := by
    apply (div_le_iff₀ hdenom).mpr
    nlinarith [sq_nonneg predicted]
  exact ⟨hp, hup, hle.trans hple⟩