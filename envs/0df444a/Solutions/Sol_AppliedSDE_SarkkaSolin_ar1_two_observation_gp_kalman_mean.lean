-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_two_observation_gp_kalman_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:03:18.409793+00:00
-- url     : https://prove2.me/submissions/d28a218f-bf85-495c-b4cb-404385d70e67

import Mathlib
set_option autoImplicit false
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    (a V r y0 y1 : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    let D : ℝ := (V + r) ^ 2 - (a * V) ^ 2
    let P0 : ℝ := V * r / (V + r)
    let pred : ℝ := a ^ 2 * P0 + V * (1 - a ^ 2)
    let m0 : ℝ := V / (V + r) * y0
    (a * V * ((V + r) * y0 - a * V * y1) +
      V * ((V + r) * y1 - a * V * y0)) / D =
        a * m0 + pred / (pred + r) * (y1 - a * m0) := by
  let p : ℝ := a ^ 2 * (V * r / (V + r)) + V * (1 - a ^ 2)
  have hvr : 0 < V + r := add_pos hV hr
  have hvne : V + r ≠ 0 := ne_of_gt hvr
  have ha2 : a ^ 2 < 1 := by nlinarith [sq_nonneg (1 - a)]
  have hp : 0 < p := by
    dsimp [p]
    apply add_pos_of_nonneg_of_pos
    · exact mul_nonneg (sq_nonneg a)
        (le_of_lt (div_pos (mul_pos hV hr) hvr))
    · exact mul_pos hV (sub_pos.mpr ha2)
  have hden : p + r ≠ 0 := ne_of_gt (add_pos hp hr)
  have hMpred : (V + r) * p = V * ((V + r) - a ^ 2 * V) := by
    dsimp [p]
    field_simp [hvne]
    ring
  have hdet :
      (V + r) ^ 2 - (a * V) ^ 2 = (V + r) * (p + r) := by
    dsimp [p]
    field_simp [hvne]
    ring
  have hnum :
      a * V * ((V + r) * y0 - a * V * y1) +
          V * ((V + r) * y1 - a * V * y0) =
        a * V * r * y0 + (V + r) * p * y1 := by
    calc
      _ = a * V * r * y0 +
          (V * ((V + r) - a ^ 2 * V)) * y1 := by ring
      _ = a * V * r * y0 + (V + r) * p * y1 := by rw [hMpred]
  change
    (a * V * ((V + r) * y0 - a * V * y1) +
      V * ((V + r) * y1 - a * V * y0)) /
       ((V + r) ^ 2 - (a * V) ^ 2) =
      a * (V / (V + r) * y0) + p / (p + r) *
        (y1 - a * (V / (V + r) * y0))
  rw [hnum, hdet]
  field_simp [hvne, hden]
  ring
