-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_two_observation_posterior_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:18:12.517088+00:00
-- url     : https://prove2.me/submissions/06f91344-57ea-4e74-983b-0e4794d47c70

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    let D : ℝ := (V + r) ^ 2 - (a * V) ^ 2
    let P0 : ℝ := V * r / (V + r)
    let pred : ℝ := a ^ 2 * P0 + V * (1 - a ^ 2)
    V - ((a * V) ^ 2 * (V + r) -
         2 * (a * V) * V * (a * V) + V ^ 2 * (V + r)) / D =
      pred * r / (pred + r) := by
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
      (a * V) ^ 2 * (V + r) -
        2 * (a * V) * V * (a * V) + V ^ 2 * (V + r) =
      (V + r) * (V * (p + r) - p * r) := by
    calc
      _ = V ^ 2 * ((V + r) + a ^ 2 * (r - V)) := by ring
      _ = V * (V + r) * r +
            (V * ((V + r) - a ^ 2 * V)) * (V - r) := by ring
      _ = V * (V + r) * r + ((V + r) * p) * (V - r) := by
        rw [hMpred]
      _ = (V + r) * (V * (p + r) - p * r) := by ring
  change V - ((a * V) ^ 2 * (V + r) -
         2 * (a * V) * V * (a * V) + V ^ 2 * (V + r)) /
         ((V + r) ^ 2 - (a * V) ^ 2) =
      p * r / (p + r)
  rw [hnum, hdet]
  field_simp [hvne, hden]
  ring