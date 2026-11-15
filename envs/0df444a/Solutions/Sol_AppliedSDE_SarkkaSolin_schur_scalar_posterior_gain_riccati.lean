-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_scalar_posterior_gain_riccati
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:56:22.114293+00:00
-- url     : https://prove2.me/submissions/bd0f12b8-4b3c-4ee8-ac22-26f326a61241

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (P r μ y : ℝ) (hP : 0 < P) (hr : 0 < r) :
    (μ + P / (P + r) * (y - μ) =
       (r * μ + P * y) / (P + r)) ∧
    (P - P ^ 2 / (P + r) = P * r / (P + r)) := by
  have hden : P + r ≠ 0 := ne_of_gt (add_pos hP hr)
  constructor
  · field_simp [hden]
    ring
  · field_simp [hden]
    ring
