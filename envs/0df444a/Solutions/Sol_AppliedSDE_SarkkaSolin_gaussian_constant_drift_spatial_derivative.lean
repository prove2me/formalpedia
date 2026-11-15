-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:19:41.033911+00:00
-- url     : https://prove2.me/submissions/879c02d1-448e-41a2-8759-4271c0d6e0bf

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (b q y s t x : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ -> ℝ := fun z =>
      Real.exp (-((z - y - b * (t - s)) ^ 2 / (2 * q * (t - s)))) /
        Real.sqrt (2 * Real.pi * q * (t - s))
    deriv p x = -((x - y - b * (t - s)) / (q * (t - s))) * p x := by
  let d : ℝ := t - s
  let Q : ℝ := 2 * Real.pi * q * d
  let k : ℝ := 2 * q * d
  let xi : ℝ := x - y - b * d
  let p : ℝ -> ℝ := fun z =>
    Real.exp (-((z - y - b * d) ^ 2 / k)) / Real.sqrt Q
  change deriv p x = -(xi / (q * d)) * p x
  have hd : 0 < d := sub_pos.mpr hst
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hQne : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hqn : q ≠ 0 := ne_of_gt hq
  have hdn : d ≠ 0 := ne_of_gt hd
  have hsub : HasDerivAt (fun z : ℝ => z - y - b * d) 1 x :=
    ((hasDerivAt_id x).sub_const y).sub_const (b * d)
  have hcalc := ((hsub.pow 2).div_const k).neg
  have hpder := hcalc.exp.div_const (Real.sqrt Q)
  change HasDerivAt p _ x at hpder
  rw [hpder.deriv]
  all_goals
    try dsimp [p, xi, k, d, Q]
    field_simp [hqn, hdn, hQne]
    try ring
