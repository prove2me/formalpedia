-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:51:05.219194+00:00
-- url     : https://prove2.me/submissions/c269e70d-ac83-4090-8ef6-b8945b17f6a4

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_constant_drift_spatial_derivative
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
    deriv (deriv p) x =
      (((x - y - b * (t - s)) ^ 2 / (q ^ 2 * (t - s) ^ 2)) -
        1 / (q * (t - s))) * p x := by
  let d : ℝ := t - s
  let xi : ℝ -> ℝ := fun z => z - y - b * d
  let p : ℝ -> ℝ := fun z =>
    Real.exp (-((xi z) ^ 2 / (2 * q * d))) /
      Real.sqrt (2 * Real.pi * q * d)
  change deriv (deriv p) x =
    ((xi x ^ 2 / (q ^ 2 * d ^ 2)) - 1 / (q * d)) * p x
  have hd : 0 < d := sub_pos.mpr hst
  have hqn : q ≠ 0 := ne_of_gt hq
  have hdn : d ≠ 0 := ne_of_gt hd
  have hfirst : (deriv p) =
      fun z : ℝ => -(xi z / (q * d)) * p z := by
    funext z
    simpa [p, xi, d] using
      (AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_derivative
        b q y s t z hq hst)
  have hxi : HasDerivAt xi 1 x :=
    ((hasDerivAt_id x).sub_const y).sub_const (b * d)
  have hcoef := (hxi.div_const (q * d)).neg
  have hpDiff : DifferentiableAt ℝ p x := by
    fun_prop
  have hp : HasDerivAt p (-(xi x / (q * d)) * p x) x := by
    simpa only [hfirst] using hpDiff.hasDerivAt
  change HasDerivAt (fun z : ℝ => -(xi z / (q * d)))
    (-(1 / (q * d))) x at hcoef
  have hprod := hcoef.mul hp
  change HasDerivAt (fun z : ℝ => -(xi z / (q * d)) * p z) _ x at hprod
  rw [hfirst]
  change deriv (fun z : ℝ => -(xi z / (q * d)) * p z) x =
    ((xi x ^ 2 / (q ^ 2 * d ^ 2)) - 1 / (q * d)) * p x
  rw [hprod.deriv]
  field_simp [hqn, hdn]
  all_goals ring
