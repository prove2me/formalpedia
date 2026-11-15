-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.fpk_gaussian_constant_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:42:20.015404+00:00
-- url     : https://prove2.me/submissions/21173312-b4cc-4a37-8f19-6a4e0a910362

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_constant_drift_spatial_derivative
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_constant_drift_spatial_second_derivative
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_constant_drift_time_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false
theorem solution
    (b q y s x t : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ → ℝ → ℝ := fun z τ =>
      Real.exp (-((z - y - b * (τ - s)) ^ 2 / (2 * q * (τ - s)))) /
        Real.sqrt (2 * Real.pi * q * (τ - s));
    deriv (fun τ => p x τ) t =
      -b * deriv (fun z => p z t) x +
        q / 2 * deriv (fun z => deriv (fun w => p w t) z) x := by
  let p : ℝ -> ℝ -> ℝ := fun z tau =>
    Real.exp (-((z - y - b * (tau - s)) ^ 2 /
      (2 * q * (tau - s)))) /
      Real.sqrt (2 * Real.pi * q * (tau - s))
  let d : ℝ := t - s
  let xi : ℝ := x - y - b * d
  change deriv (fun tau : ℝ => p x tau) t =
    -b * deriv (fun z : ℝ => p z t) x +
      q / 2 * deriv (fun z : ℝ =>
        deriv (fun w : ℝ => p w t) z) x
  have ht : deriv (fun tau : ℝ => p x tau) t =
      (b * xi / (q * d) + xi ^ 2 / (2 * q * d ^ 2) -
        1 / (2 * d)) * p x t := by
    simpa [p, xi, d] using
      (AppliedSDE.SarkkaSolin.gaussian_constant_drift_time_derivative
        b q y s t x hq hst)
  have hs1 : deriv (fun z : ℝ => p z t) x =
      -(xi / (q * d)) * p x t := by
    simpa [p, xi, d] using
      (AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_derivative
        b q y s t x hq hst)
  have hs2 : deriv (fun z : ℝ =>
        deriv (fun w : ℝ => p w t) z) x =
      (xi ^ 2 / (q ^ 2 * d ^ 2) - 1 / (q * d)) * p x t := by
    change deriv (deriv (fun w : ℝ => p w t)) x =
      (xi ^ 2 / (q ^ 2 * d ^ 2) - 1 / (q * d)) * p x t
    simpa only [p, xi, d] using
      (AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_second_derivative
        b q y s t x hq hst)
  rw [ht, hs1, hs2]
  have hqne : q ≠ 0 := ne_of_gt hq
  have hdne : d ≠ 0 := ne_of_gt (sub_pos.mpr hst)
  field_simp [hqne, hdne]
  all_goals ring
