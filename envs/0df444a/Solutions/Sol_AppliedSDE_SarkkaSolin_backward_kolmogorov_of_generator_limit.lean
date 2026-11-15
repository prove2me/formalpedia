-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.backward_kolmogorov_of_generator_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:22:42.683099+00:00
-- url     : https://prove2.me/submissions/6d0056ea-21b7-4d2e-a215-a2c16bc6f639

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped MeasureTheory Topology ENNReal NNReal
set_option autoImplicit false
theorem solution
    (b a : ℝ → ℝ → ℝ)
    (p : ℝ → ℝ → ℝ → ℝ → ℝ)
    (s y t x : ℝ) (hst : s < t)
    (hTime : DifferentiableAt ℝ (fun u : ℝ => p u y t x) s)
    (hCK : ∀ h : ℝ, 0 < h → s + h < t →
      ∫ z : ℝ, p s y (s + h) z * p (s + h) z t x =
        p s y t x)
    (hGenerator : Tendsto
      (fun h : ℝ =>
        ((∫ z : ℝ, p s y (s + h) z * p (s + h) z t x) -
          p (s + h) y t x) / h)
      (𝓝[>] (0 : ℝ))
      (𝓝 (b s y * deriv (fun z : ℝ => p s z t x) y +
        a s y / 2 *
          deriv (fun z : ℝ => deriv (fun w : ℝ => p s w t x) z) y))) :
    -(deriv (fun u : ℝ => p u y t x) s) =
      b s y * deriv (fun z : ℝ => p s z t x) y +
        a s y / 2 * deriv
          (fun z : ℝ => deriv (fun w : ℝ => p s w t x) z) y := by
  let f : ℝ -> ℝ := fun u => p u y t x
  have hd : HasDerivAt f (deriv f s) s := hTime.hasDerivAt
  have hslope : Tendsto
      (fun h : ℝ => h⁻¹ • (f (s + h) - f s))
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv f s)) :=
    hd.tendsto_slope_zero_right
  have hneg : Tendsto
      (fun h : ℝ => -(h⁻¹ • (f (s + h) - f s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(deriv f s))) :=
    hslope.neg
  have hfun :
      (fun h : ℝ => (f s - f (s + h)) / h) =
        (fun h => -(h⁻¹ • (f (s + h) - f s))) := by
    funext h
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hfirst : Tendsto
      (fun h : ℝ => (f s - f (s + h)) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(deriv f s))) := by
    rw [hfun]
    exact hneg
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), s + h < t := by
    filter_upwards [
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (sub_pos.mpr hst))] with h hh
    change h < t - s at hh
    linarith
  have hEq :
      (fun h : ℝ =>
        ((∫ z : ℝ, p s y (s + h) z * p (s + h) z t x) -
          p (s + h) y t x) / h) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun h : ℝ => (f s - f (s + h)) / h) := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hlt hpos
    dsimp [f]
    rw [hCK h hpos hlt]
  have hlim : Tendsto
      (fun h : ℝ =>
        ((∫ z : ℝ, p s y (s + h) z * p (s + h) z t x) -
          p (s + h) y t x) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(deriv f s))) :=
    hfirst.congr' hEq.symm
  change -(deriv f s) =
    b s y * deriv (fun z : ℝ => p s z t x) y +
    a s y / 2 * deriv (fun z : ℝ => deriv (fun w : ℝ => p s w t x) z) y
  exact tendsto_nhds_unique hlim hGenerator
