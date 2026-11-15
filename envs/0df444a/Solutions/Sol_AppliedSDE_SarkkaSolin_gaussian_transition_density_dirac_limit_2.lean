-- Prove2me | solution 2 for AppliedSDE.SarkkaSolin.gaussian_transition_density_dirac_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:03:39.286402+00:00
-- url     : https://prove2.me/submissions/2fd5cad2-511f-44f0-ba28-8b911a7c89d2

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_transition_kernel_integral_eq_gaussianReal
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussianReal_expectation_narrow_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology NNReal
set_option autoImplicit false
theorem solution
    (b q y s : ℝ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) :
    let p : ℝ → ℝ → ℝ := fun x t =>
      Real.exp (-((x - y - b * (t - s)) ^ 2 / (2 * q * (t - s)))) /
        Real.sqrt (2 * Real.pi * q * (t - s));
    Tendsto (fun h : ℝ => ∫ x : ℝ, p x (s + h) * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  let p : ℝ -> ℝ -> ℝ := fun x t =>
    Real.exp (-((x - y - b * (t - s)) ^ 2 /
      (2 * q * (t - s)))) /
      Real.sqrt (2 * Real.pi * q * (t - s))
  change Tendsto (fun h : ℝ =>
    ∫ x : ℝ, p x (s + h) * f x) (𝓝[>] (0 : ℝ)) (𝓝 (f y))
  have hlimit := AppliedSDE.SarkkaSolin.gaussianReal_expectation_narrow_limit
    b q y hq f hf hfb
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpos : 0 < h := hh
  have hqh : 0 ≤ q * h := (mul_pos hq hpos).le
  have hv : (⟨q * h, hqh⟩ : ℝ≥0) =
      (q * h).toNNReal := (Real.toNNReal_of_nonneg hqh).symm
  have hkernel :=
    AppliedSDE.SarkkaSolin.gaussian_transition_kernel_integral_eq_gaussianReal
      b q y h hq hpos f
  simp only [hv] at hkernel
  simpa only [p, add_sub_cancel_left] using hkernel.symm
