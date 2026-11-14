-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.constant_drift_brownian_likelihood_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:35:50.301748+00:00
-- url     : https://prove2.me/submissions/bb772e98-c5e4-4585-9305-38f953035016

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_constant_drift_gaussian_likelihood_ratio
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter
open scoped BigOperators

theorem solution
    (b q t x : ℝ) (hq : 0 < q) (ht : 0 < t) :
    let gaussian : ℝ → ℝ := fun u =>
      Real.exp (-((x - u * t) ^ 2 / (2 * q * t))) /
        Real.sqrt (2 * Real.pi * q * t)
    gaussian b = Real.exp (b * x / q - b ^ 2 * t / (2 * q)) *
      gaussian 0 := by
  simpa using
    (AppliedSDE.SarkkaSolin.constant_drift_gaussian_likelihood_ratio
      b 0 q t x hq ht)
