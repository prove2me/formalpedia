-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.constant_drift_gaussian_likelihood_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:35:16.879932+00:00
-- url     : https://prove2.me/submissions/a1f060ce-4e64-4cf5-a918-e79f57342f36

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter
open scoped BigOperators

theorem solution
    (b c q t x : ℝ) (hq : 0 < q) (ht : 0 < t) :
    let p : ℝ → ℝ := fun u =>
      Real.exp (-((x - u * t) ^ 2 / (2 * q * t))) /
        Real.sqrt (2 * Real.pi * q * t)
    p b = Real.exp ((b - c) * x / q -
      (b ^ 2 - c ^ 2) * t / (2 * q)) * p c := by
  have hqne : q ≠ 0 := ne_of_gt hq
  have htne : t ≠ 0 := ne_of_gt ht
  have hexponent :
      -((x - b * t) ^ 2 / (2 * q * t)) =
        ((b - c) * x / q - (b ^ 2 - c ^ 2) * t / (2 * q)) +
          -((x - c * t) ^ 2 / (2 * q * t)) := by
    field_simp [hqne, htne]
    ring
  dsimp
  rw [hexponent, Real.exp_add]
  ring
