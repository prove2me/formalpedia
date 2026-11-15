-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_time_density_quotient_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:02:40.727867+00:00
-- url     : https://prove2.me/submissions/b3887aad-242f-4811-9bf4-0f130e855d4b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false
theorem solution
    (b q d g S E : ℝ)
    (hq : q ≠ 0) (hd : d ≠ 0) (hS : S ≠ 0)
    (hSsq : S ^ 2 = 2 * Real.pi * q * d) :
    ((E * (-((2 * g * (-b) * (2 * q * d) - g ^ 2 * (2 * q)) /
        (2 * q * d) ^ 2))) * S -
      E * ((2 * Real.pi * q) / (2 * S))) / S ^ 2 =
    (b * g / (q * d) + g ^ 2 / (2 * q * d ^ 2) - 1 / (2 * d)) *
      E / S := by
  have hnorm : (2 * Real.pi * q) / (2 * S ^ 2) = 1 / (2 * d) := by
    rw [hSsq]
    field_simp [hq, hd, Real.pi_ne_zero]
    try ring
  have hexp : -((2 * g * (-b) * (2 * q * d) - g ^ 2 * (2 * q)) /
      (2 * q * d) ^ 2) =
      b * g / (q * d) + g ^ 2 / (2 * q * d ^ 2) := by
    field_simp [hq, hd]
    try ring
  calc
    ((E * (-((2 * g * (-b) * (2 * q * d) - g ^ 2 * (2 * q)) /
        (2 * q * d) ^ 2))) * S -
      E * ((2 * Real.pi * q) / (2 * S))) / S ^ 2 =
        E / S * (-((2 * g * (-b) * (2 * q * d) - g ^ 2 * (2 * q)) /
          (2 * q * d) ^ 2) - (2 * Real.pi * q) / (2 * S ^ 2)) := by
          field_simp [hq, hd, hS]
          try ring
    _ = E / S * (b * g / (q * d) +
        g ^ 2 / (2 * q * d ^ 2) - 1 / (2 * d)) := by rw [hexp, hnorm]
    _ = (b * g / (q * d) +
        g ^ 2 / (2 * q * d ^ 2) - 1 / (2 * d)) * E / S := by ring
