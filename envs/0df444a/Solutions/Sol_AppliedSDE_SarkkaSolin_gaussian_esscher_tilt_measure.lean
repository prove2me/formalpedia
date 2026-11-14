-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_esscher_tilt_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:36:00.70119+00:00
-- url     : https://prove2.me/submissions/ecf2843b-be29-4761-886a-523ee2b80a1c

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    (v : ℝ≥0) (hv : 0 < v) (theta : ℝ) :
    (gaussianReal 0 v).withDensity
      (fun x : ℝ => ENNReal.ofReal
        (Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2))) =
      gaussianReal ((v : ℝ) * theta) v := by
  have hne : v ≠ 0 := ne_of_gt hv
  rw [gaussianReal_of_var_ne_zero 0 hne,
    gaussianReal_of_var_ne_zero ((v : ℝ) * theta) hne]
  have hm : Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2))) :=
    Measurable.ennreal_ofReal (by fun_prop)
  rw [← withDensity_mul (volume : Measure ℝ)
    (measurable_gaussianPDF 0 v) hm]
  apply congrArg (fun density : ℝ → ℝ≥0∞ =>
    (volume : Measure ℝ).withDensity density)
  funext x
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
  congr 1
  unfold gaussianPDFReal
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  have hexpo :
      -(x - 0) ^ 2 / (2 * (v : ℝ)) +
        (theta * x - (v : ℝ) * theta ^ 2 / 2) =
      -(x - (v : ℝ) * theta) ^ 2 / (2 * (v : ℝ)) := by
    field_simp [hvne]
    ring
  rw [mul_assoc, ← Real.exp_add, hexpo]