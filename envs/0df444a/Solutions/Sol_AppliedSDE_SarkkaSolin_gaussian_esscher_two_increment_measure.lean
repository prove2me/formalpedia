-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_esscher_two_increment_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:53:27.036257+00:00
-- url     : https://prove2.me/submissions/b347d092-6a0a-4a30-a22e-47d70159dd5b

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_tilt_measure
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w) (theta : ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 w)).withDensity
      (fun z : ℝ × ℝ =>
        ENNReal.ofReal
          (Real.exp (theta * z.1 - (v : ℝ) * theta ^ 2 / 2)) *
        ENNReal.ofReal
          (Real.exp (theta * z.2 - (w : ℝ) * theta ^ 2 / 2))) =
    (gaussianReal ((v : ℝ) * theta) v).prod
      (gaussianReal ((w : ℝ) * theta) w) := by
  let f : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal
      (Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2))
  let g : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal
      (Real.exp (theta * x - (w : ℝ) * theta ^ 2 / 2))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  change ((gaussianReal 0 v).prod (gaussianReal 0 w)).withDensity
      (fun z : ℝ × ℝ => f z.1 * g z.2) =
      (gaussianReal ((v : ℝ) * theta) v).prod
        (gaussianReal ((w : ℝ) * theta) w)
  rw [← MeasureTheory.prod_withDensity (μ := gaussianReal 0 v)
      (ν := gaussianReal 0 w) hf hg]
  rw [AppliedSDE.SarkkaSolin.gaussian_esscher_tilt_measure v hv theta,
      AppliedSDE.SarkkaSolin.gaussian_esscher_tilt_measure w hw theta]