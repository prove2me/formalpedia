-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_esscher_three_increment_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:06:16.474803+00:00
-- url     : https://prove2.me/submissions/57d47aa9-89df-45b8-9712-c4a7cd00e285

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_two_increment_measure
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_tilt_measure
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    (v w u : ℝ≥0) (hv : 0 < v) (hw : 0 < w) (hu : 0 < u)
    (theta : ℝ) :
    (((gaussianReal 0 v).prod (gaussianReal 0 w)).prod
      (gaussianReal 0 u)).withDensity
      (fun z : (ℝ × ℝ) × ℝ =>
        (ENNReal.ofReal
            (Real.exp (theta * z.1.1 - (v : ℝ) * theta ^ 2 / 2)) *
          ENNReal.ofReal
            (Real.exp (theta * z.1.2 - (w : ℝ) * theta ^ 2 / 2))) *
        ENNReal.ofReal
          (Real.exp (theta * z.2 - (u : ℝ) * theta ^ 2 / 2))) =
    ((gaussianReal ((v : ℝ) * theta) v).prod
      (gaussianReal ((w : ℝ) * theta) w)).prod
      (gaussianReal ((u : ℝ) * theta) u) := by
  let f : ℝ × ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (Real.exp (theta * z.1 - (v : ℝ) * theta ^ 2 / 2)) *
      ENNReal.ofReal
        (Real.exp (theta * z.2 - (w : ℝ) * theta ^ 2 / 2))
  let g : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal
      (Real.exp (theta * x - (u : ℝ) * theta ^ 2 / 2))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  change (((gaussianReal 0 v).prod (gaussianReal 0 w)).prod
      (gaussianReal 0 u)).withDensity
      (fun z : (ℝ × ℝ) × ℝ => f z.1 * g z.2) =
    ((gaussianReal ((v : ℝ) * theta) v).prod
      (gaussianReal ((w : ℝ) * theta) w)).prod
      (gaussianReal ((u : ℝ) * theta) u)
  rw [← MeasureTheory.prod_withDensity
    (μ := (gaussianReal 0 v).prod (gaussianReal 0 w))
    (ν := gaussianReal 0 u) hf hg]
  rw [AppliedSDE.SarkkaSolin.gaussian_esscher_two_increment_measure
      v w hv hw theta,
    AppliedSDE.SarkkaSolin.gaussian_esscher_tilt_measure u hu theta]
