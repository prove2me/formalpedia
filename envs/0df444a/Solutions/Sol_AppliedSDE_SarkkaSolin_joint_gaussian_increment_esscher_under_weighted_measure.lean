-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.joint_gaussian_increment_esscher_under_weighted_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:47:17.162277+00:00
-- url     : https://prove2.me/submissions/5a1dcb58-c943-4723-9244-8a02dfa2efae

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_likelihood_tilt_pushforward
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_two_increment_measure
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w)
    (theta : ℝ)
    (hZ : Measurable (fun ω : Ω => (X ω, Y ω)))
    (hXY : HasLaw (fun ω : Ω => (X ω, Y ω))
      ((gaussianReal 0 v).prod (gaussianReal 0 w)) P) :
    (P.withDensity (fun ω =>
        ENNReal.ofReal
          (Real.exp (theta * X ω - (v : ℝ) * theta ^ 2 / 2)) *
        ENNReal.ofReal
          (Real.exp (theta * Y ω - (w : ℝ) * theta ^ 2 / 2)))).map
        (fun ω : Ω => (X ω, Y ω)) =
      (gaussianReal ((v : ℝ) * theta) v).prod
        (gaussianReal ((w : ℝ) * theta) w) := by
  let Z : Ω → ℝ × ℝ := fun ω => (X ω, Y ω)
  let f : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal
      (Real.exp (theta * p.1 - (v : ℝ) * theta ^ 2 / 2)) *
    ENNReal.ofReal
      (Real.exp (theta * p.2 - (w : ℝ) * theta ^ 2 / 2))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hpush := AppliedSDE.SarkkaSolin.likelihood_tilt_pushforward
    P Z hZ f hf
  change (P.withDensity (fun ω => f (Z ω))).map Z =
    (gaussianReal ((v : ℝ) * theta) v).prod
      (gaussianReal ((w : ℝ) * theta) w)
  calc
    (P.withDensity (fun ω => f (Z ω))).map Z =
      (P.map Z).withDensity f := hpush
    _ = ((gaussianReal 0 v).prod (gaussianReal 0 w)).withDensity f := by
      rw [hXY.map_eq]
    _ = (gaussianReal ((v : ℝ) * theta) v).prod
      (gaussianReal ((w : ℝ) * theta) w) :=
      AppliedSDE.SarkkaSolin.gaussian_esscher_two_increment_measure
        v w hv hw theta
