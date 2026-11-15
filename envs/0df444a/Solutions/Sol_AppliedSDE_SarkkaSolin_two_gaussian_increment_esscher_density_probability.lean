-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.two_gaussian_increment_esscher_density_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:01:20.812202+00:00
-- url     : https://prove2.me/submissions/4047072b-d162-4421-9ec7-ff612eb336a5

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_joint_gaussian_increment_esscher_under_weighted_measure
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
    IsProbabilityMeasure
      (P.withDensity (fun ω =>
        ENNReal.ofReal
          (Real.exp (theta * X ω - (v : ℝ) * theta ^ 2 / 2)) *
        ENNReal.ofReal
          (Real.exp (theta * Y ω - (w : ℝ) * theta ^ 2 / 2)))) := by
  let Q : Measure Ω := P.withDensity (fun ω =>
    ENNReal.ofReal
      (Real.exp (theta * X ω - (v : ℝ) * theta ^ 2 / 2)) *
    ENNReal.ofReal
      (Real.exp (theta * Y ω - (w : ℝ) * theta ^ 2 / 2)))
  let Z : Ω → ℝ × ℝ := fun ω => (X ω, Y ω)
  have hlaw : Q.map Z =
      (gaussianReal ((v : ℝ) * theta) v).prod
        (gaussianReal ((w : ℝ) * theta) w) :=
    AppliedSDE.SarkkaSolin.joint_gaussian_increment_esscher_under_weighted_measure
      X Y v w hv hw theta hZ hXY
  change IsProbabilityMeasure Q
  refine ⟨?_⟩
  calc
    Q Set.univ = (Q.map Z) Set.univ := by
      rw [Measure.map_apply hZ MeasurableSet.univ]
      simp
    _ = ((gaussianReal ((v : ℝ) * theta) v).prod
        (gaussianReal ((w : ℝ) * theta) w)) Set.univ := by rw [hlaw]
    _ = 1 := by simp
