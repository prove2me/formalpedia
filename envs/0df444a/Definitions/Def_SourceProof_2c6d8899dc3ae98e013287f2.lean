-- Prove2me | Definitions.Def_SourceProof_2c6d8899dc3ae98e013287f2
-- name    : SourceProof_2c6d8899dc3ae98e013287f2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:24:08.647169+00:00
-- url     : https://prove2.me/theorems/60bf6f32-2553-4dce-81cf-e53fc5654cd1
-- title:
--   LevyStochCalc source module: SourceProof_2c6d8899dc3ae98e013287f2
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.aestronglyMeasurable_pathwise_count` comes from the `LevyStochCalc.Poisson.CompensatorL1` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_6572ebe1e254a873e7002b18

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}


theorem _root_.Prove2MeSourceProof.h_2c6d8899dc3ae98e013287f2 (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η)
    (hm : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2)
    (hen : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P ≠ ⊤) :
    AEStronglyMeasurable
      (fun ω => ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω)) P := by
  obtain ⟨hpos, -, -⟩ := _root_.Prove2MeSourceProof.h_a6be76747887c395a8454e6f N hℱ hA hAν T
    (Ψ := fun p : Ω × ℝ × E => ENNReal.ofReal (η p.1 p.2.1 p.2.2))
    (ENNReal.measurable_ofReal.comp hη)
  obtain ⟨hneg, -, -⟩ := _root_.Prove2MeSourceProof.h_a6be76747887c395a8454e6f N hℱ hA hAν T
    (Ψ := fun p : Ω × ℝ × E => ENNReal.ofReal (-η p.1 p.2.1 p.2.2))
    (ENNReal.measurable_ofReal.comp hη.neg)
  refine AEStronglyMeasurable.congr
    (((ENNReal.measurable_toReal.comp_aemeasurable hpos).sub
      (ENNReal.measurable_toReal.comp_aemeasurable hneg)).aestronglyMeasurable) ?_
  filter_upwards [_root_.Prove2MeSourceProof.h_6572ebe1e254a873e7002b18 N hℱ hA hAν T hη hm hen] with ω hω
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω.1).symm
end Pathwise

end LevyStochCalc.Poisson


