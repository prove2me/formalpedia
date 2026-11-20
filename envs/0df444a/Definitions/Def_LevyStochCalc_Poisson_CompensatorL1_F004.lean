-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F004
-- name    : LevyStochCalc_Poisson_CompensatorL1_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:22:07.025176+00:00
-- url     : https://prove2.me/theorems/53d9f4e7-d6db-469f-a918-08d574ecad5f
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatorL1
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatorL1. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001

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

omit [IsProbabilityMeasure P] in
/-- The pathwise integral against the reference intensity, as a function of the sample point. -/
theorem stronglyMeasurable_pathwise_intensity {η : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2) (A : Set E) (T : ℝ) :
    StronglyMeasurable
      fun ω => ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(referenceIntensity ν) := by
  haveI : SigmaFinite (referenceIntensity ν) := by
    rw [referenceIntensity]
    infer_instance
  exact StronglyMeasurable.integral_prod_right'
    (ν := (referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) hm.stronglyMeasurable
end Pathwise

end LevyStochCalc.Poisson


