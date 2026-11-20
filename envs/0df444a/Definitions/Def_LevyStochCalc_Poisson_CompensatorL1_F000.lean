-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F000
-- name    : LevyStochCalc_Poisson_CompensatorL1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:54:12.668054+00:00
-- url     : https://prove2.me/theorems/3a4429c3-1f6f-4309-95ce-8b796c592dd2
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

omit [IsProbabilityMeasure P] in
/-- The reference intensity of a window, as an iterated integral over time and marks. -/
theorem lintegral_referenceIntensity_window {f : ℝ × E → ℝ≥0∞} (hf : Measurable f)
    (A : Set E) (T : ℝ) :
    ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, f q ∂(referenceIntensity ν)
      = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e in A, f (s, e) ∂ν ∂volume := by
  have hsub : Set.Ioc (0 : ℝ) T ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) T := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => h.1.le
  have hres : (referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
      = (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A) := by
    rw [referenceIntensity, ← Measure.prod_restrict,
      Measure.restrict_restrict measurableSet_Ioc, hsub]
  rw [hres, lintegral_prod _ hf.aemeasurable]
end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

end Pathwise

end LevyStochCalc.Poisson


