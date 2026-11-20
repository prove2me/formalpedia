-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F002
-- name    : LevyStochCalc_Poisson_CompensatorL1_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:16:25.448481+00:00
-- url     : https://prove2.me/theorems/294e633f-5ac9-4dd6-970c-78d962d9ccad
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

/-- The compensator identity for the size of a predictable marked integrand. -/
theorem lintegral_enorm_count_eq (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω) ∂P
      = ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P :=
  lintegral_lintegral_slice_eq N hℱ hA hAν T (Ψ := fun p => ‖η p.1 p.2.1 p.2.2‖ₑ)
    (measurable_enorm.comp hη)
/-- **The mean size of the pathwise compensated integral is at most twice the mean size against
the reference intensity.** -/
theorem lintegral_enorm_pathwise_le (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η) :
    ∫⁻ ω, ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ ∂P
      ≤ 2 * ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P := by
  obtain ⟨hc, -, -⟩ := _root_.Prove2MeSourceProof.h_a6be76747887c395a8454e6f N hℱ hA hAν T
    (Ψ := fun p : Ω × ℝ × E => ‖η p.1 p.2.1 p.2.2‖ₑ) (measurable_enorm.comp hη)
  have hstep : ∀ ω : Ω,
      ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ
      ≤ (∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω))
          + ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
              ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) := fun ω =>
    le_trans enorm_sub_le
      (add_le_add (enorm_integral_le_lintegral_enorm _) (enorm_integral_le_lintegral_enorm _))
  calc ∫⁻ ω, ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω))
          - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ ∂P
      ≤ ∫⁻ ω, ((∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω))
          + ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
              ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν)) ∂P := lintegral_mono hstep
    _ = (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω) ∂P)
          + ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
              ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P := lintegral_add_left' hc _
    _ = 2 * ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P := by
        rw [lintegral_enorm_count_eq N hℱ hA hAν T hη, two_mul]
end Pathwise

end LevyStochCalc.Poisson


