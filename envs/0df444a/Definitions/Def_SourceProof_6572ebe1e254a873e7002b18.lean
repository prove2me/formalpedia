-- Prove2me | Definitions.Def_SourceProof_6572ebe1e254a873e7002b18
-- name    : SourceProof_6572ebe1e254a873e7002b18
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:12:27.848739+00:00
-- url     : https://prove2.me/theorems/8cf7c937-0ef6-466b-819a-7134b896ac08
-- title:
--   LevyStochCalc source module: SourceProof_6572ebe1e254a873e7002b18
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_integrableOn_window` comes from the `LevyStochCalc.Poisson.CompensatorL1` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F002
import Definitions.Def_SourceProof_cee30bfb9b70a700a473aa9b

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


theorem _root_.Prove2MeSourceProof.h_6572ebe1e254a873e7002b18 (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η)
    (hm : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2)
    (hen : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => η ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)
      ∧ IntegrableOn (fun q : ℝ × E => η ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
          (referenceIntensity ν) := by
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν T
  have hmeanI : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η ω q.1 q.2‖ₑ ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (_root_.Prove2MeSourceProof.h_cee30bfb9b70a700a473aa9b hRfin hm)
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hen)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hRfin)
  have hmeanN : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω) ∂P ≠ ⊤ := by
    rw [LevyStochCalc.Poisson.lintegral_enorm_count_eq N hℱ hA hAν T hη]
    exact hmeanI
  obtain ⟨hcAE, hiM, -⟩ := _root_.Prove2MeSourceProof.h_a6be76747887c395a8454e6f N hℱ hA hAν T
    (Ψ := fun p : Ω × ℝ × E => ‖η p.1 p.2.1 p.2.2‖ₑ) (measurable_enorm.comp hη)
  have hslice : ∀ ω : Ω, Measurable fun q : ℝ × E => η ω q.1 q.2 :=
    fun ω => hm.comp measurable_prodMk_left
  filter_upwards [ae_lt_top' hcAE hmeanN, ae_lt_top' hiM.aemeasurable hmeanI] with ω hN hI
  exact ⟨⟨(hslice ω).stronglyMeasurable.aestronglyMeasurable, hN⟩,
    ⟨(hslice ω).stronglyMeasurable.aestronglyMeasurable, hI⟩⟩
end Pathwise

end LevyStochCalc.Poisson


