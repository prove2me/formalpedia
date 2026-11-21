-- Prove2me | Definitions.Def_SourceProof_31426d8eac40eee65570d324
-- name    : SourceProof_31426d8eac40eee65570d324
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:43.565178+00:00
-- url     : https://prove2.me/theorems/4b872f4c-8cdb-450b-931b-e8b3e4c305c7
-- title:
--   LevyStochCalc source module: SourceProof_31426d8eac40eee65570d324
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.setIntegral_count_eq_integral_add` comes from the `LevyStochCalc.Poisson.CellIntegrand` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CellIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A continuous adapted factor in a marked integrand

A bounded continuous adapted process, cut to a window of finite mark measure, multiplies a
predictable marked integrand carried by that window into another one: the product is predictable
(`Probability/PredictableContinuous.lean`), vanishes off the horizon and has finite energy. Since
the product is predictable it is pathwise, so on the window the integral of the product against
the random measure is its compensated integral plus its integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Cut

namespace MarkedHorizonIntegrand

variable {T : ℝ}


theorem _root_.Prove2MeSourceProof.h_31426d8eac40eee65570d324 (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (G : MarkedHorizonIntegrand P ν ℱ T) {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {C : ℝ} (hC0 : 0 ≤ C) (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun) (hT : 0 < T)
    {τ : ℝ} (hτT : τ ≤ T) :
    ∀ᵐ ω ∂P, (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω))
      = (G.cutMul hXc hXa hC0 hXb hA hAν hGpred τ).integral N hℱ ω
        + ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
            X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν) := by
  set F := G.cutMul hXc hXa hC0 hXb hA hAν hGpred τ with hF
  have hsupp : ∀ (ω : Ω) (s : ℝ) (e : E), e ∉ A → F.toFun ω s e = 0 := by
    intro ω s e he
    have : LevyStochCalc.Poisson.Compensated.cutWindow X A τ ω s e = 0 :=
      Set.indicator_of_notMem (fun hmem => he hmem.2) _
    change LevyStochCalc.Poisson.Compensated.cutWindow X A τ ω s e * G.toFun ω s e = 0
    rw [this, zero_mul]
  have hpath := LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱ F.toFun F.measurable_uncurry
    F.progressive F.sq_int_global hA
    (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.markedPredictable_cutMul hXc hXa hA hAν hGpred τ) hAν hsupp hT
  have hWm : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  have hSm : MeasurableSet (Set.Ioc (0 : ℝ) τ ×ˢ A) := measurableSet_Ioc.prod hA
  have hSS : (Set.Ioc (0 : ℝ) τ ×ˢ A : Set (ℝ × E)) ⊆ Set.Ioc (0 : ℝ) T ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right hτT) le_rfl
  have hcongr : ∀ (μ : Measure (ℝ × E)) (ω : Ω),
      (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, F.toFun ω q.1 q.2 ∂μ)
        = ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, X q.1 ω * G.toFun ω q.1 q.2 ∂μ := by
    intro μ ω
    have hshrink : (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, F.toFun ω q.1 q.2 ∂μ)
        = ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, F.toFun ω q.1 q.2 ∂μ := by
      refine LevyStochCalc.Poisson.Compensated.setIntegral_eq_of_vanishing hSm hSS (fun q _ hq => ?_) hWm
      change LevyStochCalc.Poisson.Compensated.cutWindow X A τ ω q.1 q.2 * G.toFun ω q.1 q.2 = 0
      rw [LevyStochCalc.Poisson.Compensated.cutWindow_eq_zero (by simpa using hq) ω, zero_mul]
    rw [hshrink]
    refine setIntegral_congr_fun hSm fun q hq => ?_
    change LevyStochCalc.Poisson.Compensated.cutWindow X A τ ω q.1 q.2 * G.toFun ω q.1 q.2 = _
    rw [LevyStochCalc.Poisson.Compensated.cutWindow_eq hq.1.1 hq.1.2 hq.2]
  filter_upwards [hpath] with ω hω
  have hI : F.integral N hℱ ω
      = (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
            X q.1 ω * G.toFun ω q.1 q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
    rw [LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral, hω, hcongr (N.N ω) ω, hcongr (LevyStochCalc.Poisson.referenceIntensity ν) ω]
  rw [hI]
  ring
end MarkedHorizonIntegrand

end Cut

end LevyStochCalc.Poisson.Compensated


