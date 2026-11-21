-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CellIntegrand_F000
-- name    : LevyStochCalc_Poisson_CellIntegrand_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:33:00.316183+00:00
-- url     : https://prove2.me/theorems/7dc2ac36-f0cd-48e2-b168-02347b229155
-- title:
--   Source declarations: LevyStochCalc.Poisson.CellIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CellIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003
import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F001
import Definitions.Def_LevyStochCalc_Probability_PredictableContinuous_F000
import Definitions.Def_SourceProof_6bebe70af91e345e56c64c09
import Definitions.Def_SourceProof_fd3bd66735f5f2c41b2b3f00

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

/-- A process cut to a window of the time–mark space. -/
noncomputable def cutWindow (X : ℝ → Ω → ℝ) (A : Set E) (τ : ℝ) (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  (Set.Ioc (0 : ℝ) τ ×ˢ A).indicator (fun _ : ℝ × E => X s ω) (s, e)
omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem cutWindow_eq_zero {X : ℝ → Ω → ℝ} {A : Set E} {τ : ℝ} {s : ℝ} {e : E}
    (h : ((s, e) : ℝ × E) ∉ Set.Ioc (0 : ℝ) τ ×ˢ A) (ω : Ω) : cutWindow X A τ ω s e = 0 :=
  Set.indicator_of_notMem h _
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Shrinking the domain of a set integral to where the integrand lives. -/
theorem setIntegral_eq_of_vanishing {μ : Measure (ℝ × E)} {S S' : Set (ℝ × E)}
    (hS : MeasurableSet S) (hSS' : S ⊆ S') {f : ℝ × E → ℝ}
    (hf : ∀ q ∈ S', q ∉ S → f q = 0) (hS'm : MeasurableSet S') :
    ∫ q in S', f q ∂μ = ∫ q in S, f q ∂μ := by
  have hcongr : ∫ q in S', f q ∂μ = ∫ q in S', S.indicator f q ∂μ := by
    refine setIntegral_congr_fun hS'm fun q hq => ?_
    by_cases hqS : q ∈ S
    · rw [Set.indicator_of_mem hqS]
    · rw [Set.indicator_of_notMem hqS, hf q hq hqS]
  rw [hcongr, setIntegral_indicator hS, Set.inter_eq_right.mpr hSS']
omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem cutWindow_eq {X : ℝ → Ω → ℝ} {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T) {e : E}
    (he : e ∈ A) (ω : Ω) : cutWindow X A T ω s e = X s ω := by
  have hmem : ((s, e) : ℝ × E) ∈ Set.Ioc (0 : ℝ) T ×ˢ A := ⟨⟨hs, hsT⟩, he⟩
  exact Set.indicator_of_mem hmem _
omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem abs_cutWindow_le {X : ℝ → Ω → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hX : ∀ s ω, |X s ω| ≤ C)
    (A : Set E) (T : ℝ) (ω : Ω) (s : ℝ) (e : E) : |cutWindow X A T ω s e| ≤ C := by
  unfold cutWindow
  by_cases h : ((s, e) : ℝ × E) ∈ Set.Ioc (0 : ℝ) T ×ˢ A
  · rw [Set.indicator_of_mem h]; exact hX s ω
  · rw [Set.indicator_of_notMem h, abs_zero]; exact hC0
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem measurable_uncurry_cutWindow {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) {A : Set E} (hA : MeasurableSet A)
    (T : ℝ) :
    Measurable fun p : Ω × ℝ × E => cutWindow X A T p.1 p.2.1 p.2.2 := by
  have h1 : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_fst.prodMk measurable_snd.fst)
  have h2 : MeasurableSet ((Set.Ioc (0 : ℝ) T ×ˢ A : Set (ℝ × E))) :=
    measurableSet_Ioc.prod hA
  have h3 : Measurable fun p : Ω × ℝ × E => ((p.2.1, p.2.2) : ℝ × E) :=
    measurable_snd.fst.prodMk measurable_snd.snd
  exact h1.indicator (h3 h2)
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A factor bounded by `C` scales the energy by at most `C²`. -/
theorem markedEnergy_bddMul_ne_top {φ ψ : Ω → ℝ → E → ℝ} {C T : ℝ}
    (hψ : ∀ ω s e, |ψ ω s e| ≤ C) (h : markedEnergy P ν T φ ≠ ⊤) :
    markedEnergy P ν T (fun ω s e => ψ ω s e * φ ω s e) ≠ ⊤ := by
  have hC : ENNReal.ofReal (C ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC h) ?_
  unfold markedEnergy
  rw [← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun s => ?_
  rw [← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun e => ?_
  rw [coe_nnnorm_sq_eq_ofReal_sq, coe_nnnorm_sq_eq_ofReal_sq,
    ← ENNReal.ofReal_mul (sq_nonneg C)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow, ← sq_abs (ψ ω s e)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hψ ω s e) 2) (sq_nonneg _)
namespace MarkedHorizonIntegrand

variable {T : ℝ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The cut factor times a predictable integrand is predictable. -/
theorem markedPredictable_cutMul {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {φ : Ω → ℝ → E → ℝ}
    (hφ : Probability.MarkedPredictable ℱ ν φ) (T : ℝ) :
    Probability.MarkedPredictable ℱ ν fun ω s e => cutWindow X A T ω s e * φ ω s e :=
  (_root_.Prove2MeSourceProof.h_fd3bd66735f5f2c41b2b3f00 hXc hXa hA hAν T).mul hφ
/-- A bounded continuous adapted process, cut to the window, times an admissible marked
integrand. -/
noncomputable def cutMul (G : MarkedHorizonIntegrand P ν ℱ T) {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {C : ℝ} (hC0 : 0 ≤ C) (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun) (τ : ℝ) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => cutWindow X A τ ω s e * G.toFun ω s e
  measurable_uncurry := by
    have hXjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) := by
      have h : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => X t ω) :=
        measurable_uncurry_of_continuous_of_measurable (fun ω => hXc ω)
          (fun t => ((hXa t).mono (ℱ.le t)).measurable)
      exact h.comp measurable_swap
    exact (measurable_uncurry_cutWindow hXjoint hA τ).mul G.measurable_uncurry
  progressive := (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (markedPredictable_cutMul hXc hXa hA hAν hGpred τ))
  vanishing := fun ω s e hs => by rw [G.vanishing ω s e hs, mul_zero]
  energy_ne_top := markedEnergy_bddMul_ne_top (abs_cutWindow_le hC0 hXb A τ) G.energy_ne_top
end MarkedHorizonIntegrand

end Cut

end LevyStochCalc.Poisson.Compensated


