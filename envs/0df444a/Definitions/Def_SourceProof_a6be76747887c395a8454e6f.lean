-- Prove2me | Definitions.Def_SourceProof_a6be76747887c395a8454e6f
-- name    : SourceProof_a6be76747887c395a8454e6f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:51:15.067154+00:00
-- url     : https://prove2.me/theorems/6b0da503-63a4-4e56-bc8d-ef3f827b6257
-- title:
--   LevyStochCalc source module: SourceProof_a6be76747887c395a8454e6f
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.aemeasurable_and_lintegral_lintegral_slice_eq` comes from the `LevyStochCalc.Poisson.Compensator` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_SourceProof_c9b460a82af6b4349b617217

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The reference intensity as compensator on a finite-activity window

On a predictable rectangle the count of the Poisson random measure is independent of the past
event carried by the rectangle, so its mean factorises as the probability of that event times
the intensity of the time–mark part. The sets on which the two mean occupations agree form a
Dynkin system — complements by subtracting from the finite occupation of the window, countable
disjoint unions by monotone convergence — so they agree on every predictable set.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Rectangle

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Rectangle

section Window

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_a6be76747887c395a8454e6f (hℱ : IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {Ψ : Ω × ℝ × E → ℝ≥0∞}
    (hΨ : Measurable[Probability.markedPredictableSigma ℱ ν] Ψ) :
    AEMeasurable (fun ω => ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(N.N ω)) P
      ∧ Measurable (fun ω =>
          ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(referenceIntensity ν))
      ∧ ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(N.N ω) ∂P
          = ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(referenceIntensity ν) ∂P := by
  classical
  set R : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hRdef
  have hslicemeas : ∀ {G : Ω × ℝ × E → ℝ≥0∞},
      Measurable[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] G →
      ∀ ω : Ω, Measurable fun p : ℝ × E => G (ω, p) := by
    intro G hG ω
    exact (hG.mono (LevyStochCalc.Probability.markedPredictableSigma_le ℱ ν) le_rfl).comp
      measurable_prodMk_left
  refine (@Measurable.ennreal_induction (Ω × ℝ × E)
    (LevyStochCalc.Probability.markedPredictableSigma ℱ ν)
    (fun G => AEMeasurable (fun ω => ∫⁻ p in R, G (ω, p) ∂(N.N ω)) P
      ∧ Measurable (fun ω => ∫⁻ p in R, G (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν))
      ∧ ∫⁻ ω, ∫⁻ p in R, G (ω, p) ∂(N.N ω) ∂P
          = ∫⁻ ω, ∫⁻ p in R, G (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P)
    ?_ ?_ ?_ Ψ hΨ)
  · intro c S hS
    obtain ⟨hc, hi, he⟩ := _root_.Prove2MeSourceProof.h_c9b460a82af6b4349b617217 N hℱ hA hAν T hS
    have hXm : ∀ ω : Ω, MeasurableSet (Prod.mk ω ⁻¹' S) :=
      fun ω => LevyStochCalc.Probability.measurableSet_slice hS ω
    have hpt : ∀ (μ : Measure (ℝ × E)) (ω : Ω),
        ∫⁻ p in R, (Set.indicator S fun _ => c) (ω, p) ∂μ = c * μ (Prod.mk ω ⁻¹' S ∩ R) := by
      intro μ ω
      have hfun : (fun p : ℝ × E => (Set.indicator S fun _ => c) (ω, p))
          = (Prod.mk ω ⁻¹' S).indicator fun _ => c := by
        funext p
        by_cases hp : (ω, p) ∈ S
        · rw [Set.indicator_of_mem hp,
            Set.indicator_of_mem (show p ∈ Prod.mk ω ⁻¹' S from hp)]
        · rw [Set.indicator_of_notMem hp,
            Set.indicator_of_notMem (show p ∉ Prod.mk ω ⁻¹' S from hp)]
      rw [hfun, lintegral_indicator (hXm ω), setLIntegral_const,
        Measure.restrict_apply (hXm ω), mul_comm]
    have hN : (fun ω => ∫⁻ p in R, (Set.indicator S fun _ => c) (ω, p) ∂(N.N ω))
        = fun ω => c * LevyStochCalc.Poisson.sliceCount N R S ω := funext fun ω => hpt (N.N ω) ω
    have hI : (fun ω => ∫⁻ p in R, (Set.indicator S fun _ => c) (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν))
        = fun ω => c * LevyStochCalc.Poisson.sliceIntensity ν R S ω := funext fun ω => hpt (LevyStochCalc.Poisson.referenceIntensity ν) ω
    refine ⟨?_, ?_, ?_⟩
    · rw [hN]; exact hc.const_mul c
    · rw [hI]; exact hi.const_mul c
    · rw [hN, hI, lintegral_const_mul'' c hc, lintegral_const_mul'' c hi.aemeasurable, he]
  · rintro f g - hf hg ⟨hcf, hif, hef⟩ ⟨hcg, hig, heg⟩
    have hsplit : ∀ (μ : Measure (ℝ × E)) (ω : Ω), Measurable (fun p : ℝ × E => f (ω, p)) →
        ∫⁻ p in R, (f + g) (ω, p) ∂μ
          = (∫⁻ p in R, f (ω, p) ∂μ) + ∫⁻ p in R, g (ω, p) ∂μ := by
      intro μ ω hfω
      exact lintegral_add_left hfω _
    have hN : (fun ω => ∫⁻ p in R, (f + g) (ω, p) ∂(N.N ω))
        = fun ω => (∫⁻ p in R, f (ω, p) ∂(N.N ω)) + ∫⁻ p in R, g (ω, p) ∂(N.N ω) :=
      funext fun ω => hsplit (N.N ω) ω (hslicemeas hf ω)
    have hI : (fun ω => ∫⁻ p in R, (f + g) (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν))
        = fun ω => (∫⁻ p in R, f (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν))
            + ∫⁻ p in R, g (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν) :=
      funext fun ω => hsplit (LevyStochCalc.Poisson.referenceIntensity ν) ω (hslicemeas hf ω)
    refine ⟨?_, ?_, ?_⟩
    · rw [hN]; exact hcf.add hcg
    · rw [hI]; exact hif.add hig
    · rw [hN, hI, lintegral_add_left' hcf, lintegral_add_left' hif.aemeasurable, hef, heg]
  · intro f hf hmono ih
    have hN : (fun ω => ∫⁻ p in R, (⨆ n, f n (ω, p)) ∂(N.N ω))
        = fun ω => ⨆ n, ∫⁻ p in R, f n (ω, p) ∂(N.N ω) := by
      funext ω
      exact lintegral_iSup (fun n => hslicemeas (hf n) ω)
        (fun m n hmn p => hmono hmn (ω, p))
    have hI : (fun ω => ∫⁻ p in R, (⨆ n, f n (ω, p)) ∂(LevyStochCalc.Poisson.referenceIntensity ν))
        = fun ω => ⨆ n, ∫⁻ p in R, f n (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      funext ω
      exact lintegral_iSup (fun n => hslicemeas (hf n) ω)
        (fun m n hmn p => hmono hmn (ω, p))
    have hmonoN : ∀ ω : Ω, Monotone fun n => ∫⁻ p in R, f n (ω, p) ∂(N.N ω) :=
      fun ω m n hmn => lintegral_mono fun p => hmono hmn (ω, p)
    have hmonoI : ∀ ω : Ω, Monotone fun n => ∫⁻ p in R, f n (ω, p) ∂(LevyStochCalc.Poisson.referenceIntensity ν) :=
      fun ω m n hmn => lintegral_mono fun p => hmono hmn (ω, p)
    refine ⟨?_, ?_, ?_⟩
    · rw [hN]; exact AEMeasurable.iSup fun n => (ih n).1
    · rw [hI]; exact Measurable.iSup fun n => (ih n).2.1
    · rw [hN, hI, lintegral_iSup' (fun n => (ih n).1)
        (Filter.Eventually.of_forall hmonoN),
        lintegral_iSup' (fun n => ((ih n).2.1).aemeasurable)
        (Filter.Eventually.of_forall hmonoI)]
      exact iSup_congr fun n => (ih n).2.2
end Window

end LevyStochCalc.Poisson


