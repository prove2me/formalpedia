-- Prove2me | Definitions.Def_SourceProof_c9b460a82af6b4349b617217
-- name    : SourceProof_c9b460a82af6b4349b617217
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:50:20.834613+00:00
-- url     : https://prove2.me/theorems/b587b557-8690-4c3e-85f7-f0d0ba74e47b
-- title:
--   LevyStochCalc source module: SourceProof_c9b460a82af6b4349b617217
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.aemeasurable_and_lintegral_slice_eq` comes from the `LevyStochCalc.Poisson.Compensator` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000

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


theorem _root_.Prove2MeSourceProof.h_c9b460a82af6b4349b617217 (hℱ : IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {S : Set (Ω × ℝ × E)} (hS : MeasurableSet[Probability.markedPredictableSigma ℱ ν] S) :
    AEMeasurable (sliceCount N (Set.Ioc (0 : ℝ) T ×ˢ A) S) P
      ∧ Measurable (sliceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) S)
      ∧ ∫⁻ ω, sliceCount N (Set.Ioc (0 : ℝ) T ×ˢ A) S ω ∂P
          = ∫⁻ ω, sliceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) S ω ∂P := by
  classical
  set R : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hRdef
  have hRm : MeasurableSet R := measurableSet_Ioc.prod hA
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ := LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν T
  have hNR : ∫⁻ ω, N.N ω R ∂P = LevyStochCalc.Poisson.referenceIntensity ν R :=
    _root_.Prove2MeSourceProof.h_9d62612e2dce26cbc374ccfb N hRm hRfin
  have hNRfin : ∀ᵐ ω ∂P, N.N ω R ≠ ⊤ := LevyStochCalc.Poisson.count_Ioc_ne_top N hA hAν T
  have hNRmeas : Measurable fun ω => N.N ω R := N.measurable_eval hRm
  have hIle : ∀ (S' : Set (Ω × ℝ × E)) (ω : Ω),
      LevyStochCalc.Poisson.sliceIntensity ν R S' ω ≤ LevyStochCalc.Poisson.referenceIntensity ν R :=
    fun _ _ => measure_mono Set.inter_subset_right
  have hIfin : ∀ S' : Set (Ω × ℝ × E), ∫⁻ ω, LevyStochCalc.Poisson.sliceIntensity ν R S' ω ∂P ≠ ⊤ := by
    intro S'
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω => hIle S' ω)
    rw [lintegral_const, measure_univ, mul_one]
    exact hRfin
  refine MeasurableSpace.induction_on_inter
    (C := fun S' _ => AEMeasurable (LevyStochCalc.Poisson.sliceCount N R S') P ∧ Measurable (LevyStochCalc.Poisson.sliceIntensity ν R S')
      ∧ ∫⁻ ω, LevyStochCalc.Poisson.sliceCount N R S' ω ∂P = ∫⁻ ω, LevyStochCalc.Poisson.sliceIntensity ν R S' ω ∂P)
    rfl (LevyStochCalc.Probability.isPiSystem_markedPredictableRect ℱ ν) ?_ ?_ ?_ ?_ S hS
  · have h0 : LevyStochCalc.Poisson.sliceCount N R ∅ = fun _ : Ω => (0 : ℝ≥0∞) := by
      funext ω; simp [LevyStochCalc.Poisson.sliceCount]
    have h1 : LevyStochCalc.Poisson.sliceIntensity ν R ∅ = fun _ : Ω => (0 : ℝ≥0∞) := by
      funext ω; simp [LevyStochCalc.Poisson.sliceIntensity]
    rw [h0, h1]
    exact ⟨measurable_const.aemeasurable, measurable_const, rfl⟩
  · rintro _ ⟨r, q, F, B, hr, hF, hB, hBν, rfl⟩
    have hFm : MeasurableSet F := ℱ.le r _ hF
    have hBA : MeasurableSet (B ∩ A) := hB.inter hA
    have hBAν : ν (B ∩ A) ≠ ⊤ := ne_top_of_le_ne_top hBν (measure_mono Set.inter_subset_left)
    have hrectm : MeasurableSet (Set.Ioc r (min q T) ×ˢ (B ∩ A)) := measurableSet_Ioc.prod hBA
    have hslice : ∀ ω : Ω, Prod.mk ω ⁻¹' (F ×ˢ (Set.Ioc r q ×ˢ B)) ∩ R
        = if ω ∈ F then Set.Ioc r (min q T) ×ˢ (B ∩ A) else ∅ := by
      intro ω
      by_cases hω : ω ∈ F
      · rw [if_pos hω, hRdef]
        ext p
        have hpos : r < p.1 → (0 : ℝ) < p.1 := fun h => lt_of_le_of_lt hr h
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_Ioc, le_min_iff,
          hω, true_and]
        tauto
      · rw [if_neg hω]
        ext p
        simp [hω]
    have hcount : LevyStochCalc.Poisson.sliceCount N R (F ×ˢ (Set.Ioc r q ×ˢ B))
        = F.indicator fun ω => N.N ω (Set.Ioc r (min q T) ×ˢ (B ∩ A)) := by
      funext ω
      rw [LevyStochCalc.Poisson.sliceCount, hslice ω]
      by_cases hω : ω ∈ F
      · rw [if_pos hω, Set.indicator_of_mem hω]
      · rw [if_neg hω, Set.indicator_of_notMem hω, measure_empty]
    have hint : LevyStochCalc.Poisson.sliceIntensity ν R (F ×ˢ (Set.Ioc r q ×ˢ B))
        = F.indicator fun _ => LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc r (min q T) ×ˢ (B ∩ A)) := by
      funext ω
      rw [LevyStochCalc.Poisson.sliceIntensity, hslice ω]
      by_cases hω : ω ∈ F
      · rw [if_pos hω, Set.indicator_of_mem hω]
      · rw [if_neg hω, Set.indicator_of_notMem hω, measure_empty]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcount]
      exact ((N.measurable_eval hrectm).indicator hFm).aemeasurable
    · rw [hint]
      exact measurable_const.indicator hFm
    · rw [hcount, hint, lintegral_indicator hFm, lintegral_indicator hFm,
        LevyStochCalc.Poisson.setLIntegral_count_eq N hℱ hr hF hBA hBAν, setLIntegral_const]
      exact mul_comm _ _
  · rintro S' hSm ⟨ihc, ihi, ihe⟩
    have hXm : ∀ ω : Ω, MeasurableSet (Prod.mk ω ⁻¹' S') :=
      fun ω => LevyStochCalc.Probability.measurableSet_slice hSm ω
    have hCfin : ∫⁻ ω, LevyStochCalc.Poisson.sliceCount N R S' ω ∂P ≠ ⊤ := by rw [ihe]; exact hIfin S'
    have hCle : ∀ᵐ ω ∂P, LevyStochCalc.Poisson.sliceCount N R S' ω ≤ N.N ω R :=
      Filter.Eventually.of_forall fun _ => measure_mono Set.inter_subset_right
    have hcompl' : LevyStochCalc.Poisson.sliceCount N R S'ᶜ =ᵐ[P] fun ω => N.N ω R - LevyStochCalc.Poisson.sliceCount N R S' ω := by
      filter_upwards [hNRfin] with ω hω
      have hsum : N.N ω (R ∩ Prod.mk ω ⁻¹' S') + N.N ω (R \ Prod.mk ω ⁻¹' S') = N.N ω R :=
        measure_inter_add_sdiff _ (hXm ω)
      have h1 : LevyStochCalc.Poisson.sliceCount N R S' ω = N.N ω (R ∩ Prod.mk ω ⁻¹' S') := by
        rw [LevyStochCalc.Poisson.sliceCount, Set.inter_comm]
      have h2 : LevyStochCalc.Poisson.sliceCount N R S'ᶜ ω = N.N ω (R \ Prod.mk ω ⁻¹' S') := by
        rw [LevyStochCalc.Poisson.sliceCount, Set.preimage_compl, Set.inter_comm, Set.sdiff_eq]
      rw [h1, h2, ← hsum]
      refine (ENNReal.add_sub_cancel_left ?_).symm
      exact ne_top_of_le_ne_top hω (measure_mono Set.inter_subset_left)
    have hicompl : LevyStochCalc.Poisson.sliceIntensity ν R S'ᶜ
        = fun ω => LevyStochCalc.Poisson.referenceIntensity ν R - LevyStochCalc.Poisson.sliceIntensity ν R S' ω := by
      funext ω
      have hsum : LevyStochCalc.Poisson.referenceIntensity ν (R ∩ Prod.mk ω ⁻¹' S')
          + LevyStochCalc.Poisson.referenceIntensity ν (R \ Prod.mk ω ⁻¹' S') = LevyStochCalc.Poisson.referenceIntensity ν R :=
        measure_inter_add_sdiff _ (hXm ω)
      have h1 : LevyStochCalc.Poisson.sliceIntensity ν R S' ω = LevyStochCalc.Poisson.referenceIntensity ν (R ∩ Prod.mk ω ⁻¹' S') := by
        rw [LevyStochCalc.Poisson.sliceIntensity, Set.inter_comm]
      have h2 : LevyStochCalc.Poisson.sliceIntensity ν R S'ᶜ ω = LevyStochCalc.Poisson.referenceIntensity ν (R \ Prod.mk ω ⁻¹' S') := by
        rw [LevyStochCalc.Poisson.sliceIntensity, Set.preimage_compl, Set.inter_comm, Set.sdiff_eq]
      rw [h1, h2, ← hsum]
      refine (ENNReal.add_sub_cancel_left ?_).symm
      exact ne_top_of_le_ne_top hRfin (measure_mono Set.inter_subset_left)
    refine ⟨?_, ?_, ?_⟩
    · exact (hNRmeas.aemeasurable.sub ihc).congr hcompl'.symm
    · rw [hicompl]
      exact measurable_const.sub ihi
    · rw [lintegral_congr_ae hcompl', hicompl, lintegral_sub' ihc hCfin hCle,
        lintegral_sub ihi (hIfin S') (Filter.Eventually.of_forall fun ω => hIle S' ω), hNR,
        lintegral_const, measure_univ, mul_one, ihe]
  · intro f hd hfm ih
    have hdisj : ∀ ω : Ω, Pairwise (Function.onFun Disjoint
        fun i => Prod.mk ω ⁻¹' f i ∩ R) := fun ω i j hij =>
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left
        ((hd hij).preimage (Prod.mk ω))
    have hslice : ∀ ω : Ω, Prod.mk ω ⁻¹' (⋃ i, f i) ∩ R = ⋃ i, Prod.mk ω ⁻¹' f i ∩ R := by
      intro ω
      rw [Set.preimage_iUnion, Set.iUnion_inter]
    have hcount : LevyStochCalc.Poisson.sliceCount N R (⋃ i, f i) = fun ω => ∑' i, LevyStochCalc.Poisson.sliceCount N R (f i) ω := by
      funext ω
      rw [LevyStochCalc.Poisson.sliceCount, hslice ω,
        measure_iUnion (hdisj ω) fun i => (LevyStochCalc.Probability.measurableSet_slice (hfm i) ω).inter hRm]
      rfl
    have hint : LevyStochCalc.Poisson.sliceIntensity ν R (⋃ i, f i) = fun ω => ∑' i, LevyStochCalc.Poisson.sliceIntensity ν R (f i) ω := by
      funext ω
      rw [LevyStochCalc.Poisson.sliceIntensity, hslice ω,
        measure_iUnion (hdisj ω) fun i => (LevyStochCalc.Probability.measurableSet_slice (hfm i) ω).inter hRm]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hcount]
      exact AEMeasurable.tsum fun i => (ih i).1
    · rw [hint]
      exact Measurable.tsum fun i => (ih i).2.1
    · rw [hcount, hint, lintegral_tsum fun i => (ih i).1,
        lintegral_tsum fun i => (ih i).2.1.aemeasurable]
      exact tsum_congr fun i => (ih i).2.2
end Window

end LevyStochCalc.Poisson


