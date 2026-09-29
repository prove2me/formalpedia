-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/42214ede-079f-54ef-8e05-0614f914e3d4

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram
p2m_attr_erase "instance" "instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace SwapCore

theorem integrable_of_bound_of_ae_support {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (s : Set X) (hs : MeasurableSet s) (hμs : μ s < ⊤) (B : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ B) (h0 : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : Integrable f μ := by
  have hind : (fun x => s.indicator f x) =ᵐ[μ] f := by
    filter_upwards [h0] with x hx
    by_cases hxs : x ∈ s
    · simp [Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem hxs, hx hxs]
  refine Integrable.congr ?_ hind
  rw [integrable_indicator_iff hs]
  refine Measure.integrableOn_of_bounded (M := B) hμs.ne hf ?_
  exact ae_of_all _ fun x => hb x

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem levels (τ : Measure α) (κ : Measure β) (ν : Measure γ) [SFinite τ] [IsFiniteMeasure κ] [SFinite ν]
    (ξ : γ → ℂ) (hξm : Measurable ξ) (Mξ : ℝ) (hMξ : 0 ≤ Mξ) (Cz : Set γ) (hCz : MeasurableSet Cz)
    (hξb : ∀ z ∈ Cz, ‖ξ z‖ ≤ Mξ) (hν : ν Cz < ⊤) (Ct : Set α) (hCt : MeasurableSet Ct) (hτ : τ Ct < ⊤)
    (R : α → β → γ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hRm : Measurable fun p : α × β × γ => R p.1 p.2.1 p.2.2)
    (hRb : ∀ t k z, ‖R t k z‖ ≤ B) (hRz : ∀ t k z, z ∉ Cz → R t k z = 0)
    (hRt : ∀ᵐ t ∂τ, t ∉ Ct → ∀ k z, R t k z = 0) :
    (∀ t k, Integrable (fun z => ξ z * R t k z) ν) ∧
    (∀ t, Integrable (fun k => ∫ z, ξ z * R t k z ∂ν) κ) ∧
    Integrable (fun t => ∫ k, ∫ z, ξ z * R t k z ∂ν ∂κ) τ ∧
    (∀ t k, ‖∫ z, ξ z * R t k z ∂ν‖ ≤ Mξ * B * ν.real Cz) := by
  have hm1 : Measurable fun p : α × β × γ => ξ p.2.2 * R p.1 p.2.1 p.2.2 :=
    (hξm.comp measurable_snd.snd).mul hRm
  have hbz : ∀ t k z, ‖ξ z * R t k z‖ ≤ Mξ * B := by
    intro t k z
    by_cases hz : z ∈ Cz
    · rw [norm_mul]; exact mul_le_mul (hξb z hz) (hRb t k z) (norm_nonneg _) hMξ
    · rw [hRz t k z hz, mul_zero, norm_zero]; positivity
  have hI1 : ∀ t k, Integrable (fun z => ξ z * R t k z) ν := by
    intro t k
    refine integrable_of_bound_of_ae_support ν _ ?_ Cz hCz hν (Mξ * B) (hbz t k) (ae_of_all _ fun z hz => ?_)
    · exact (hm1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    · rw [hRz t k z hz, mul_zero]
  have hm2 : Measurable fun p : α × β => ∫ z, ξ z * R p.1 p.2 z ∂ν := by
    have : Measurable fun q : (α × β) × γ => ξ q.2 * R q.1.1 q.1.2 q.2 :=
      hm1.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact (this.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hb2 : ∀ t k, ‖∫ z, ξ z * R t k z ∂ν‖ ≤ Mξ * B * ν.real Cz := by
    intro t k
    have h0 : ∫ z, ξ z * R t k z ∂ν = ∫ z in Cz, ξ z * R t k z ∂ν := by
      rw [← integral_indicator hCz]
      congr 1; funext z
      by_cases hz : z ∈ Cz
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hRz t k z hz, mul_zero]
    rw [h0]
    exact norm_setIntegral_le_of_norm_le_const hν (fun z _ => hbz t k z)
  have hI2 : ∀ t, Integrable (fun k => ∫ z, ξ z * R t k z ∂ν) κ := by
    intro t
    refine ⟨(hm2.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
    exact HasFiniteIntegral.of_bounded (C := Mξ * B * ν.real Cz) (ae_of_all _ fun k => hb2 t k)
  have hm3 : Measurable fun t : α => ∫ k, ∫ z, ξ z * R t k z ∂ν ∂κ :=
    (hm2.stronglyMeasurable.integral_prod_right' (ν := κ)).measurable
  have hb3 : ∀ t, ‖∫ k, ∫ z, ξ z * R t k z ∂ν ∂κ‖ ≤ Mξ * B * ν.real Cz * κ.real Set.univ := by
    intro t
    have := norm_integral_le_of_norm_le_const (μ := κ) (C := Mξ * B * ν.real Cz) (ae_of_all _ fun k => hb2 t k)
    simpa [mul_comm] using this
  have hI3 : Integrable (fun t => ∫ k, ∫ z, ξ z * R t k z ∂ν ∂κ) τ := by
    refine integrable_of_bound_of_ae_support τ _ hm3.aestronglyMeasurable Ct hCt hτ _ hb3 ?_
    filter_upwards [hRt] with t ht hnt
    have : ∀ k, (∫ z, ξ z * R t k z ∂ν) = 0 := fun k => by simp [ht hnt k]
    simp [this]
  exact ⟨hI1, hI2, hI3, hb2⟩

theorem fubini4 (τ : Measure α) (κ : Measure β) (ν : Measure γ) (μ : Measure δ)
    [SFinite τ] [IsFiniteMeasure κ] [SFinite ν] [SFinite μ]
    (ξ : γ → ℂ) (hξm : Measurable ξ) (Mξ : ℝ) (hMξ : 0 ≤ Mξ) (Cz : Set γ) (hCz : MeasurableSet Cz)
    (hξb : ∀ z ∈ Cz, ‖ξ z‖ ≤ Mξ) (hν : ν Cz < ⊤)
    (P : α → β → γ → δ → ℂ) (hPm : Measurable fun p : (α × β × γ) × δ => P p.1.1 p.1.2.1 p.1.2.2 p.2)
    (Ct : Set α) (Cr : Set δ) (hCt : MeasurableSet Ct) (hCr : MeasurableSet Cr) (hτ : τ Ct < ⊤) (hμ : μ Cr < ⊤)
    (M : ℝ) (hM : 0 ≤ M) (hPb : ∀ t k z r, ‖P t k z r‖ ≤ M)
    (hPz : ∀ t k z r, z ∉ Cz → P t k z r = 0) (hPr : ∀ t k z r, r ∉ Cr → P t k z r = 0)
    (N : Set α) (hNm : MeasurableSet N) (hN0 : τ N = 0)
    (hPt : ∀ t, t ∉ N → t ∉ Ct → ∀ k z r, P t k z r = 0) :
    ∫ t, ∫ k, ∫ z, ξ z * ∫ u, P t k z u ∂μ ∂ν ∂κ ∂τ =
      ∫ u, (∫ t, ∫ k, (∫ z, ξ z * P t k z u ∂ν) ∂κ ∂τ) ∂μ := by
  set Q : (α × β × γ) × δ → ℂ := fun p => ξ p.1.2.2 * P p.1.1 p.1.2.1 p.1.2.2 p.2 with hQ
  have hQm : Measurable Q := (hξm.comp measurable_fst.snd.snd).mul hPm
  set Box : Set ((α × β × γ) × δ) := ((Ct ∪ N) ×ˢ ((Set.univ : Set β) ×ˢ Cz)) ×ˢ Cr with hBox
  have hBoxm : MeasurableSet Box :=
    ((hCt.union hNm).prod (MeasurableSet.univ.prod hCz)).prod hCr
  have hBoxfin : ((τ.prod (κ.prod ν)).prod μ) Box < ⊤ := by
    rw [hBox, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
    have h1 : τ (Ct ∪ N) < ⊤ := by
      refine lt_of_le_of_lt (measure_union_le _ _) ?_
      rw [hN0, add_zero]; exact hτ
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top h1 (ENNReal.mul_lt_top (measure_lt_top κ _) hν)) hμ
  have hQ0 : ∀ p, p ∉ Box → Q p = 0 := by
    rintro ⟨⟨t, k, z⟩, u⟩ hp
    simp only [hBox, Set.mem_prod, Set.mem_univ, true_and, Set.mem_union, not_and_or, not_or] at hp
    simp only [hQ]
    rcases hp with (⟨htC, htN⟩ | hz) | hu
    · rw [hPt t htN htC, mul_zero]
    · rw [hPz t k z u hz, mul_zero]
    · rw [hPr t k z u hu, mul_zero]
  have hQb : ∀ p, ‖Q p‖ ≤ Mξ * M := by
    rintro ⟨⟨t, k, z⟩, u⟩
    simp only [hQ]
    by_cases hz : z ∈ Cz
    · rw [norm_mul]; exact mul_le_mul (hξb z hz) (hPb t k z u) (norm_nonneg _) hMξ
    · rw [hPz t k z u hz, mul_zero, norm_zero]; positivity
  have hQint : Integrable Q ((τ.prod (κ.prod ν)).prod μ) :=
    integrable_of_bound_of_ae_support _ Q hQm.aestronglyMeasurable Box hBoxm hBoxfin (Mξ * M) hQb
      (ae_of_all _ hQ0)
  have hL1 : Integrable (fun p : α × β × γ => ∫ u, Q (p, u) ∂μ) (τ.prod (κ.prod ν)) := hQint.integral_prod_left
  have hleft : ∫ t, ∫ k, ∫ z, ξ z * ∫ u, P t k z u ∂μ ∂ν ∂κ ∂τ = ∫ p, ∫ u, Q (p, u) ∂μ ∂(τ.prod (κ.prod ν)) := by
    rw [integral_prod _ hL1]
    refine integral_congr_ae ?_
    filter_upwards [hL1.prod_right_ae] with t ht
    rw [integral_prod _ ht]
    refine integral_congr_ae (ae_of_all _ fun k => integral_congr_ae (ae_of_all _ fun z => ?_))
    simp only [hQ]
    exact (integral_const_mul _ _).symm
  have hR1 : Integrable (fun p : δ × (α × β × γ) => Q (p.2, p.1)) (μ.prod (τ.prod (κ.prod ν))) :=
    hQint.swap
  have hright : ∫ u, (∫ t, ∫ k, (∫ z, ξ z * P t k z u ∂ν) ∂κ ∂τ) ∂μ =
      ∫ u, ∫ p, Q (p, u) ∂(τ.prod (κ.prod ν)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hR1.prod_right_ae] with u hu
    rw [integral_prod _ hu]
    refine integral_congr_ae ?_
    filter_upwards [hu.prod_right_ae] with t ht
    rw [integral_prod _ ht]
  rw [hleft, hright]
  exact integral_integral_swap hQint

theorem lintegral3_ne_top (τ : Measure α) (κ : Measure β) (ν : Measure γ) [IsFiniteMeasure κ]
    (Cz : Set γ) (hCz : MeasurableSet Cz) (hν : ν Cz < ⊤) (Ct : Set α) (hCt : MeasurableSet Ct) (hτ : τ Ct < ⊤)
    (H : α → β → γ → ℂ) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hHb : ∀ t k z, ‖H t k z‖ₑ ≤ Cz.indicator (fun _ => B) z)
    (hHt : ∀ᵐ t ∂τ, t ∉ Ct → ∀ k z, H t k z = 0) :
    ∫⁻ t, ∫⁻ k, ∫⁻ z, ‖H t k z‖ₑ ∂ν ∂κ ∂τ ≠ ⊤ := by
  have hz : ∀ t k, ∫⁻ z, ‖H t k z‖ₑ ∂ν ≤ B * ν Cz := fun t k => by
    calc ∫⁻ z, ‖H t k z‖ₑ ∂ν ≤ ∫⁻ z, Cz.indicator (fun _ => B) z ∂ν := lintegral_mono fun z => hHb t k z
      _ = B * ν Cz := by rw [lintegral_indicator_const hCz]
  have hk : ∀ t, ∫⁻ k, ∫⁻ z, ‖H t k z‖ₑ ∂ν ∂κ ≤ B * ν Cz * κ Set.univ := fun t => by
    calc ∫⁻ k, ∫⁻ z, ‖H t k z‖ₑ ∂ν ∂κ ≤ ∫⁻ k, B * ν Cz ∂κ := lintegral_mono fun k => hz t k
      _ = B * ν Cz * κ Set.univ := by rw [lintegral_const]
  have ht : ∫⁻ t, ∫⁻ k, ∫⁻ z, ‖H t k z‖ₑ ∂ν ∂κ ∂τ ≤ ∫⁻ t, Ct.indicator (fun _ => B * ν Cz * κ Set.univ) t ∂τ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hHt] with t htt
    by_cases h : t ∈ Ct
    · rw [Set.indicator_of_mem h]; exact hk t
    · rw [Set.indicator_of_notMem h]
      have : ∀ k z, ‖H t k z‖ₑ = 0 := fun k z => by rw [htt h k z, enorm_zero]
      simp [this]
  refine ne_top_of_le_ne_top ?_ ht
  rw [lintegral_indicator_const hCt]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hB hν.ne) (measure_ne_top κ _)) hτ.ne

theorem main
    (τ : Measure α) (κ : Measure β) (ν : Measure γ) (μ : Measure δ)
    [SFinite τ] [IsFiniteMeasure κ] [SFinite ν] [SFinite μ]
    (ξ : γ → ℂ) (hξm : Measurable ξ) (Mξ : ℝ) (Cz : Set γ) (hξb : ∀ z ∈ Cz, ‖ξ z‖ ≤ Mξ) (hMξ : 0 ≤ Mξ)
    (P : α → β → γ → δ → ℂ)
    (hPm : Measurable fun p : (α × β × γ) × δ => P p.1.1 p.1.2.1 p.1.2.2 p.2)
    (Ct : Set α) (Cr : Set δ) (hCt : MeasurableSet Ct) (hCz : MeasurableSet Cz) (hCr : MeasurableSet Cr)
    (hτ : τ Ct < ⊤) (hν : ν Cz < ⊤) (hμ : μ Cr < ⊤)
    (M : ℝ) (hM : 0 ≤ M) (hPb : ∀ t k z r, ‖P t k z r‖ ≤ M)
    (hPz : ∀ t k z r, z ∉ Cz → P t k z r = 0)
    (hPr : ∀ t k z r, r ∉ Cr → P t k z r = 0)
    (hPt : ∀ᵐ t ∂τ, t ∉ Ct → ∀ k z r, P t k z r = 0)
    {ι : Type*} (q : ι → δ) (hq : {i | q i ∈ Cr}.Finite)
    (c : ℂ) (b : Prop) [Decidable b] :
    (∫⁻ t, ∫⁻ k, ∫⁻ z, ‖ξ z * ((∑ᶠ i, P t k z (q i)) - (if b then c * ∫ u, P t k z u ∂μ else 0))‖ₑ ∂ν ∂κ ∂τ ≠ ⊤) ∧
    ∫ t, ∫ k, (∫ z, ξ z * ((∑ᶠ i, P t k z (q i)) - (if b then c * ∫ u, P t k z u ∂μ else 0)) ∂ν) ∂κ ∂τ =
      (∑ᶠ i, ∫ t, ∫ k, (∫ z, ξ z * P t k z (q i) ∂ν) ∂κ ∂τ) -
        (if b then c * ∫ u, (∫ t, ∫ k, (∫ z, ξ z * P t k z u ∂ν) ∂κ ∂τ) ∂μ else 0) := by
  classical

  set F : Finset ι := hq.toFinset with hF
  have hF_mem : ∀ i, i ∈ F ↔ q i ∈ Cr := fun i => by simp [hF]
  have hfinsum : ∀ t k z, (∑ᶠ i, P t k z (q i)) = ∑ i ∈ F, P t k z (q i) := by
    intro t k z
    apply finsum_eq_sum_of_support_subset
    intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.mem_coe, hF_mem]
    by_contra h
    exact hi (hPr t k z (q i) h)

  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (s := {t | ¬ (t ∉ Ct → ∀ k z r, P t k z r = 0)}) (ae_iff.1 hPt)
  have hgoodt : ∀ t, t ∉ N → t ∉ Ct → ∀ k z r, P t k z r = 0 := by
    intro t ht; by_contra h; exact ht (hNsub h)

  have hPm3 : ∀ r, Measurable fun p : α × β × γ => P p.1 p.2.1 p.2.2 r := fun r =>
    hPm.comp (measurable_id.prodMk measurable_const)
  have hPu_m : Measurable fun p : α × β × γ => ∫ u, P p.1 p.2.1 p.2.2 u ∂μ :=
    (hPm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hPu_b : ∀ t k z, ‖∫ u, P t k z u ∂μ‖ ≤ M * μ.real Cr := by
    intro t k z
    have h0 : ∫ u, P t k z u ∂μ = ∫ u in Cr, P t k z u ∂μ := by
      rw [← integral_indicator hCr]
      congr 1; funext u
      by_cases hu : u ∈ Cr
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, hPr t k z u hu]
    rw [h0]
    exact norm_setIntegral_le_of_norm_le_const hμ (fun u _ => hPb t k z u)
  have hPu_z : ∀ t k z, z ∉ Cz → ∫ u, P t k z u ∂μ = 0 := by
    intro t k z hz; simp [hPz t k z _ hz]
  have hMu : 0 ≤ M * μ.real Cr := mul_nonneg hM ENNReal.toReal_nonneg

  have hq_int : ∀ i : ι,
      (∀ t k, Integrable (fun z => ξ z * P t k z (q i)) ν) ∧
      (∀ t, Integrable (fun k => ∫ z, ξ z * P t k z (q i) ∂ν) κ) ∧
      Integrable (fun t => ∫ k, ∫ z, ξ z * P t k z (q i) ∂ν ∂κ) τ ∧
      (∀ t k, ‖∫ z, ξ z * P t k z (q i) ∂ν‖ ≤ Mξ * M * ν.real Cz) := fun i =>
    levels τ κ ν ξ hξm Mξ hMξ Cz hCz hξb hν Ct hCt hτ (fun t k z => P t k z (q i)) M hM (hPm3 (q i))
      (fun t k z => hPb t k z _) (fun t k z hz => hPz t k z _ hz)
      (by filter_upwards [hPt] with t ht hnt k z; exact ht hnt k z _)
  obtain ⟨hu1, hu2, hu3, -⟩ :=
    levels τ κ ν ξ hξm Mξ hMξ Cz hCz hξb hν Ct hCt hτ (fun t k z => ∫ u, P t k z u ∂μ) (M * μ.real Cr) hMu
      hPu_m hPu_b hPu_z (by filter_upwards [hPt] with t ht hnt k z; simp [ht hnt k z])

  set W : α → β → γ → ℂ := fun t k z => if b then c * ∫ u, P t k z u ∂μ else 0 with hW
  have hW1 : ∀ t k, Integrable (fun z => ξ z * W t k z) ν := by
    intro t k; by_cases hb : b
    · simp only [hW, if_pos hb]
      have := (hu1 t k).const_mul c
      refine this.congr (ae_of_all _ fun z => ?_)
      show c * (ξ z * ∫ u, P t k z u ∂μ) = ξ z * (c * ∫ u, P t k z u ∂μ)
      ring
    · simp only [hW, if_neg hb, mul_zero]; exact integrable_zero _ _ _
  have hWz : ∀ t k, ∫ z, ξ z * W t k z ∂ν = (if b then c * ∫ z, ξ z * ∫ u, P t k z u ∂μ ∂ν else 0) := by
    intro t k; by_cases hb : b
    · simp only [hW, if_pos hb]
      rw [← integral_const_mul]; congr 1; funext z; ring
    · simp only [hW, if_neg hb, mul_zero, integral_zero]
  have hW2 : ∀ t, Integrable (fun k => ∫ z, ξ z * W t k z ∂ν) κ := by
    intro t; simp only [hWz]; by_cases hb : b
    · simp only [if_pos hb]; exact (hu2 t).const_mul c
    · simp only [if_neg hb]; exact integrable_zero _ _ _
  have hWk : ∀ t, ∫ k, ∫ z, ξ z * W t k z ∂ν ∂κ = (if b then c * ∫ k, ∫ z, ξ z * ∫ u, P t k z u ∂μ ∂ν ∂κ else 0) := by
    intro t; simp only [hWz]; by_cases hb : b
    · simp only [if_pos hb]; rw [integral_const_mul]
    · simp only [if_neg hb, integral_zero]
  have hW3 : Integrable (fun t => ∫ k, ∫ z, ξ z * W t k z ∂ν ∂κ) τ := by
    simp only [hWk]; by_cases hb : b
    · simp only [if_pos hb]; exact hu3.const_mul c
    · simp only [if_neg hb]; exact integrable_zero _ _ _
  have hWt : ∫ t, ∫ k, ∫ z, ξ z * W t k z ∂ν ∂κ ∂τ =
      (if b then c * ∫ t, ∫ k, ∫ z, ξ z * ∫ u, P t k z u ∂μ ∂ν ∂κ ∂τ else 0) := by
    simp only [hWk]; by_cases hb : b
    · simp only [if_pos hb]; rw [integral_const_mul]
    · simp only [if_neg hb, integral_zero]

  have hpt : ∀ t k z, ξ z * ((∑ᶠ i, P t k z (q i)) - (if b then c * ∫ u, P t k z u ∂μ else 0)) =
      (∑ i ∈ F, ξ z * P t k z (q i)) - ξ z * W t k z := by
    intro t k z; rw [hfinsum, mul_sub, Finset.mul_sum]

  have hLz : ∀ t k, ∫ z, ξ z * ((∑ᶠ i, P t k z (q i)) - (if b then c * ∫ u, P t k z u ∂μ else 0)) ∂ν =
      (∑ i ∈ F, ∫ z, ξ z * P t k z (q i) ∂ν) - ∫ z, ξ z * W t k z ∂ν := by
    intro t k
    simp only [hpt]
    rw [integral_sub (integrable_finset_sum _ fun i _ => (hq_int i).1 t k) (hW1 t k),
      integral_finset_sum _ fun i _ => (hq_int i).1 t k]

  have hLk : ∀ t, ∫ k, ∫ z, ξ z * ((∑ᶠ i, P t k z (q i)) - (if b then c * ∫ u, P t k z u ∂μ else 0)) ∂ν ∂κ =
      (∑ i ∈ F, ∫ k, ∫ z, ξ z * P t k z (q i) ∂ν ∂κ) - ∫ k, ∫ z, ξ z * W t k z ∂ν ∂κ := by
    intro t
    simp only [hLz]
    rw [integral_sub (integrable_finset_sum _ fun i _ => (hq_int i).2.1 t) (hW2 t),
      integral_finset_sum _ fun i _ => (hq_int i).2.1 t]

  have hLt : ∫ t, ∫ k, ∫ z, ξ z * ((∑ᶠ i, P t k z (q i)) - (if b then c * ∫ u, P t k z u ∂μ else 0)) ∂ν ∂κ ∂τ =
      (∑ i ∈ F, ∫ t, ∫ k, ∫ z, ξ z * P t k z (q i) ∂ν ∂κ ∂τ) - ∫ t, ∫ k, ∫ z, ξ z * W t k z ∂ν ∂κ ∂τ := by
    simp only [hLk]
    rw [integral_sub (integrable_finset_sum _ fun i _ => (hq_int i).2.2.1) hW3,
      integral_finset_sum _ fun i _ => (hq_int i).2.2.1]

  have hRfin : (∑ᶠ i, ∫ t, ∫ k, (∫ z, ξ z * P t k z (q i) ∂ν) ∂κ ∂τ) =
      ∑ i ∈ F, ∫ t, ∫ k, ∫ z, ξ z * P t k z (q i) ∂ν ∂κ ∂τ := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.mem_coe, hF_mem]
    by_contra h
    apply hi
    simp [hPr _ _ _ (q i) h]

  have hFub := fubini4 τ κ ν μ ξ hξm Mξ hMξ Cz hCz hξb hν P hPm Ct Cr hCt hCr hτ hμ M hM hPb hPz hPr N hNm hN0 hgoodt

  have hFIN := lintegral3_ne_top τ κ ν Cz hCz hν Ct hCt hτ
    (fun t k z => ξ z * ((∑ᶠ i, P t k z (q i)) - (if b then c * ∫ u, P t k z u ∂μ else 0)))
    (ENNReal.ofReal (Mξ * ((F.card : ℝ) * M + ‖c‖ * (M * μ.real Cr)))) ENNReal.ofReal_ne_top
    (by
      intro t k z
      beta_reduce
      by_cases hz : z ∈ Cz
      · rw [Set.indicator_of_mem hz, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul]
        refine mul_le_mul (hξb z hz) ?_ (norm_nonneg _) hMξ
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [hfinsum]
          refine (norm_sum_le _ _).trans ?_
          have : ∑ i ∈ F, ‖P t k z (q i)‖ ≤ ∑ i ∈ F, M := Finset.sum_le_sum fun i _ => hPb _ _ _ _
          simpa using this
        · by_cases hb : b
          · rw [if_pos hb, norm_mul]; exact mul_le_mul_of_nonneg_left (hPu_b t k z) (norm_nonneg _)
          · rw [if_neg hb, norm_zero]; positivity
      · rw [Set.indicator_of_notMem hz]
        have h1 : (∑ᶠ i, P t k z (q i)) = 0 := by
          rw [hfinsum]; exact Finset.sum_eq_zero fun i _ => hPz t k z _ hz
        rw [h1, hPu_z t k z hz, mul_zero, ite_self, sub_self, mul_zero, enorm_zero])
    (by
      filter_upwards [hPt] with t ht hnt k z
      have h1 : (∑ᶠ i, P t k z (q i)) = 0 := by
        rw [hfinsum]; exact Finset.sum_eq_zero fun i _ => ht hnt k z _
      simp [h1, ht hnt k z])
  exact ⟨hFIN, by rw [hLt, hRfin, hWt, hFub]⟩

end SwapCore

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

section Inst

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in
set_option maxHeartbeats 4000000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSτ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ ↔ (v ∈ S ∧ v ∉ T) ∨
        ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v ∧
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1)
    (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hgood : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin j v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hgood' : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
        τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1)
    (hbad : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN))
    (harch : ∀ j (v : InfinitePlace K),
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN)
    (hfac3 : ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂(τ j) =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v)) :
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        ∀ (j : Fin n) (y : (AdeleRing (𝓞 K) K)ˣ) (θ : ℝ),
          (∫⁻ t, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if θ < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0))‖ₑ ∂νZL ∂(maximalCompactHaar L) ∂(τ j)) ≠ ⊤ ∧
            (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if θ < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) =
            ((∑ᶠ η : Kˣ, (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ∂νZL)
              ∂(maximalCompactHaar L) ∂(τ j))) -
              (if θ < NumberField.TateGlobal.ideleNorm K y then
                ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂νZL)
              ∂(maximalCompactHaar L) ∂(τ j)) ∂μK else 0)) := by
  classical
  intro ks js φ φf hfac j y θ
  have hIL : ‹MeasurableSpace (AdeleRing (𝓞 L) L)ˣ› = NumberField.Idele.ideleBorel L := BorelSpace.measurable_eq
  subst hIL
  have hIK : ‹MeasurableSpace (AdeleRing (𝓞 K) K)› = NumberField.AdelicHaar.adeleBorel (𝓞 K) K :=
    BorelSpace.measurable_eq
  subst hIK

  obtain ⟨Ct, Cz, Cr, Cw, M, hCt, hCz, hCr, hCw, hM, hBd, hZ, hTt, hRW, hcont⟩ :=
    AutomorphicForm.TwistedBruhat.exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
      K L νZL D σ hgen SL ξL hSL hξc hξt S φa φS μK hξσ T hT ws ns rTs zs Sτ hSτ n c τ τfin τarch πs
      hcpos hlev hτfin hτ0 hgood hgood' hbad harch hfac3 ks js φ φf hfac j

  haveI := NumberField.AdeleRing.secondCountableTopology L
  haveI := NumberField.AdeleRing.secondCountableTopology K
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
    haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
      (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 L) L)).symm.secondCountableTopology
    exact Units.isInducing_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (AdeleRing (𝓞 K) K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite (τ j) := by haveI := hτfin j; infer_instance

  set 𝓌 : Measure (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :=
    Measure.pi fun _ => adelicAddHaar (𝓞 K) K with h𝓌
  set ξ : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun ζ => ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) with hξ
  have hξm : Measurable ξ := hξc.measurable
  obtain ⟨Bξ, hBξ⟩ := hCz.exists_bound_of_continuousOn (f := ξ) hξc.continuousOn
  set Mξ : ℝ := max Bξ 0 with hMξ
  have hMξ0 : 0 ≤ Mξ := le_max_right _ _
  have hξb : ∀ z ∈ Cz, ‖ξ z‖ ≤ Mξ := fun z hz => (hBξ z hz).trans (le_max_left _ _)

  set Φ5 := (fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
                ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
                  (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) =>
              (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                  (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) =>
                φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) with hΦ5
  have hΦ5c : Continuous Φ5 := hcont
  set e : ((((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 K) K) ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K)) →
      ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
        ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
          (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) :=
    fun q => ((q.1.1.1, q.1.1.2.1), (q.1.1.2.2, (q.1.2, q.2))) with he
  have hem : Measurable e :=
    (measurable_fst.fst.fst.prodMk measurable_fst.fst.snd.fst).prodMk
      (measurable_fst.fst.snd.snd.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hHm : Measurable (Φ5 ∘ e) := hΦ5c.measurable.comp hem

  set P0 : (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → AdeleRing (𝓞 K) K → ℂ :=
    fun t k ζ r => ∫ w', (Φ5 ∘ e) (((t, k, ζ), r), w') ∂𝓌 with hP0
  have hP0_tp : ∀ t k ζ r, P0 t k ζ r = tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r := by
    intro t k ζ r; rfl
  set P' : (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → AdeleRing (𝓞 K) K → ℂ :=
    fun t k ζ r => if t ∈ Ct then P0 t k ζ r else 0 with hP'

  have hΦ_bd : ∀ t k ζ r w', ‖(Φ5 ∘ e) (((t, k, ζ), r), w')‖ ≤ M := fun t k ζ r w' => hBd t k ζ r w'
  have hΦ_z : ∀ t k ζ r w', ζ ∉ Cz → (Φ5 ∘ e) (((t, k, ζ), r), w') = 0 := fun t k ζ r w' hz => hZ t k ζ r w' hz
  have hΦ_rw : ∀ t ∈ Ct, ∀ k ζ r w', (r ∉ Cr ∨ w' ∉ Cw) → (Φ5 ∘ e) (((t, k, ζ), r), w') = 0 :=
    fun t ht k ζ r w' h => hRW t ht k ζ r w' h
  have hΦ_t : ∀ᵐ t ∂(τ j), t ∉ Ct → ∀ k ζ r w', (Φ5 ∘ e) (((t, k, ζ), r), w') = 0 := by
    filter_upwards [hTt] with t ht hnt k ζ r w'
    exact ht hnt k ζ r w'

  have hCtm : MeasurableSet Ct := hCt.isClosed.measurableSet
  have hCzm : MeasurableSet Cz := hCz.isClosed.measurableSet
  have hCrm : MeasurableSet Cr := hCr.isClosed.measurableSet
  have hCwm : MeasurableSet Cw := hCw.isClosed.measurableSet
  have hP0m : Measurable fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ) ×
      AdeleRing (𝓞 K) K => P0 p.1.1 p.1.2.1 p.1.2.2 p.2 :=
    (hHm.stronglyMeasurable.integral_prod_right' (ν := 𝓌)).measurable
  have hP'm : Measurable fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ) ×
      AdeleRing (𝓞 K) K => P' p.1.1 p.1.2.1 p.1.2.2 p.2 :=
    Measurable.ite (measurable_fst.fst hCtm) hP0m measurable_const

  have h𝓌Cw : 𝓌 Cw < ⊤ := hCw.measure_lt_top
  have hP'b : ∀ t k ζ r, ‖P' t k ζ r‖ ≤ M * 𝓌.real Cw := by
    intro t k ζ r
    by_cases ht : t ∈ Ct
    · simp only [hP', if_pos ht, hP0]
      have h0 : ∫ w', (Φ5 ∘ e) (((t, k, ζ), r), w') ∂𝓌 = ∫ w' in Cw, (Φ5 ∘ e) (((t, k, ζ), r), w') ∂𝓌 := by
        rw [← integral_indicator hCwm]
        congr 1; funext w'
        by_cases hw : w' ∈ Cw
        · rw [Set.indicator_of_mem hw]
        · rw [Set.indicator_of_notMem hw, hΦ_rw t ht k ζ r w' (Or.inr hw)]
      rw [h0]
      exact norm_setIntegral_le_of_norm_le_const h𝓌Cw (fun w' _ => hΦ_bd t k ζ r w')
    · simp only [hP', if_neg ht, norm_zero]; positivity
  have hP'z : ∀ t k ζ r, ζ ∉ Cz → P' t k ζ r = 0 := by
    intro t k ζ r hz
    by_cases ht : t ∈ Ct
    · simp only [hP', if_pos ht, hP0, hΦ_z t k ζ r _ hz, integral_zero]
    · simp only [hP', if_neg ht]
  have hP'r : ∀ t k ζ r, r ∉ Cr → P' t k ζ r = 0 := by
    intro t k ζ r hr
    by_cases ht : t ∈ Ct
    · simp only [hP', if_pos ht, hP0, hΦ_rw t ht k ζ r _ (Or.inl hr), integral_zero]
    · simp only [hP', if_neg ht]
  have hP't : ∀ᵐ t ∂(τ j), t ∉ Ct → ∀ k ζ r, P' t k ζ r = 0 :=
    ae_of_all _ fun t ht k ζ r => by simp only [hP', if_neg ht]

  have hq : {η : Kˣ | algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) ∈ Cr}.Finite := by
    have hC' : IsCompact ((fun x : AdeleRing (𝓞 K) K => x * ((y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) '' Cr) :=
      hCr.image (continuous_mul_right _)
    have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hC'
    refine (hfin.preimage (Units.val_injective.injOn)).subset ?_
    intro η hη
    refine ⟨algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), hη, ?_⟩
    beta_reduce
    rw [mul_assoc, Units.inv_mul, mul_one]

  have hτCt : τ j Ct < ⊤ := by haveI := hτfin j; exact hCt.measure_lt_top
  have hνCz : νZL Cz < ⊤ := hCz.measure_lt_top
  have hμCr : μK Cr < ⊤ := hCr.measure_lt_top

  obtain ⟨hFIN', hEQ'⟩ := SwapCore.main (τ j) (maximalCompactHaar L) νZL μK ξ hξm Mξ Cz hξb hMξ0 P' hP'm Ct Cr
    hCtm hCzm hCrm hτCt hνCz hμCr (M * 𝓌.real Cw) (mul_nonneg hM ENNReal.toReal_nonneg) hP'b hP'z hP'r hP't
    (fun η : Kˣ => algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) hq
    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) (θ < NumberField.TateGlobal.ideleNorm K y)

  have hae : ∀ᵐ t ∂(τ j), ∀ k ζ r, P' t k ζ r = P0 t k ζ r := by
    filter_upwards [hΦ_t] with t ht k ζ r
    by_cases htc : t ∈ Ct
    · simp only [hP', if_pos htc]
    · simp only [hP', if_neg htc, hP0, ht htc, integral_zero]

  refine ⟨?_, ?_⟩
  · refine ne_of_eq_of_ne ?_ hFIN'
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with t ht
    simp only [ht, hP0_tp, hξ]
  · have hL : (∫ t, ∫ k, (∫ ζ, ξ ζ * ((∑ᶠ η : Kˣ, P0 t k ζ (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
          (if θ < NumberField.TateGlobal.ideleNorm K y then ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, P0 t k ζ u ∂μK else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) =
        ∫ t, ∫ k, (∫ ζ, ξ ζ * ((∑ᶠ η : Kˣ, P' t k ζ (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
          (if θ < NumberField.TateGlobal.ideleNorm K y then ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, P' t k ζ u ∂μK else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with t ht
      simp only [ht]
    have hR1 : ∀ η : Kˣ, (∫ t, ∫ k, (∫ ζ, ξ ζ * P0 t k ζ (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) =
        ∫ t, ∫ k, (∫ ζ, ξ ζ * P' t k ζ (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j) := by
      intro η
      refine integral_congr_ae ?_
      filter_upwards [hae] with t ht
      simp only [ht]
    have hR2 : ∀ u : AdeleRing (𝓞 K) K, (∫ t, ∫ k, (∫ ζ, ξ ζ * P0 t k ζ u ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) =
        ∫ t, ∫ k, (∫ ζ, ξ ζ * P' t k ζ u ∂νZL) ∂(maximalCompactHaar L) ∂(τ j) := by
      intro u
      refine integral_congr_ae ?_
      filter_upwards [hae] with t ht
      simp only [ht]
    have hEQ0 : (∫ t, ∫ k, (∫ ζ, ξ ζ * ((∑ᶠ η : Kˣ, P0 t k ζ (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
          (if θ < NumberField.TateGlobal.ideleNorm K y then ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, P0 t k ζ u ∂μK else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) =
        (∑ᶠ η : Kˣ, ∫ t, ∫ k, (∫ ζ, ξ ζ * P0 t k ζ (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) -
          (if θ < NumberField.TateGlobal.ideleNorm K y then ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) *
            ∫ u, (∫ t, ∫ k, (∫ ζ, ξ ζ * P0 t k ζ u ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) ∂μK else 0) := by
      rw [hL, hEQ']
      simp only [hR1, hR2]
    simpa only [hP0_tp, hξ] using hEQ0

end Inst

end
end S_AutomorphicForm_TwistedBruhat_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram (solution)
