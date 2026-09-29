-- Prove2me | solution 1 for AutomorphicForm.exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e70edf8c-1936-5e4d-b57d-4a593d007d39

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace FundamentalDomainSlab

open scoped Pointwise ENNReal

section FDAction

variable {H α : Type*} [Group H] [MulAction H α] [MeasurableSpace α] [MeasurableConstSMul H α]
  [Countable H] {ν : Measure α} [SMulInvariantMeasure H α ν]

private theorem setLIntegral_fd_le_of_cover {S E : Set α} (hS : IsFundamentalDomain H S ν)
    (hcov : S ⊆ ⋃ γ : H, (γ • ·) ⁻¹' E) (F : α → ℝ≥0∞) (hF : ∀ (γ : H) (w : α), F (γ • w) = F w) :
    ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in E, F w ∂ν := by
  calc ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in ⋃ γ : H, S ∩ (γ • ·) ⁻¹' E, F w ∂ν := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp (hcov hw)
        exact Set.mem_iUnion.mpr ⟨γ, hw, hγ⟩
    _ ≤ ∑' γ : H, ∫⁻ w in S ∩ (γ • ·) ⁻¹' E, F w ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : H, ∫⁻ w in γ • S ∩ E, F w ∂ν := by
        refine tsum_congr fun γ => ?_
        have hpre : (fun w : α => γ • w) ⁻¹' (γ • S ∩ E) = S ∩ (γ • ·) ⁻¹' E := by
          rw [Set.preimage_inter, Set.preimage_smul, inv_smul_smul]
        rw [← (measurePreserving_smul γ ν).setLIntegral_comp_preimage_emb
          (measurableEmbedding_const_smul γ) F (γ • S ∩ E), hpre]
        simp_rw [hF]
    _ = ∫⁻ w in E, F w ∂ν := by
        rw [hS.setLIntegral_eq_tsum F E]
        exact tsum_congr fun γ => by rw [Set.inter_comm]

private theorem exists_measure_smul_inter_ne_zero {S U : Set α} (hS : IsFundamentalDomain H S ν)
    (hU : ν U ≠ 0) : ∃ γ : H, ν (γ • U ∩ S) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hU ((hS.measure_eq_tsum U).trans (ENNReal.tsum_eq_zero.mpr h))

end FDAction

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

private theorem smulInvariantMeasure_restrict (Γ : Subgroup G) [MeasurableConstSMul ↥Γ G]
    (μ : Measure G) [SMulInvariantMeasure ↥Γ G μ] {T : Set G} (hT : MeasurableSet T)
    (hΓT : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' T = T) :
    SMulInvariantMeasure ↥Γ G (μ.restrict T) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓT γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hT)

variable [MeasurableMul G]

private theorem isFundamentalDomain_image_mul_right (Γ : Subgroup G) (μ : Measure G)
    [μ.IsMulRightInvariant] {S T T' : Set G} (hS : IsFundamentalDomain ↥Γ S (μ.restrict T))
    (g : G) (hTT' : (fun w : G => w * g⁻¹) ⁻¹' T = T') :
    IsFundamentalDomain ↥Γ ((fun w : G => w * g) '' S) (μ.restrict T') := by
  have hmp : MeasurePreserving (fun w : G => w * g⁻¹) (μ.restrict T') (μ.restrict T) := by
    rw [← hTT']
    exact (measurePreserving_mul_right μ g⁻¹).restrict_preimage_emb (measurableEmbedding_mulRight g⁻¹) T
  have h := hS.image_of_equiv (ν := μ.restrict T') (Equiv.mulRight g)
    (by simpa using hmp.quasiMeasurePreserving) (Equiv.refl _)
    (fun γ w => show (γ : G) * w * g = (γ : G) * (w * g) from mul_assoc _ _ _)
  simpa using h

private theorem isFundamentalDomain_image_mul_left (Γ : Subgroup G) (μ : Measure G)
    [μ.IsMulLeftInvariant] {S T T' : Set G} (hS : IsFundamentalDomain ↥Γ S (μ.restrict T))
    (z : G) (hz : ∀ γ : ↥Γ, z * (γ : G) = (γ : G) * z)
    (hTT' : (fun w : G => z⁻¹ * w) ⁻¹' T = T') :
    IsFundamentalDomain ↥Γ ((fun w : G => z * w) '' S) (μ.restrict T') := by
  have hmp : MeasurePreserving (fun w : G => z⁻¹ * w) (μ.restrict T') (μ.restrict T) := by
    rw [← hTT']
    exact (measurePreserving_mul_left μ z⁻¹).restrict_preimage_emb (measurableEmbedding_mulLeft z⁻¹) T
  have h := hS.image_of_equiv (ν := μ.restrict T') (Equiv.mulLeft z)
    (by simpa using hmp.quasiMeasurePreserving) (Equiv.refl _)
    (fun γ w => show z * ((γ : G) * w) = (γ : G) * (z * w) by rw [← mul_assoc, hz γ, mul_assoc])
  simpa using h

private theorem setIntegral_mul_right_eq_of_isFundamentalDomain
    (Γ : Subgroup G) [Countable ↥Γ] [MeasurableConstSMul ↥Γ G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [SMulInvariantMeasure ↥Γ G μ]
    {S T T' : Set G} (hS : IsFundamentalDomain ↥Γ S (μ.restrict T)) (hST : S ⊆ T)
    (g z : G) (hz : ∀ γ : ↥Γ, z * (γ : G) = (γ : G) * z)
    (hT' : MeasurableSet T') (hΓT' : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' T' = T')
    (hgT : (fun w : G => w * g⁻¹) ⁻¹' T = T') (hzT : (fun w : G => z⁻¹ * w) ⁻¹' T = T')
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : G → E)
    (hΦΓ : ∀ (γ : ↥Γ) (w : G), Φ (γ • w) = Φ w) (hΦz : ∀ w, Φ (z * w) = Φ w) :
    ∫ w in S, Φ (w * g) ∂μ = ∫ w in S, Φ w ∂μ := by
  haveI : SMulInvariantMeasure ↥Γ G (μ.restrict T') := smulInvariantMeasure_restrict Γ μ hT' hΓT'
  have hFDg := isFundamentalDomain_image_mul_right Γ μ hS g hgT
  have hFDz := isFundamentalDomain_image_mul_left Γ μ hS z hz hzT
  have hSg : (fun w => w * g) '' S ⊆ T' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hgT]
    show w * g * g⁻¹ ∈ T
    rw [mul_inv_cancel_right]
    exact hST hw
  have hSz : (fun w => z * w) '' S ⊆ T' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hzT]
    show z⁻¹ * (z * w) ∈ T
    rw [inv_mul_cancel_left]
    exact hST hw
  calc ∫ w in S, Φ (w * g) ∂μ
      = ∫ w in (fun w => w * g) '' S, Φ w ∂μ :=
        ((measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) Φ S).symm
    _ = ∫ w in (fun w => w * g) '' S, Φ w ∂(μ.restrict T') := by
        rw [Measure.restrict_restrict_of_subset hSg]
    _ = ∫ w in (fun w => z * w) '' S, Φ w ∂(μ.restrict T') := hFDg.setIntegral_eq hFDz fun γ w => hΦΓ γ w
    _ = ∫ w in (fun w => z * w) '' S, Φ w ∂μ := by
        rw [Measure.restrict_restrict_of_subset hSz]
    _ = ∫ w in S, Φ (z * w) ∂μ :=
        (measurePreserving_mul_left μ z).setIntegral_image_emb (measurableEmbedding_mulLeft z) Φ S
    _ = ∫ w in S, Φ w ∂μ := by simp_rw [hΦz]

private theorem aestronglyMeasurable_of_cover_translates (μ : Measure G) [μ.IsMulLeftInvariant]
    {D X : Set G} {f : G → ℂ} (hf : AEStronglyMeasurable f (μ.restrict D))
    {ι : Type*} [Countable ι] (a : ι → G) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (hfa : ∀ (i : ι) (w : G), f (a i * w) = c i * f w) (hX : X ⊆ ⋃ i, (fun w => a i * w) ⁻¹' D) :
    AEStronglyMeasurable f (μ.restrict X) := by
  have hpiece : ∀ i, AEStronglyMeasurable f (μ.restrict ((fun w => a i * w) ⁻¹' D)) := by
    intro i
    have hmp : MeasurePreserving (fun w => a i * w) (μ.restrict ((fun w => a i * w) ⁻¹' D))
        (μ.restrict D) :=
      (measurePreserving_mul_left μ (a i)).restrict_preimage_emb (measurableEmbedding_mulLeft (a i)) D
    have h1 : AEStronglyMeasurable (f ∘ fun w => a i * w) (μ.restrict ((fun w => a i * w) ⁻¹' D)) :=
      hf.comp_measurePreserving hmp
    have h2 : (fun w => (c i)⁻¹ * (f ∘ fun w => a i * w) w) = f := by
      funext w
      simp only [Function.comp_apply, hfa, ← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]
    rw [← h2]
    exact h1.const_mul _
  exact (AEStronglyMeasurable.iUnion hpiece).mono_measure (Measure.restrict_mono hX le_rfl)

private theorem setLIntegral_biUnion_translates_le (μ : Measure G) [μ.IsMulLeftInvariant]
    {D : Set G} (F : G → ℝ≥0∞) {ι : Type*} (I : Finset ι) (b : ι → G) (k : ι → ℝ≥0∞)
    (hk : ∀ i, k i ≠ ∞) (hFb : ∀ (i : ι) (w : G), F (b i * w) = k i * F w) :
    ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ ≤ ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := by
  have hpiece : ∀ i, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ = k i * ∫⁻ w in D, F w ∂μ := by
    intro i
    rw [← (measurePreserving_mul_left μ (b i)).setLIntegral_comp_emb (measurableEmbedding_mulLeft (b i)) F D]
    simp_rw [hFb]
    exact lintegral_const_mul' (k i) _ (hk i)
  calc ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ
      ≤ ∫⁻ w in ⋃ i : ↥I, (fun w => b i * w) '' D, F w ∂μ := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hw⟩
    _ ≤ ∑' i : ↥I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := by
        rw [tsum_fintype, Finset.sum_coe_sort I fun i => ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ]
    _ = ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := Finset.sum_congr rfl fun i _ => hpiece i

private theorem memLp_comp_mul_right (μ : Measure G) [μ.IsMulRightInvariant] {S : Set G}
    {f : G → ℂ} (h : G) (hf : MemLp f 2 (μ.restrict ((fun w => w * h) '' S))) :
    MemLp (fun z => f (z * h)) 2 (μ.restrict S) :=
  hf.comp_measurePreserving
    ((measurePreserving_mul_right μ h).restrict_image_emb (measurableEmbedding_mulRight h) S)

end Group

section Positivity

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [BorelSpace G]

private theorem setIntegral_pos_of_isFundamentalDomain (Γ : Subgroup G) [Countable ↥Γ]
    [MeasurableConstSMul ↥Γ G] (μ : Measure G) [μ.IsOpenPosMeasure] {S T : Set G}
    [SMulInvariantMeasure ↥Γ G (μ.restrict T)]
    (hS : IsFundamentalDomain ↥Γ S (μ.restrict T)) (F : G → ℝ)
    (hF0 : ∀ w, 0 ≤ F w) (hFΓ : ∀ (γ : ↥Γ) (w : G), F (γ • w) = F w)
    (hint : IntegrableOn F S μ) {U : Set G} (hUo : IsOpen U) (hUne : U.Nonempty) (hUT : U ⊆ T)
    (hUF : ∀ w ∈ U, 0 < F w) : 0 < ∫ w in S, F w ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun w => hF0 w) hint]
  have hU : (μ.restrict T) U ≠ 0 := by
    rw [Measure.restrict_apply hUo.measurableSet, Set.inter_eq_self_of_subset_left hUT]
    exact (hUo.measure_pos μ hUne).ne'
  obtain ⟨γ, hγ⟩ := exists_measure_smul_inter_ne_zero hS hU
  have hsub : γ • U ∩ S ⊆ Function.support F ∩ S := by
    rintro w ⟨⟨u, hu, rfl⟩, hw⟩
    exact ⟨show F (γ • u) ≠ 0 by rw [hFΓ γ u]; exact (hUF u hu).ne', hw⟩
  refine pos_iff_ne_zero.mpr fun h0 => hγ (nonpos_iff_eq_zero.mp ?_)
  calc (μ.restrict T) (γ • U ∩ S) ≤ μ (γ • U ∩ S) := Measure.le_iff'.mp Measure.restrict_le_self _
    _ ≤ μ (Function.support F ∩ S) := measure_mono hsub
    _ = 0 := h0

end Positivity

section Pairing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem integrable_mul_conj_mul {x y : α → ℂ} {wt : α → ℝ} (hx : MemLp x 2 μ)
    (hy : MemLp y 2 μ) (hwt : AEStronglyMeasurable wt μ) {C : ℝ} (hC : ∀ᵐ a ∂μ, ‖wt a‖ ≤ C) :
    Integrable (fun a => x a * (starRingEnd ℂ) (y a) * ((wt a : ℝ) : ℂ)) μ := by
  have hxa := hx.aestronglyMeasurable
  have hya := hy.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun a => x a * (starRingEnd ℂ) (y a) * ((wt a : ℝ) : ℂ)) μ :=
    (hxa.mul (Complex.continuous_conj.comp_aestronglyMeasurable hya)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hwt)
  have hx2 : Integrable (fun a => ‖x a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hxa).mp hx
  have hy2 : Integrable (fun a => ‖y a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hya).mp hy
  refine Integrable.mono' ((hx2.add hy2).const_mul (max C 0)) hmeas ?_
  filter_upwards [hC] with a ha
  simp only [Pi.add_apply]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real]
  have h2 : ‖x a‖ * ‖y a‖ ≤ ‖x a‖ ^ 2 + ‖y a‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x a‖ - ‖y a‖), norm_nonneg (x a), norm_nonneg (y a)]
  calc ‖x a‖ * ‖y a‖ * ‖wt a‖ ≤ (‖x a‖ ^ 2 + ‖y a‖ ^ 2) * max C 0 :=
        mul_le_mul h2 (ha.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = max C 0 * (‖x a‖ ^ 2 + ‖y a‖ ^ 2) := mul_comm _ _

private theorem integrable_norm_sq_mul {f : α → ℂ} {wt : α → ℝ} (hf : MemLp f 2 μ)
    (hwt : AEStronglyMeasurable wt μ) {C : ℝ} (hC : ∀ᵐ a ∂μ, ‖wt a‖ ≤ C) :
    Integrable (fun a => ‖f a‖ ^ 2 * wt a) μ := by
  have hf2 : Integrable (fun a => ‖f a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  refine Integrable.mono' (hf2.const_mul (max C 0)) (hf2.aestronglyMeasurable.mul hwt) ?_
  filter_upwards [hC] with a ha
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖f a‖ ^ 2 * ‖wt a‖ ≤ ‖f a‖ ^ 2 * max C 0 :=
        mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (sq_nonneg _)
    _ = max C 0 * ‖f a‖ ^ 2 := mul_comm _ _

private theorem integral_mul_conj_mul_self (f : α → ℂ) (wt : α → ℝ) :
    ∫ a, f a * (starRingEnd ℂ) (f a) * ((wt a : ℝ) : ℂ) ∂μ = ((∫ a, ‖f a‖ ^ 2 * wt a ∂μ : ℝ) : ℂ) := by
  have h : ∀ a, f a * (starRingEnd ℂ) (f a) * ((wt a : ℝ) : ℂ) = ((‖f a‖ ^ 2 * wt a : ℝ) : ℂ) := fun a => by
    rw [Complex.mul_conj, Complex.ofReal_mul, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [h]
  exact integral_ofReal

private theorem memLp_two_of_lintegral {f : α → ℂ} (h1 : AEStronglyMeasurable f μ)
    (h2 : ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞) : MemLp f 2 μ := by
  refine ⟨h1, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mpr ?_⟩
  simpa only [ENNReal.toReal_ofNat] using h2

private theorem lintegral_lt_top_of_memLp_two {f : α → ℂ} (hf : MemLp f 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mp hf.2
  simpa only [ENNReal.toReal_ofNat] using h

end Pairing

section Spans

variable {G : Type*} [Group G]

private abbrev trSpan (f : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun z => f (z * h))

private theorem self_mem_trSpan (f : G → ℂ) : f ∈ trSpan f :=
  Submodule.subset_span ⟨1, funext fun z => congrArg f (mul_one z)⟩

private def rt (g : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun x := fun z => x (z * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem translate_mem_trSpan {f x : G → ℂ} (hx : x ∈ trSpan f) (g : G) :
    (fun z => x (z * g)) ∈ trSpan f := by
  have h : Submodule.map (rt g) (trSpan f) ≤ trSpan f := by
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, funext fun z => congrArg f (mul_assoc z g h).symm⟩
  exact h (Submodule.mem_map_of_mem hx)

private theorem translate_mem_sup {f f' x : G → ℂ} (hx : x ∈ trSpan f ⊔ trSpan f') (g : G) :
    (fun z => x (z * g)) ∈ trSpan f ⊔ trSpan f' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  exact Submodule.mem_sup.mpr ⟨_, translate_mem_trSpan ha g, _, translate_mem_trSpan hb g, rfl⟩

private theorem apply_mul_of_mem_trSpan {f x : G → ℂ} (a : G) (c : ℂ) (hf : ∀ w, f (a * w) = c * f w)
    (hx : x ∈ trSpan f) : ∀ w, x (a * w) = c * x w := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    intro w
    show f (a * w * h) = c * f (w * h)
    rw [mul_assoc, hf]
  | zero => intro w; simp
  | add y z _ _ hy hz => intro w; rw [Pi.add_apply, Pi.add_apply, hy w, hz w, mul_add]
  | smul r y _ hy => intro w; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hy w]; ring

private theorem apply_mul_of_mem_sup {f f' x : G → ℂ} (a : G) (c : ℂ) (hf : ∀ w, f (a * w) = c * f w)
    (hf' : ∀ w, f' (a * w) = c * f' w) (hx : x ∈ trSpan f ⊔ trSpan f') : ∀ w, x (a * w) = c * x w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  intro w
  rw [Pi.add_apply, Pi.add_apply, apply_mul_of_mem_trSpan a c hf hy w, apply_mul_of_mem_trSpan a c hf' hz w,
    mul_add]

private theorem apply_mul_eq_of_mem_trSpan {f x : G → ℂ} (a : G) (hf : ∀ w, f (a * w) = f w)
    (hx : x ∈ trSpan f) : ∀ w, x (a * w) = x w := fun w => by
  rw [apply_mul_of_mem_trSpan a 1 (fun w => by rw [one_mul]; exact hf w) hx w, one_mul]

private theorem apply_mul_eq_of_mem_sup {f f' x : G → ℂ} (a : G) (hf : ∀ w, f (a * w) = f w)
    (hf' : ∀ w, f' (a * w) = f' w) (hx : x ∈ trSpan f ⊔ trSpan f') : ∀ w, x (a * w) = x w := fun w => by
  rw [apply_mul_of_mem_sup a 1 (fun w => by rw [one_mul]; exact hf w) (fun w => by rw [one_mul]; exact hf' w) hx w,
    one_mul]

variable [MeasurableSpace G]

private theorem memLp_of_mem_trSpan {μ : Measure G} {f x : G → ℂ}
    (hgen : ∀ h : G, MemLp (fun z => f (z * h)) 2 μ) (hx : x ∈ trSpan f) : MemLp x 2 μ := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨h, rfl⟩ := hy; exact hgen h
  | zero => exact MemLp.zero'
  | add y z _ _ hy hz => exact hy.add hz
  | smul r y _ hy => exact hy.const_smul r

private theorem memLp_of_mem_sup {μ : Measure G} {f f' x : G → ℂ}
    (hgen : ∀ h : G, MemLp (fun z => f (z * h)) 2 μ) (hgen' : ∀ h : G, MemLp (fun z => f' (z * h)) 2 μ)
    (hx : x ∈ trSpan f ⊔ trSpan f') : MemLp x 2 μ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  exact (memLp_of_mem_trSpan hgen hy).add (memLp_of_mem_trSpan hgen' hz)

end Spans

section Forms

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem exists_sesqForm_eq_on (W V : Submodule ℂ M) (B : M → M → ℂ)
    (hadd₁ : ∀ x₁ ∈ W, ∀ x₂ ∈ W, ∀ y ∈ V, B (x₁ + x₂) y = B x₁ y + B x₂ y)
    (hsmul₁ : ∀ (a : ℂ) (x y : M), B (a • x) y = a * B x y)
    (hadd₂ : ∀ x ∈ W, ∀ y₁ ∈ V, ∀ y₂ ∈ V, B x (y₁ + y₂) = B x y₁ + B x y₂)
    (hsmul₂ : ∀ (a : ℂ) (x y : M), B x (a • y) = (starRingEnd ℂ) a * B x y) :
    ∃ P : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, ∀ x ∈ W, ∀ y ∈ V, P x y = B x y := by
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  obtain ⟨V', hV'⟩ := Submodule.exists_isCompl V
  let pW : M →ₗ[ℂ] ↥W := Submodule.projectionOnto W W' hW'
  let pV : M →ₗ[ℂ] ↥V := Submodule.projectionOnto V V' hV'
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => B (pW x) (pV y)) ?_ ?_ ?_ ?_, ?_⟩
  · intro x₁ x₂ y
    show B (pW (x₁ + x₂)) (pV y) = B (pW x₁) (pV y) + B (pW x₂) (pV y)
    rw [map_add, Submodule.coe_add]
    exact hadd₁ _ (pW x₁).2 _ (pW x₂).2 _ (pV y).2
  · intro a x y
    show B (pW (a • x)) (pV y) = (RingHom.id ℂ) a • B (pW x) (pV y)
    rw [map_smul, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    exact hsmul₁ a _ _
  · intro x y₁ y₂
    show B (pW x) (pV (y₁ + y₂)) = B (pW x) (pV y₁) + B (pW x) (pV y₂)
    rw [map_add, Submodule.coe_add]
    exact hadd₂ _ (pW x).2 _ (pV y₁).2 _ (pV y₂).2
  · intro a x y
    show B (pW x) (pV (a • y)) = (starRingEnd ℂ) a • B (pW x) (pV y)
    rw [map_smul, Submodule.coe_smul, smul_eq_mul]
    exact hsmul₂ a _ _
  · intro x hx y hy
    show B (pW x) (pV y) = B x y
    rw [show (pW x : M) = x from congrArg Subtype.val (Submodule.projectionOnto_apply_left hW' ⟨x, hx⟩),
      show (pV y : M) = y from congrArg Subtype.val (Submodule.projectionOnto_apply_left hV' ⟨y, hy⟩)]

end Forms

end FundamentalDomainSlab

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 globalPoints centralScalar ideleNorm_det_globalPoints exists_finset_central_slab_covering_of_coversModCentre"
p2m_open "AutomorphicForm"
namespace PeterssonSlabPairing

open NumberField.TateGlobal FundamentalDomainSlab
open scoped ENNReal

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private abbrev dn (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)

private abbrev slab (F : Type) [Field F] [NumberField F] (a b : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

private abbrev μH (F : Type) [Field F] [NumberField F] : Measure (AdelicGL2 (𝓞 F) F) :=
  adelicGLHaar (Fin 2) (𝓞 F) F

private abbrev Γp (F : Type) [Field F] [NumberField F] : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (globalPoints (𝓞 F) F).range

private abbrev pairFn (s : ℝ) (x y : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun w => x w * (starRingEnd ℂ) (y w) * ((dn w ^ (-s) : ℝ) : ℂ)

private scoped instance instCountableF : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

private scoped instance instCountableΓ : Countable ↥(Γp F) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable

private theorem dn_pos (g : AdelicGL2 (𝓞 F) F) : 0 < dn g := ideleNorm_pos _

private theorem dn_mul (g h : AdelicGL2 (𝓞 F) F) : dn (g * h) = dn g * dn h := by
  show ideleNorm F _ = _
  rw [map_mul, ideleNorm_mul]

private theorem dn_globalPoints_mul (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    dn (globalPoints (𝓞 F) F γ * g) = dn g := by
  rw [dn_mul]
  show ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ)) * dn g = dn g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

private theorem dn_subtype_mul (γ : ↥(Γp F)) (g : AdelicGL2 (𝓞 F) F) : dn ((γ : AdelicGL2 (𝓞 F) F) * g) = dn g := by
  obtain ⟨_, γ', rfl⟩ := γ
  exact dn_globalPoints_mul γ' g

private theorem dn_one : dn (1 : AdelicGL2 (𝓞 F) F) = 1 := by
  show ideleNorm F (Matrix.GeneralLinearGroup.det 1) = 1
  rw [map_one]
  unfold ideleNorm
  rw [map_one, NNReal.coe_one]

private theorem dn_inv (g : AdelicGL2 (𝓞 F) F) : dn g⁻¹ = (dn g)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← dn_mul, mul_inv_cancel, dn_one])

private theorem dn_centralScalar (n : (AdeleRing (𝓞 F) F)ˣ) :
    dn (centralScalar (𝓞 F) F n) = ideleNorm F n ^ 2 := by
  show ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F n)) = _
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  unfold ideleNorm
  rw [map_pow, NNReal.coe_pow]

private theorem dn_centralScalar_mul (n : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    dn (centralScalar (𝓞 F) F n * g) = ideleNorm F n ^ 2 * dn g := by
  rw [dn_mul, dn_centralScalar]

private theorem continuous_dn : Continuous (fun g : AdelicGL2 (𝓞 F) F => dn g) :=
  NumberField.TateGlobal.continuous_ideleNorm_det F

private theorem continuous_dn_rpow (s : ℝ) : Continuous (fun g : AdelicGL2 (𝓞 F) F => dn g ^ s) :=
  continuous_dn.rpow_const fun g => Or.inl (dn_pos g).ne'

private theorem subtype_mul_mem_slab (γ : ↥(Γp F)) {a b : ℝ} {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ slab F a b) :
    (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F a b := by
  show dn ((γ : AdelicGL2 (𝓞 F) F) * g) ∈ Set.Icc a b
  rw [dn_subtype_mul]
  exact hg

private theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab F a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F a b

private theorem preimage_subtype_mul_slab (γ : ↥(Γp F)) (a b : ℝ) :
    (fun w : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * w) ⁻¹' slab F a b = slab F a b := by
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [show ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * w)) = dn w from
    dn_subtype_mul γ w]

private theorem preimage_mul_right_slab (g : AdelicGL2 (𝓞 F) F) {a b : ℝ} :
    (fun w : AdelicGL2 (𝓞 F) F => w * g⁻¹) ⁻¹' slab F a b = slab F (a * dn g) (b * dn g) := by
  ext w
  have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det (w * g⁻¹)) = dn w / dn g := by
    rw [div_eq_mul_inv, ← dn_inv g]
    exact dn_mul w g⁻¹
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
  rw [h1, le_div_iff₀ (dn_pos g), div_le_iff₀ (dn_pos g)]

private theorem preimage_mul_left_slab (n : (AdeleRing (𝓞 F) F)ˣ) {a b : ℝ} :
    (fun w : AdelicGL2 (𝓞 F) F => (centralScalar (𝓞 F) F n)⁻¹ * w) ⁻¹' slab F a b
      = slab F (a * ideleNorm F n ^ 2) (b * ideleNorm F n ^ 2) := by
  ext w
  have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det ((centralScalar (𝓞 F) F n)⁻¹ * w))
      = dn w / ideleNorm F n ^ 2 := by
    rw [div_eq_mul_inv, ← dn_centralScalar, ← dn_inv, mul_comm (dn w)]
    exact dn_mul _ w
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
  rw [h1, le_div_iff₀ (pow_pos (ideleNorm_pos n) 2), div_le_iff₀ (pow_pos (ideleNorm_pos n) 2)]

private theorem image_mul_right_subset_slab {S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} (hS : S ⊆ slab F a b)
    (g : AdelicGL2 (𝓞 F) F) : (fun w => w * g) '' S ⊆ slab F (a * dn g) (b * dn g) := by
  rintro _ ⟨w, hw, rfl⟩
  have h := hS hw
  show dn (w * g) ∈ Set.Icc (a * dn g) (b * dn g)
  rw [dn_mul]
  exact ⟨mul_le_mul_of_nonneg_right h.1 (dn_pos g).le, mul_le_mul_of_nonneg_right h.2 (dn_pos g).le⟩

private theorem rpow_le_of_mem_slab {a b : ℝ} (ha : 0 < a) (s : ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ slab F a b) : ‖dn g ^ s‖ ≤ max (a ^ s) (b ^ s) := by
  have h : a ≤ dn g ∧ dn g ≤ b := hg
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (dn_pos g).le s)]
  rcases le_or_gt 0 s with hs | hs
  · exact (Real.rpow_le_rpow (dn_pos g).le h.2 hs).trans (le_max_right _ _)
  · refine le_trans ?_ (le_max_left _ _)
    rw [← neg_neg s, Real.rpow_neg (dn_pos g).le, Real.rpow_neg ha.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le h.1 (neg_nonneg.mpr hs.le))

private theorem centralScalar_comm_subtype (n : (AdeleRing (𝓞 F) F)ˣ) (γ : ↥(Γp F)) :
    centralScalar (𝓞 F) F n * (γ : AdelicGL2 (𝓞 F) F) = (γ : AdelicGL2 (𝓞 F) F) * centralScalar (𝓞 F) F n :=
  (mul_centralScalar_comm n _).symm

private theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp F) (AdelicGL2 (𝓞 F) F) ((μH F).restrict (slab F a b)) :=
  smulInvariantMeasure_restrict (Γp F) (μH F) (measurableSet_slab a b) (fun γ => preimage_subtype_mul_slab γ a b)

private def CoveredBy (D : Set (AdelicGL2 (𝓞 F) F)) (N : Finset (AdeleRing (𝓞 F) F)ˣ)
    (X : Set (AdelicGL2 (𝓞 F) F)) : Prop :=
  ∀ g ∈ X, ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
    (centralScalar (𝓞 F) F n)⁻¹ * (globalPoints (𝓞 F) F γ * g) ∈ D

private theorem CoveredBy.mono {D : Set (AdelicGL2 (𝓞 F) F)} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {X X' : Set (AdelicGL2 (𝓞 F) F)} (h : CoveredBy D N X) (hX : X' ⊆ X) : CoveredBy D N X' :=
  fun g hg => h g (hX hg)

private theorem coveredBy_of_forall {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)} {a b : ℝ}
    {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂) :
    CoveredBy (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N (slab F a b) := by
  intro g hg
  obtain ⟨γ, n, hn, x, hx, y, hy, hyx⟩ := h g hg
  refine ⟨γ, n, hn, ?_⟩
  rw [← hyx]
  show (centralScalar (𝓞 F) F n)⁻¹ * (y * (centralScalar (𝓞 F) F n * x)) ∈ _
  rw [← mul_assoc y, mul_centralScalar_comm n y, mul_assoc, inv_mul_cancel_left]
  exact Set.mem_iUnion₂.mpr ⟨x, hx, y, hy, rfl⟩

private theorem memLp_of_coveredBy {D S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hmem : MemLp f 2 ((μH F).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hχ : ∀ n, χ n ≠ 0)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F a b))) (hSs : S ⊆ slab F a b)
    (hX : CoveredBy D N (slab F a b)) : MemLp f 2 ((μH F).restrict S) := by
  have hcov' : ∀ g ∈ slab F a b, ∃ γ : ↥(Γp F), ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * ((γ : AdelicGL2 (𝓞 F) F) * g) ∈ D := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g hg
    exact ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩, n, hn, h⟩
  have hfa : ∀ (i : ↥(Γp F) × ↥N) (w : AdelicGL2 (𝓞 F) F),
      f ((centralScalar (𝓞 F) F (i.2 : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * (i.1 : AdelicGL2 (𝓞 F) F) * w)
        = χ (i.2 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ * f w := by
    rintro ⟨⟨_, γ, rfl⟩, n, hn⟩ w
    show f ((centralScalar (𝓞 F) F n)⁻¹ * globalPoints (𝓞 F) F γ * w) = χ n⁻¹ * f w
    rw [← map_inv, mul_assoc, hZ, hΓ]

  have h1 : AEStronglyMeasurable f ((μH F).restrict S) := by
    refine aestronglyMeasurable_of_cover_translates (μH F) hmem.1
      (fun i : ↥(Γp F) × ↥N =>
        (centralScalar (𝓞 F) F (i.2 : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * (i.1 : AdelicGL2 (𝓞 F) F))
      (fun i => χ (i.2 : (AdeleRing (𝓞 F) F)ˣ)⁻¹) (fun i => hχ _) hfa fun g hg => ?_
    obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
    refine Set.mem_iUnion.mpr ⟨⟨γ, n, hn⟩, ?_⟩
    show (centralScalar (𝓞 F) F n)⁻¹ * (γ : AdelicGL2 (𝓞 F) F) * g ∈ D
    rwa [mul_assoc]

  have h2 : ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) < ∞ := by
    haveI := smulInvariantMeasure_slab (F := F) a b
    have hcovE : S ⊆ ⋃ γ : ↥(Γp F), (γ • ·) ⁻¹'
        ((⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b) := fun g hg => by
      obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
      refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨n, hn, _, h, mul_inv_cancel_left _ _⟩, ?_⟩
      exact subtype_mul_mem_slab γ (hSs hg)
    have hF : ∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F), ‖f (γ • w)‖ₑ ^ (2 : ℝ) = ‖f w‖ₑ ^ (2 : ℝ) := by
      rintro ⟨_, γ, rfl⟩ w
      show ‖f (globalPoints (𝓞 F) F γ * w)‖ₑ ^ (2 : ℝ) = _
      rw [hΓ]
    have hD : ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) < ∞ := lintegral_lt_top_of_memLp_two hmem
    calc ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F)
        = ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) := by
          rw [Measure.restrict_restrict_of_subset hSs]
      _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b,
            ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) :=
          setLIntegral_fd_le_of_cover hS hcovE _ hF
      _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
          lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
      _ ≤ ∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
          setLIntegral_biUnion_translates_le (μH F) _ N (fun n => centralScalar (𝓞 F) F n)
            (fun n => ‖χ n‖ₑ ^ (2 : ℝ)) (fun n => ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
            (fun n w => by rw [hZ, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)])
      _ < ∞ := by
          refine ENNReal.sum_lt_top.mpr fun n _ => ENNReal.mul_lt_top ?_ hD
          exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
  exact memLp_two_of_lintegral h1 h2

private theorem memLp_translate_of_cover [(μH F).IsMulRightInvariant] {D S : Set (AdelicGL2 (𝓞 F) F)}
    {α β : ℝ} (hα : 0 < α) {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hmem : MemLp f 2 ((μH F).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hχ : ∀ n, χ n ≠ 0)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F α β))) (hSs : S ⊆ slab F α β)
    (hcov : ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, CoveredBy D N (slab F a b))
    (h : AdelicGL2 (𝓞 F) F) : MemLp (fun z => f (z * h)) 2 ((μH F).restrict S) := by
  obtain ⟨N, hN⟩ := hcov (α * dn h) (β * dn h) (mul_pos hα (dn_pos h))
  refine memLp_comp_mul_right (μH F) h ?_
  exact memLp_of_coveredBy hmem hΓ hZ hχ
    (isFundamentalDomain_image_mul_right (Γp F) (μH F) hS h (preimage_mul_right_slab h))
    (image_mul_right_subset_slab hSs h) hN

private theorem lintegral_sq_le_of_coveredBy {D S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F a b))) (hSs : S ⊆ slab F a b)
    (hX : CoveredBy D N (slab F a b)) :
    ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) ≤ ∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) := by
  have hcov' : ∀ g ∈ slab F a b, ∃ γ : ↥(Γp F), ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * ((γ : AdelicGL2 (𝓞 F) F) * g) ∈ D := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g hg
    exact ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩, n, hn, h⟩
  haveI := smulInvariantMeasure_slab (F := F) a b
  have hcovE : S ⊆ ⋃ γ : ↥(Γp F), (γ • ·) ⁻¹'
      ((⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b) := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
    refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨n, hn, _, h, mul_inv_cancel_left _ _⟩, ?_⟩
    exact subtype_mul_mem_slab γ (hSs hg)
  have hF : ∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F), ‖f (γ • w)‖ₑ ^ (2 : ℝ) = ‖f w‖ₑ ^ (2 : ℝ) := by
    rintro ⟨_, γ, rfl⟩ w
    show ‖f (globalPoints (𝓞 F) F γ * w)‖ₑ ^ (2 : ℝ) = _
    rw [hΓ]
  calc ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F)
      = ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) := by
        rw [Measure.restrict_restrict_of_subset hSs]
    _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b,
          ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) :=
        setLIntegral_fd_le_of_cover hS hcovE _ hF
    _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
    _ ≤ ∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
        setLIntegral_biUnion_translates_le (μH F) _ N (fun n => centralScalar (𝓞 F) F n)
          (fun n => ‖χ n‖ₑ ^ (2 : ℝ)) (fun n => ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
          (fun n w => by rw [hZ, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)])

private theorem eLpNorm_translate_le [(μH F).IsMulRightInvariant] {D S : Set (AdelicGL2 (𝓞 F) F)}
    {α β : ℝ} {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hmem : MemLp f 2 ((μH F).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hχ : ∀ n, χ n ≠ 0)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F α β))) (hSs : S ⊆ slab F α β)
    {a' b' : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ} (hN : CoveredBy D N (slab F a' b'))
    (h : AdelicGL2 (𝓞 F) F) (hh : slab F (α * dn h) (β * dn h) ⊆ slab F a' b') :
    eLpNorm (fun z => f (z * h)) 2 ((μH F).restrict S) ≤
      (∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F)) ^ (1 / 2 : ℝ) := by
  have hFD := isFundamentalDomain_image_mul_right (Γp F) (μH F) hS h (preimage_mul_right_slab h)
  have hSh : (fun w => w * h) '' S ⊆ slab F (α * dn h) (β * dn h) := image_mul_right_subset_slab hSs h
  have hN' : CoveredBy D N (slab F (α * dn h) (β * dn h)) := hN.mono hh
  have hmemSh : MemLp f 2 ((μH F).restrict ((fun w => w * h) '' S)) := memLp_of_coveredBy hmem hΓ hZ hχ hFD hSh hN'
  have hmp : MeasurePreserving (fun w => w * h) ((μH F).restrict S) ((μH F).restrict ((fun w => w * h) '' S)) :=
    (measurePreserving_mul_right (μH F) h).restrict_image_emb (measurableEmbedding_mulRight h) S
  have h1 : eLpNorm (fun z => f (z * h)) 2 ((μH F).restrict S) = eLpNorm f 2 ((μH F).restrict ((fun w => w * h) '' S)) :=
    eLpNorm_comp_measurePreserving hmemSh.1 hmp
  rw [h1, eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow (lintegral_sq_le_of_coveredBy hΓ hZ hFD hSh hN') (by norm_num)

end PeterssonSlabPairing
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain.AutomorphicForm.PeterssonSlabPairing"
end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain.AutomorphicForm.PeterssonSlabPairing P2MW.S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain.AutomorphicForm"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain.AutomorphicForm AutomorphicForm.PeterssonSlabPairing FundamentalDomainSlab in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (_hd : d₁ < d₂)
    (_hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ) (_hχ : ∀ n, χ n ≠ 0)
    (_hmem : MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (_hΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (_hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (α β : ℝ) (_hα : 0 < α) (_hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F)) (_hSs : S ⊆ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    (∀ h : AdelicGL2 (𝓞 F) F, MemLp (fun w => f (w * h)) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) ∧
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ h : AdelicGL2 (𝓞 F) F,
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det h) ∈ Set.Icc a b →
          eLpNorm (fun w => f (w * h)) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) ≤ C := by
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  have hcovN : ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ,
      CoveredBy (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N (slab F a b) := fun a b ha => by
    obtain ⟨N, hN⟩ := AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T _hd _hcov a b ha
    exact ⟨N, coveredBy_of_forall hN⟩
  refine ⟨fun h => memLp_translate_of_cover _hα _hmem _hΓ _hZ _hχ _hS _hSs hcovN h, fun a b ha hab => ?_⟩
  obtain ⟨N, hN⟩ := hcovN (α * a) (β * b) (mul_pos _hα ha)
  have hD : ∫⁻ w in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) < ⊤ :=
    lintegral_lt_top_of_memLp_two _hmem
  refine ⟨(∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖f w‖ₑ ^ (2 : ℝ)
      ∂(μH F)) ^ (1 / 2 : ℝ), ?_, fun h hh => ?_⟩
  · refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_of_lt ?_)
    refine ENNReal.sum_lt_top.mpr fun n _ => ENNReal.mul_lt_top ?_ hD
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
  · refine eLpNorm_translate_le _hmem _hΓ _hZ _hχ _hS _hSs hN h ?_
    intro g hg
    obtain ⟨h1, h2⟩ := hg
    have hβ : 0 < β := _hα.trans _hαβ
    exact ⟨le_trans (mul_le_mul_of_nonneg_left hh.1 _hα.le) h1, le_trans h2 (mul_le_mul_of_nonneg_left hh.2 hβ.le)⟩

end
end S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain (solution)
