-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.isCompactOperator_lift_rightConv_comp_cuspSubcarrier
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/bf4aafcf-1de6-5eda-8004-612b9e33d3d2

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
import Theorems.Thm_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_isCompactOperator_lift_rightConv_comp_cuspSubcarrier
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal NNReal InnerProductSpace BigOperators Topology Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace CT6

variable (F : Type) [Field F] [NumberField F]

private theorem _root_.eLpNorm_two_eq' {X : Type*} [MeasurableSpace X] (φ : X → ℂ) (ν : Measure X) :
    eLpNorm φ 2 ν = (∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rfl

theorem weight_le_of_mem {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) {x : AdelicGL2 (𝓞 F) F} (hx : x ∈ Φ₀) :
    weight F σ x ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hΦ₀.subset hx
  unfold weight
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact (Real.rpow_le_rpow (hΦ₀.pos.le.trans h1) h2 hs).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hΦ₀.pos h1 hs.le).trans (le_max_left _ _)

theorem le_weight_of_mem {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) {x : AdelicGL2 (𝓞 F) F} (hx : x ∈ Φ₀) :
    min (α ^ (-σ)) (β ^ (-σ)) ≤ weight F σ x := by
  obtain ⟨h1, h2⟩ := hΦ₀.subset hx
  have hxpos : 0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) := hΦ₀.pos.trans_le h1
  unfold weight
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact (min_le_left _ _).trans (Real.rpow_le_rpow hΦ₀.pos.le h1 hs)
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hxpos h2 hs.le)

theorem min_rpow_pos {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) :
    0 < min (α ^ (-σ)) (β ^ (-σ)) :=
  lt_min (Real.rpow_pos_of_pos hΦ₀.pos _) (Real.rpow_pos_of_pos hΦ₀.pos_right _)

theorem ae_restrict_mem_fd {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀), x ∈ Φ₀ := by
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F
  have hres : μ.restrict Φ₀ = (μ.restrict (detNormSlab F α β)).restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet

theorem weightedMeasure_le {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) :
    weightedMeasure F Φ₀ σ ≤
      ENNReal.ofReal (max (α ^ (-σ)) (β ^ (-σ))) • (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀ := by
  unfold weightedMeasure
  rw [← withDensity_const]
  exact withDensity_mono ((ae_restrict_mem_fd F hΦ₀).mono fun x hx => ENNReal.ofReal_le_ofReal (weight_le_of_mem F hΦ₀ σ hx))

theorem restrict_le_weightedMeasure {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) :
    ENNReal.ofReal (min (α ^ (-σ)) (β ^ (-σ))) • (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀ ≤
      weightedMeasure F Φ₀ σ := by
  unfold weightedMeasure
  rw [← withDensity_const]
  exact withDensity_mono ((ae_restrict_mem_fd F hΦ₀).mono fun x hx => ENNReal.ofReal_le_ofReal (le_weight_of_mem F hΦ₀ σ hx))

theorem eLpNorm_restrict_le {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ≤
      (ENNReal.ofReal (min (α ^ (-σ)) (β ^ (-σ))))⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm φ 2 (weightedMeasure F Φ₀ σ) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (min (α ^ (-σ)) (β ^ (-σ))) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (min_rpow_pos F hΦ₀ σ)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  set ρ := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀
  have hle : ρ ≤ c⁻¹ • weightedMeasure F Φ₀ σ := by
    have h := restrict_le_weightedMeasure F hΦ₀ σ
    rw [Measure.le_iff'] at h ⊢
    intro s
    have hs := h s
    rw [Measure.smul_apply, smul_eq_mul] at hs ⊢
    calc ρ s = c⁻¹ * (c * ρ s) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
      _ ≤ c⁻¹ * weightedMeasure F Φ₀ σ s := mul_le_mul_right hs _
  calc eLpNorm φ 2 ρ ≤ eLpNorm φ 2 (c⁻¹ • weightedMeasure F Φ₀ σ) := eLpNorm_mono_measure φ hle
    _ = c⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm φ 2 (weightedMeasure F Φ₀ σ) := by
        rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top, smul_eq_mul]

end CT6

open CT6 in
theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T) :
    IsCompactOperator (T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL) := by
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI hreg : (adelicGLHaar (Fin 2) (𝓞 F) F).Regular := by unfold adelicGLHaar; infer_instance
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set μw := weightedMeasure F Φ₀ σ with hμw
  set slab : Set (AdelicGL2 (𝓞 F) F) := detNormSlab F α β with hslab
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf

  set M := cuspMemberSubmodule F Φ₀ ξ with hM
  have hmem : ∀ φ : M, (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ memberSubmodule F Φ₀ ξ := fun φ => φ.2.1.1.1
  have hcont : ∀ φ : M, Continuous (φ : AdelicGL2 (𝓞 F) F → ℂ) := fun φ => φ.2.2
  have hcm : ∀ φ : M, (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := fun φ => ⟨hmem φ, hcont φ⟩
  have hls : ∀ φ : M, IsLsXiFunction (𝓞 F) F ⊤ ξ φ := fun φ =>
    ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp (hmem φ)).1
  have hL2 : ∀ φ : M, MemLp (φ : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀) := fun φ =>
    ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp (hmem φ)).2
  set tc : M → Carrier F Φ₀ σ := fun φ => toCarrier F hΦ₀ σ ξ ⟨φ, hmem φ⟩ with htc
  let ι := {φ : M // ‖tc φ‖ < 2}
  set u : ι → AdelicGL2 (𝓞 F) F → ℂ := fun i => rightConv F (i.1 : AdelicGL2 (𝓞 F) F → ℂ) f with hu
  have hu_mem : ∀ i : ι, u i ∈ contMemberSubmodule F Φ₀ ξ := fun i => hT.mapsTo _ (hcm i.1)
  have hTu : ∀ i : ι, T (tc i.1) = toCarrier F hΦ₀ σ ξ ⟨u i, (hu_mem i).1⟩ := fun i => hT.comm _ (hcm i.1)
  have hu_toLp : ∀ i : ι, (toCarrier F hΦ₀ σ ξ ⟨u i, (hu_mem i).1⟩ : Carrier F Φ₀ σ) =
      (memLp_weightedMeasure_of_mem F hΦ₀ σ (hu_mem i).1).toLp (u i) := fun i => rfl

  set cE : ℝ≥0∞ := (ENNReal.ofReal (min (α ^ (-σ)) (β ^ (-σ))))⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal with hcE
  have hcEtop : cE ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (min_rpow_pos F hΦ₀ σ)).ne')
  set cμ : ℝ := cE.toReal with hcμ
  have hcμ0 : 0 ≤ cμ := ENNReal.toReal_nonneg
  have hnorm_tc : ∀ φ : M, ‖tc φ‖ = (eLpNorm (φ : AdelicGL2 (𝓞 F) F → ℂ) 2 μw).toReal := fun φ =>
    Lp.norm_toLp (φ : AdelicGL2 (𝓞 F) F → ℂ) (memLp_weightedMeasure_of_mem F hΦ₀ σ (hmem φ))
  have hE_le : ∀ φ : M, (eLpNorm (φ : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀)).toReal ≤ cμ * ‖tc φ‖ := by
    intro φ
    have h1 := eLpNorm_restrict_le F hΦ₀ σ (φ : AdelicGL2 (𝓞 F) F → ℂ)
    have hfin : eLpNorm (φ : AdelicGL2 (𝓞 F) F → ℂ) 2 μw ≠ ⊤ := (memLp_weightedMeasure_of_mem F hΦ₀ σ (hmem φ)).eLpNorm_ne_top
    rw [hnorm_tc, hcμ, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hcEtop hfin) h1
  have hE_lt : ∀ i : ι, (eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀)).toReal ≤ cμ * 2 := fun i =>
    (hE_le i.1).trans (mul_le_mul_of_nonneg_left i.2.le hcμ0)

  have hΦ₀fin : μ Φ₀ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      F α β hΦ₀.pos hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
    have h' : μ (Φ₀ ∩ detNormSlab F α β) < ⊤ := h
    rwa [Set.inter_eq_left.mpr hΦ₀.subset] at h'
  set Cw : ℝ≥0∞ := ENNReal.ofReal (max (α ^ (-σ)) (β ^ (-σ))) with hCw
  set ν' : Measure (AdelicGL2 (𝓞 F) F) := Cw • μ.restrict Φ₀ with hν'
  have hμw_le : μw ≤ ν' := weightedMeasure_le F hΦ₀ σ
  have hν'fin : ν' Set.univ < ⊤ := by
    rw [hν', Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΦ₀fin
  haveI : IsFiniteMeasure ν' := ⟨hν'fin⟩
  haveI : IsFiniteMeasure μw := ⟨(Measure.le_iff'.1 hμw_le Set.univ).trans_lt hν'fin⟩

  have htight : ∀ η : ℝ≥0∞, 0 < η → ∃ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K ∧ μw Kᶜ < η := by
    intro η hη
    obtain ⟨K, -, hKc, hK⟩ := MeasurableSet.univ.exists_isCompact_diff_lt (μ := ν') (measure_ne_top ν' _) hη.ne'
    refine ⟨K, hKc, lt_of_le_of_lt (Measure.le_iff'.1 hμw_le _) ?_⟩
    rwa [Set.compl_eq_univ_diff]

  have hequi : Equicontinuous u := by
    intro g₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    set ε₃ : ℝ := ε / (cμ * 2 + 1) with hε₃
    have hε₃0 : 0 < ε₃ := div_pos hε (by positivity)
    obtain ⟨V, hV, hVφ⟩ :=
      AutomorphicForm.exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
        F ξ f hf (isCompact_singleton (x := g₀)) α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain ε₃ hε₃0
    have hnhds : (fun g => g₀⁻¹ * g) ⁻¹' V ∈ 𝓝 g₀ :=
      (continuous_const_mul g₀⁻¹).continuousAt.preimage_mem_nhds (by simpa using hV)
    filter_upwards [hnhds] with g hg i
    have h := hVφ i.1 (hls i.1) (hcont i.1) (hL2 i.1) g₀ (Set.mem_singleton g₀) (g₀⁻¹ * g) hg
    rw [mul_inv_cancel_left] at h
    rw [dist_eq_norm, norm_sub_rev]
    calc ‖u i g - u i g₀‖ ≤ ε₃ * (eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀)).toReal := h
      _ ≤ ε₃ * (cμ * 2) := mul_le_mul_of_nonneg_left (hE_lt i) hε₃0.le
      _ < ε := by rw [hε₃, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith

  have hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀ := by
    intro x
    have hRc : IsCompact ((fun y => x * y) '' tsupport f) := hfs.image (continuous_const_mul x)
    obtain ⟨N, hN⟩ :=
      AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
        F ξ hRc α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
    set bE : ℝ≥0∞ := ENNReal.ofReal N ^ (1 / 2 : ℝ) with hbE
    have hbEtop : bE ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    refine ⟨(eLpNorm f 2 μ).toReal * (bE.toReal * (cμ * 2)), fun i => ?_⟩
    have hCS := norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul F (i.1 : AdelicGL2 (𝓞 F) F → ℂ) f
      (hcont i.1) hfc hfs x
    refine hCS.trans (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
    have h2 : eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict ((fun y => x * y) '' tsupport f)) ≤
        bE * eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀) := by
      rw [eLpNorm_two_eq', eLpNorm_two_eq', hbE, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
      exact ENNReal.rpow_le_rpow (hN _ (hls i.1) (hcont i.1)) (by norm_num)
    have h3 : bE * eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀) ≠ ⊤ :=
      ENNReal.mul_ne_top hbEtop (hL2 i.1).eLpNorm_ne_top
    calc (eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict ((fun y => x * y) '' tsupport f))).toReal
        ≤ (bE * eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀)).toReal := ENNReal.toReal_mono h3 h2
      _ = bE.toReal * (eLpNorm (i.1 : AdelicGL2 (𝓞 F) F → ℂ) 2 (μ.restrict Φ₀)).toReal := ENNReal.toReal_mul
      _ ≤ bE.toReal * (cμ * 2) := mul_le_mul_of_nonneg_left (hE_lt i) ENNReal.toReal_nonneg

  obtain ⟨T₀, c, hc, w, hcovall⟩ := SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet F
  have hcov := hcovall 1 2 two_pos (by norm_num)
  obtain ⟨T', hT'⟩ := exists_finset_slab_covering_of_coversModCentre F c w 1 2 T₀ (by norm_num) hcov α β hΦ₀.pos
  obtain ⟨C₁, hC₁⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
      F ξ f hf c w 1 2 T' hc one_pos α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
  have hsup : ∀ i : ι, ∀ x ∈ Φ₀, ‖u i x‖ ≤ max C₁ 0 * (cμ * 2) := by
    intro i x hx
    obtain ⟨γ, hγ⟩ := hT' x (hΦ₀.subset hx)
    have hinv : u i x = u i (globalPoints (𝓞 F) F γ * x) := by
      show rightConv F (i.1 : AdelicGL2 (𝓞 F) F → ℂ) f x = rightConv F (i.1 : AdelicGL2 (𝓞 F) F → ℂ) f (globalPoints (𝓞 F) F γ * x)
      rw [← rightConv_comp_mul_left]
      congr 1
      funext y
      exact ((hls i.1).left_invariant γ y).symm
    rw [hinv]
    refine (hC₁ _ (hls i.1) i.1.2.1.1.2 (hcont i.1) (hL2 i.1) _ hγ).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) ENNReal.toReal_nonneg).trans ?_
    exact mul_le_mul_of_nonneg_left (hE_lt i) (le_max_right _ _)
  have hae_mem : ∀ᵐ x ∂μw, x ∈ Φ₀ :=
    (withDensity_absolutelyContinuous _ _) (ae_restrict_mem_fd F hΦ₀)
  have hbound : ∀ i : ι, ∀ᵐ x ∂μw, ‖u i x‖ ≤ max C₁ 0 * (cμ * 2) := fun i => hae_mem.mono fun x hx => hsup i x hx

  set B₂ : Set (Carrier F Φ₀ σ) := Set.range fun i : ι => T (tc i.1) with hB₂
  have hB₂tb : TotallyBounded B₂ := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨s, hs⟩ :=
      MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
        u μw 2 one_le_two ENNReal.ofNat_ne_top htight hequi hpt _ hbound (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    refine ⟨(s.image fun j : ι => T (tc j.1) : Finset (Carrier F Φ₀ σ)), Finset.finite_toSet _, ?_⟩
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, hij⟩ := hs i
    refine Set.mem_iUnion₂.2 ⟨T (tc j.1), by simpa using ⟨j, hj, rfl⟩, ?_⟩
    show dist (T (tc i.1)) (T (tc j.1)) < ε
    rw [hTu, hTu, hu_toLp, hu_toLp, dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    exact ENNReal.toReal_lt_of_lt_ofReal hij

  set D : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ) (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype M) with hD
  have hcl : (cuspSubcarrier F hΦ₀ σ ξ : Set (Carrier F Φ₀ σ)) = closure (D : Set (Carrier F Φ₀ σ)) :=
    Submodule.topologicalClosure_coe D
  have hDball : (D : Set (Carrier F Φ₀ σ)) ∩ Metric.ball 0 2 ⊆ (fun i : ι => tc i.1) '' Set.univ := by
    rintro v ⟨⟨⟨φ, hφm⟩, hφM, rfl⟩, hv⟩
    have hφM' : φ ∈ M := hφM
    refine ⟨⟨⟨φ, hφM'⟩, ?_⟩, Set.mem_univ _, rfl⟩
    simpa [htc] using hv
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos, ?_⟩
  have himg : (T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL) '' Metric.closedBall 0 1 ⊆ closure B₂ := by
    rintro _ ⟨v, hv, rfl⟩
    have hv2 : (v : Carrier F Φ₀ σ) ∈ Metric.ball (0 : Carrier F Φ₀ σ) 2 := by
      rw [Metric.mem_ball, dist_zero_right]
      have : ‖(v : Carrier F Φ₀ σ)‖ ≤ 1 := by simpa using hv
      linarith
    have hvcl : (v : Carrier F Φ₀ σ) ∈ closure ((D : Set (Carrier F Φ₀ σ)) ∩ Metric.ball 0 2) := by
      have hvD : (v : Carrier F Φ₀ σ) ∈ closure (D : Set (Carrier F Φ₀ σ)) := by rw [← hcl]; exact v.2
      rw [Set.inter_comm]
      exact Metric.isOpen_ball.inter_closure ⟨hv2, hvD⟩
    have hTv : T v ∈ closure (T '' ((D : Set (Carrier F Φ₀ σ)) ∩ Metric.ball 0 2)) :=
      image_closure_subset_closure_image T.continuous ⟨_, hvcl, rfl⟩
    refine closure_mono ?_ hTv
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨i, -, rfl⟩ := hDball hw
    exact ⟨i, rfl⟩
  have hcpt : IsCompact (closure B₂) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hB₂tb.closure, isClosed_closure.isComplete⟩
  exact hcpt.of_isClosed_subset isClosed_closure (closure_minimal himg isClosed_closure)

end S_AutomorphicForm_CuspidalSpectrum_isCompactOperator_lift_rightConv_comp_cuspSubcarrier
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_isCompactOperator_lift_rightConv_comp_cuspSubcarrier (solution)
