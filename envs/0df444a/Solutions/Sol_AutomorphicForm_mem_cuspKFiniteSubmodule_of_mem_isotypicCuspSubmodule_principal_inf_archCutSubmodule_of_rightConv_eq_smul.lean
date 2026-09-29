-- Prove2me | solution 1 for AutomorphicForm.mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/007348ac-7fc5-57eb-a92f-f26486bc7a45

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_NumberField_SiegelVolume
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

open AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

open scoped ProbabilityTheory

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ) (hlam : lam ≠ 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    (heig : rightConv F φ f = lam • φ) :
    φ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
  classical
  obtain ⟨hφi, hφcut⟩ := Submodule.mem_inf.mp hφ
  have hcont : Continuous φ := continuous_of_mem_isotypicCuspSubmodule hφi
  refine Submodule.subset_span ⟨fun g => ?_, hcont, tys, hφcut⟩

  obtain ⟨α, β, Φ₀, hΦ₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain F
  have hmem : φ ∈ cuspMemberSubmodule F Φ₀ ξ := by
    refine (Submodule.span_le.mpr fun χ hχ => ?_) hφi
    exact ⟨⟨⟨AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre F c u d₁ d₂ T
        hd hcov α β hΦ₀.pos Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ χ hχ.smoothCusp.1.1, hχ.smoothCusp.1.2⟩,
      hχ.smoothCusp.2⟩, hχ.continuous⟩
  have hy : rightTranslate F g φ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ hmem
  have hlx := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hmem.1.1.1
  have hlxy := (mem_memberSubmodule_iff' F Φ₀ ξ (rightTranslate F g φ)).mp hy.1.1.1

  have hMemD : MemLp (rightTranslate F g φ) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
    haveI hRinv : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
      NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
    have hDclosed : IsClosed (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
      refine Set.Finite.isClosed_biUnion (Finset.finite_toSet T) fun x _ => ?_
      exact (Homeomorph.mulRight x).isClosed_image.mpr (isClosed_centreCutSiegelSet c u d₁ d₂)
    have hDfin : adelicGLHaar (Fin 2) (𝓞 F) F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
      refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
      have himg : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
        ext g'; constructor
        · rintro ⟨h, hh, rfl⟩; simpa [mul_inv_cancel_right] using hh
        · intro hg; exact ⟨g' * x⁻¹, hg, by simp only [inv_mul_cancel_right]⟩
      rw [himg, ← Measure.map_apply (measurable_mul_const x⁻¹) (isClosed_centreCutSiegelSet c u d₁ d₂).measurableSet,
        map_mul_right_eq_self]
      exact NumberField.SiegelVolume.measure_centreCutSiegelSet_lt_top (F := F) (adelicGLHaar (Fin 2) (𝓞 F) F) hc u hd₁ d₂
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
      isFiniteMeasure_restrict.mpr hDfin.ne

    obtain ⟨C, hC⟩ :=
      AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
        F ξ f hf c u d₁ d₂ (T.image (· * g)) hc hd₁ α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
    have hb := hC φ hlx.1 hmem.1.1.2 hcont hlx.2
    have heig' : ∀ y, φ y = lam⁻¹ * rightConv F φ f y := fun y => by
      have h1 := congrFun heig y
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      rw [h1, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
    refine MemLp.of_bound hy.2.aestronglyMeasurable
      (‖lam⁻¹‖ * (C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal))
      ((ae_restrict_mem hDclosed.measurableSet).mono fun y hyW => ?_)
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hyW
    have hmemg : s * x * g ∈ ⋃ x' ∈ T.image (· * g), (· * x') '' centreCutSiegelSet F c u d₁ d₂ :=
      Set.mem_iUnion₂.mpr ⟨x * g, Finset.mem_image_of_mem _ hx, s, hs, (mul_assoc s x g).symm⟩
    calc ‖rightTranslate F g φ (s * x)‖ = ‖lam⁻¹ * rightConv F φ f (s * x * g)‖ := by
          rw [rightTranslate_apply, heig']
      _ = ‖lam⁻¹‖ * ‖rightConv F φ f (s * x * g)‖ := norm_mul _ _
      _ ≤ ‖lam⁻¹‖ * (C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal) :=
          mul_le_mul_of_nonneg_left (hb _ hmemg) (norm_nonneg _)
  refine ⟨⟨?_, hy.1.1.2⟩, hy.1.2⟩
  exact (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (rightTranslate F g φ)).mpr
    ⟨hlxy.1, hMemD⟩

end S_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_mem_cuspKFiniteSubmodule_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul (solution)
