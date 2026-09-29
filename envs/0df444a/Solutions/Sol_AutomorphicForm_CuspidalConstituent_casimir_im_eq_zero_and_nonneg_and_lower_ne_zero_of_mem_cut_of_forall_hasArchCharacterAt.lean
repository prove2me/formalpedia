-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/31705c25-453c-5d28-8ac8-bdb4e0ad7f76

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace UPOSgen38

variable (K : Type) [Field K] [NumberField K]

theorem rightTranslate_one (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

theorem left_invariant_and_continuous_of_mem_cuspKFiniteSubmodule
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧ Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ =>
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧ Continuous φ)
    ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    rw [rightTranslate_one] at h1
    have hls := ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ φ).mp h1.1.1).1
    exact ⟨hls.left_invariant, hcont⟩
  · exact ⟨fun _ _ => rfl, continuous_zero⟩
  · rintro u w - - ⟨hu1, hu3⟩ ⟨hw1, hw3⟩
    exact ⟨fun γ g => by simp only [Pi.add_apply, hu1, hw1], hu3.add hw3⟩
  · rintro r u - ⟨hu1, hu3⟩
    exact ⟨fun γ g => by simp only [Pi.smul_apply, hu1], hu3.const_smul r⟩

theorem setIntegral_mul_conj_self_eq (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ g in 𝓕, u g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = ((∫ g in 𝓕, ‖u g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.mul_conj']
  push_cast
  rfl

theorem setIntegral_norm_sq_nonneg (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    0 ≤ ∫ g in 𝓕, ‖u g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  integral_nonneg fun g => sq_nonneg _

theorem setIntegral_mul_conj_smul (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (a : ℂ) (u v : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ g in 𝓕, u g * conj ((a • v) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = conj a * ∫ g in 𝓕, u g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  rw [← integral_const_mul]
  congr 1
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem setIntegral_smul_mul_conj (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (a : ℂ) (u v : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ g in 𝓕, (a • u) g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = a * ∫ g in 𝓕, u g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  rw [← integral_const_mul]
  congr 1
  funext g
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem setIntegral_zero_fun (𝓕 : Set (AdelicGL2 (𝓞 K) K)) :
    ∫ g in 𝓕, ‖(0 : AdelicGL2 (𝓞 K) K → ℂ) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  simp

theorem peterssonIntegral_zero_eq (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    peterssonIntegral K 0 𝓕 u u = ∫ g in 𝓕, u g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  unfold peterssonIntegral
  congr 1
  funext g
  rw [neg_zero, Real.rpow_zero]
  push_cast
  ring

theorem cut_package (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) x)
    (m : ℤ) (hxm : HasArchCharacterAt₀ K w (archWeightCharAt hw m) x) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) ∧
    Continuous x ∧ IsArchSmoothAt hw x ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧
    HasArchCharacterAt₀ K w (archWeightCharAt hw m) x ∧
    (∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d x g‖ ≤ B) ∧
        (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B)) := by
  have hxV : x ∈ V := hx.1.1
  obtain ⟨hleft, hcont⟩ := left_invariant_and_continuous_of_mem_cuspKFiniteSubmodule K _ ξ (hV.1.le hxV)
  have hS := fun l : List ArchDir =>
    AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys x hx w hw l
  exact ⟨hleft, hcont, (hS []).1, fun d => (hS [d]).2, fun d d' => (hS [d, d']).2, hxm, fun e₁ e₂ he₁ he =>
    AutomorphicForm.CuspidalConstituent.exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw x hx hpure m hxm e₁ e₂ he₁ he⟩

theorem setIntegral_norm_sq_ne_zero
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (hfin : (adelicGLHaar (Fin 2) (𝓞 K) K) 𝓕 < ⊤)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    {B : ℝ} (hB : ∀ g : AdelicGL2 (𝓞 K) K,
      ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → ‖x g‖ ≤ B)
    (hne : ∃ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ x g ≠ 0) :
    (∫ g in 𝓕, ‖x g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ 0 := by
  have hint : IntegrableOn
      (fun g => ‖x g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-(0 : ℝ))) 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    have hfun : (fun g : AdelicGL2 (𝓞 K) K =>
        ‖x g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-(0 : ℝ))) = fun g => ‖x g‖ ^ 2 := by
      funext g; rw [neg_zero, Real.rpow_zero, mul_one]
    rw [hfun]
    refine Measure.integrableOn_of_bounded (M := B ^ 2) hfin.ne
      ((continuous_norm.comp hxc).pow 2).aestronglyMeasurable ?_
    refine (ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB g (h𝓕s hg)) 2
  have h := AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
    K 0 e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x hxc hxG hne hint
  rw [peterssonIntegral_zero_eq, setIntegral_mul_conj_self_eq] at h
  exact fun h0 => h (by rw [h0]; simp)

theorem core (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsReal)
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ 𝓕 : Set (AdelicGL2 (𝓞 K) K),
      lam.im * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0 ∧
      (∫ g in 𝓕, ‖(archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (4 * lam.re + n * (n - 2)) * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      (∫ g in 𝓕, ‖(archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (4 * lam.re + n * (n + 2)) * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      ((∃ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ y g ≠ 0) →
        (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ 0) ∧
      ((∃ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ (archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g ≠ 0) →
        (∫ g in 𝓕, ‖(archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ 0) ∧
      ((∃ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ (archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g ≠ 0) →
        (∫ g in 𝓕, ‖(archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ 0) := by

  obtain ⟨d₁', d₂', tset, 𝓕, -, h𝓕m, h𝓕s, h𝓕, -⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
      K c u d₁ d₂ T hc hd₁ hd hcov e₁ e₂ he₁ he
  refine ⟨𝓕, ?_⟩
  have hfin : (adelicGLHaar (Fin 2) (𝓞 K) K) 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h

  have hG := AutomorphicForm.CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
    K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys w hw y hy hpure n hyn
  have hA := hG.1 1
  have hB := hG.2 1
  simp only [Function.iterate_one] at hA hB
  obtain ⟨⟨tysA, hAmem⟩, hAoth, hAn⟩ := hA
  obtain ⟨⟨tysB, hBmem⟩, hBoth, hBn⟩ := hB
  have hApure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m)
      (archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) := by
    intro v hv
    by_cases hvw : v = w
    · subst hvw; exact ⟨_, hAn⟩
    · obtain ⟨m, hm⟩ := hpure v hv; exact ⟨m, hAoth v hv m hvw hm⟩
  have hBpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m)
      (archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) := by
    intro v hv
    by_cases hvw : v = w
    · subst hvw; exact ⟨_, hBn⟩
    · obtain ⟨m, hm⟩ := hpure v hv; exact ⟨m, hBoth v hv m hvw hm⟩

  obtain ⟨hyl, hyc, hys, hyD, hyDD, -, hybdd⟩ :=
    cut_package K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw y hy hpure n hyn
  obtain ⟨hAl, hAc, hAs, hAD, hADD, -, hAbdd⟩ :=
    cut_package K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tysA w hw _ hAmem hApure _ hAn
  obtain ⟨hBl, hBc, hBs, hBD, hBDD, -, hBbdd⟩ :=
    cut_package K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tysB w hw _ hBmem hBpure _ hBn
  obtain ⟨By, hBy⟩ := hybdd e₁ e₂ he₁ he
  obtain ⟨BA, hBA⟩ := hAbdd e₁ e₂ he₁ he
  obtain ⟨BB, hBB⟩ := hBbdd e₁ e₂ he₁ he

  have hΩ : archCasimirAt hw y = lam • y := (hlam y hy.1.1).2
  have hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y :=
    AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt K w hw n y hys hyn
  have hOS := AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
    K w hw y hys (Complex.I * n) lam hm hΩ
  have hRL : archDerivAt hw .H (archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) + Complex.I • (archDerivAt hw .E (archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) + archDerivAt hw .Fm (archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)))
      = (-4 * lam + (Complex.I * n) ^ 2 - 2 * Complex.I * (Complex.I * n)) • y := by
    have h := hOS.2.2.1 1
    simp only [Function.iterate_one, Finset.prod_range_one, Nat.cast_zero, mul_zero, sub_zero] at h
    exact h
  have hLR : archDerivAt hw .H (archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) - Complex.I • (archDerivAt hw .E (archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) + archDerivAt hw .Fm (archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)))
      = (-4 * lam + (Complex.I * n) ^ 2 + 2 * Complex.I * (Complex.I * n)) • y := by
    have h := hOS.2.2.2 1
    simp only [Function.iterate_one, Finset.prod_range_one, Nat.cast_zero, mul_zero, add_zero] at h
    exact h

  have bnd2 : ∀ {B₁ B₂ : ℝ} {x₁ x₂ : AdelicGL2 (𝓞 K) K → ℂ},
      (∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
        ‖x₁ g‖ ≤ B₁ ∧ (∀ d : ArchDir, ‖archDerivAt hw d x₁ g‖ ≤ B₁) ∧
          (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x₁) g‖ ≤ B₁)) →
      (∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
        ‖x₂ g‖ ≤ B₂ ∧ (∀ d : ArchDir, ‖archDerivAt hw d x₂ g‖ ≤ B₂) ∧
          (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x₂) g‖ ≤ B₂)) →
      ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
        ‖x₁ g‖ ≤ max B₁ B₂ ∧ ‖x₂ g‖ ≤ max B₁ B₂ ∧
        (∀ d : ArchDir, ‖archDerivAt hw d x₁ g‖ ≤ max B₁ B₂ ∧ ‖archDerivAt hw d x₂ g‖ ≤ max B₁ B₂) ∧
        (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x₁) g‖ ≤ max B₁ B₂ ∧
          ‖archDerivAt hw d (archDerivAt hw d' x₂) g‖ ≤ max B₁ B₂) := by
    intro B₁ B₂ x₁ x₂ h₁ h₂ g hg
    obtain ⟨a0, a1, a2⟩ := h₁ g hg
    obtain ⟨b0, b1, b2⟩ := h₂ g hg
    exact ⟨a0.trans (le_max_left _ _), b0.trans (le_max_right _ _),
      fun d => ⟨(a1 d).trans (le_max_left _ _), (b1 d).trans (le_max_right _ _)⟩,
      fun d d' => ⟨(a2 d d').trans (le_max_left _ _), (b2 d d').trans (le_max_right _ _)⟩⟩
  have hALGyy := AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
    K w hw e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 y y hyl hyl hyc hyc hys hys hyD hyD hyDD hyDD (max By By) (bnd2 hBy hBy)
  have hALGyA := AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
    K w hw e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 y (archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) hyl hAl hyc hAc hys hAs hyD hAD hyDD hADD (max By BA) (bnd2 hBy hBA)
  have hALGyB := AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
    K w hw e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 y (archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) hyl hBl hyc hBc hys hBs hyD hBD hyDD hBDD (max By BB) (bnd2 hBy hBB)

  have h1 : lam.im * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0 := by
    have h := hALGyy.1
    rw [hΩ, setIntegral_smul_mul_conj, setIntegral_mul_conj_smul, setIntegral_mul_conj_self_eq] at h
    have h' := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      Complex.conj_re, Complex.conj_im] at h'
    linarith

  have h2 : (∫ g in 𝓕, ‖(archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (4 * lam.re + n * (n - 2)) * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    have h := hALGyA.2.1
    beta_reduce at h
    rw [hRL, setIntegral_mul_conj_smul, setIntegral_mul_conj_self_eq, setIntegral_mul_conj_self_eq] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.conj_re, Complex.conj_im] at h'
    rw [h']
    have : (-4 * lam + (Complex.I * n) ^ 2 - 2 * Complex.I * (Complex.I * n)).re = -(4 * lam.re + n * (n - 2)) := by
      simp [sq, Complex.mul_re, Complex.mul_im]
      ring
    rw [this]
    ring

  have h3 : (∫ g in 𝓕, ‖(archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (4 * lam.re + n * (n + 2)) * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    have h := hALGyB.2.2
    beta_reduce at h
    rw [hLR, setIntegral_mul_conj_smul, setIntegral_mul_conj_self_eq, setIntegral_mul_conj_self_eq] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.conj_re, Complex.conj_im] at h'
    rw [h']
    have : (-4 * lam + (Complex.I * n) ^ 2 + 2 * Complex.I * (Complex.I * n)).re = -(4 * lam.re + n * (n + 2)) := by
      simp [sq, Complex.mul_re, Complex.mul_im]
      ring
    rw [this]
    ring
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · exact setIntegral_norm_sq_ne_zero K e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin y hyc hyl (fun g hg => (hBy g hg).1)
  · exact setIntegral_norm_sq_ne_zero K e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin _ hAc hAl (fun g hg => (hBA g hg).1)
  · exact setIntegral_norm_sq_ne_zero K e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 hfin _ hBc hBl (fun g hg => (hBB g hg).1)

theorem slab_around (g : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det g) / 2 ∧
    ideleNorm K (Matrix.GeneralLinearGroup.det g) / 2 < 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ∧
    ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
      Set.Ioo (ideleNorm K (Matrix.GeneralLinearGroup.det g) / 2) (2 * ideleNorm K (Matrix.GeneralLinearGroup.det g)) := by
  have h := ideleNorm_pos (Matrix.GeneralLinearGroup.det g)
  exact ⟨by linarith, by linarith, by constructor <;> linarith⟩

theorem main (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsReal)
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) (hy0 : y ≠ 0) :
    lam.im = 0 ∧ 0 ≤ 4 * lam.re + n * (n - 2) ∧ 0 ≤ 4 * lam.re + n * (n + 2) ∧
      ((archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) ≠ 0 ↔ 0 < 4 * lam.re + n * (n - 2)) ∧ ((archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) ≠ 0 ↔ 0 < 4 * lam.re + n * (n + 2)) := by

  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hy0
  obtain ⟨he₁, he, hmem⟩ := slab_around K g₀
  obtain ⟨𝓕, h1, h2, h3, h4, -, -⟩ :=
    core K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw lam hlam y hy hpure n hyn _ _ he₁ he
  have hry0 : (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ 0 := h4 ⟨g₀, hmem, hg₀⟩
  have hry : 0 < (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := lt_of_le_of_ne (setIntegral_norm_sq_nonneg K 𝓕 y) (Ne.symm hry0)
  have hrA : 0 ≤ (∫ g in 𝓕, ‖(archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := setIntegral_norm_sq_nonneg K 𝓕 _
  have hrB : 0 ≤ (∫ g in 𝓕, ‖(archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := setIntegral_norm_sq_nonneg K 𝓕 _
  have him : lam.im = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hry0
  have hnnA : 0 ≤ 4 * lam.re + n * (n - 2) := by
    by_contra hneg
    have hneg' : 4 * lam.re + n * (n - 2) < 0 := lt_of_not_ge hneg
    have : (∫ g in 𝓕, ‖(archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) < 0 := by rw [h2]; exact mul_neg_of_neg_of_pos hneg' hry
    linarith
  have hnnB : 0 ≤ 4 * lam.re + n * (n + 2) := by
    by_contra hneg
    have hneg' : 4 * lam.re + n * (n + 2) < 0 := lt_of_not_ge hneg
    have : (∫ g in 𝓕, ‖(archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) < 0 := by rw [h3]; exact mul_neg_of_neg_of_pos hneg' hry
    linarith
  refine ⟨him, hnnA, hnnB, ⟨fun hA => ?_, fun hpos hA0 => ?_⟩, ⟨fun hB => ?_, fun hpos hB0 => ?_⟩⟩
  ·
    obtain ⟨g₁, hg₁⟩ := Function.ne_iff.mp hA
    obtain ⟨he₁', he', hmem'⟩ := slab_around K g₁
    obtain ⟨𝓕₁, -, h2', -, -, h5', -⟩ :=
      core K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw lam hlam y hy hpure n hyn _ _ he₁' he'
    have hne := h5' ⟨g₁, hmem', hg₁⟩
    have hpos : 0 < ∫ g in 𝓕₁, ‖(archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
      lt_of_le_of_ne (setIntegral_norm_sq_nonneg K 𝓕₁ _) (Ne.symm hne)
    have hy1 : 0 ≤ ∫ g in 𝓕₁, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := setIntegral_norm_sq_nonneg K 𝓕₁ y
    rw [h2'] at hpos
    by_contra hle
    have hle' : 4 * lam.re + n * (n - 2) ≤ 0 := le_of_not_gt hle
    have : (4 * lam.re + n * (n - 2)) * ∫ g in 𝓕₁, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle' hy1
    linarith
  ·
    have hzero : (∫ g in 𝓕, ‖(archDerivAt hw .H y - Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0 := by rw [hA0]; simp
    rw [h2] at hzero
    have : 0 < (4 * lam.re + n * (n - 2)) * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := mul_pos hpos hry
    linarith
  · obtain ⟨g₁, hg₁⟩ := Function.ne_iff.mp hB
    obtain ⟨he₁', he', hmem'⟩ := slab_around K g₁
    obtain ⟨𝓕₁, -, -, h3', -, -, h6'⟩ :=
      core K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw lam hlam y hy hpure n hyn _ _ he₁' he'
    have hne := h6' ⟨g₁, hmem', hg₁⟩
    have hpos : 0 < ∫ g in 𝓕₁, ‖(archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
      lt_of_le_of_ne (setIntegral_norm_sq_nonneg K 𝓕₁ _) (Ne.symm hne)
    have hy1 : 0 ≤ ∫ g in 𝓕₁, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := setIntegral_norm_sq_nonneg K 𝓕₁ y
    rw [h3'] at hpos
    by_contra hle
    have hle' : 4 * lam.re + n * (n + 2) ≤ 0 := le_of_not_gt hle
    have : (4 * lam.re + n * (n + 2)) * ∫ g in 𝓕₁, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle' hy1
    linarith
  · have hzero : (∫ g in 𝓕, ‖(archDerivAt hw .H y + Complex.I • (archDerivAt hw .E y + archDerivAt hw .Fm y)) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0 := by rw [hB0]; simp
    rw [h3] at hzero
    have : 0 < (4 * lam.re + n * (n + 2)) * (∫ g in 𝓕, ‖y g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := mul_pos hpos hry
    linarith

end UPOSgen38

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsReal)
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (hy0 : y ≠ 0) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    lam.im = 0 ∧ 0 ≤ 4 * lam.re + n * (n - 2) ∧ 0 ≤ 4 * lam.re + n * (n + 2) ∧
      (lower y ≠ 0 ↔ 0 < 4 * lam.re + n * (n - 2)) ∧ (raise y ≠ 0 ↔ 0 < 4 * lam.re + n * (n + 2)) := by
  intro lower raise
  exact UPOSgen38.main K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw lam hlam y hy hpure n hyn hy0

end S_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt (solution)
