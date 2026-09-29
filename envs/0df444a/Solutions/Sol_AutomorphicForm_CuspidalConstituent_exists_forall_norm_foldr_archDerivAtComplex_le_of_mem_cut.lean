-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b9d7c771-036e-5065-8501-0952be0ad409

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
import Theorems.Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace CoreSupplyC

variable (K : Type) [Field K] [NumberField K]

theorem isFactorizableTestFn_leftDeriv {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K (fun y => deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0) := by
  obtain ⟨fa, ff, hfa, hff, hαeq⟩ := hα
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', ff, hfa', hff, fun y => ?_⟩
  have h1 : (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) =
      fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) := by
    funext t; exact hαeq _
  show deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0 = _
  rw [h1]
  exact congrFun heq y

theorem exists_foldr_eq_rightConv {w : InfinitePlace K} (hw : w.IsComplex) (x' α : AdelicGL2 (𝓞 K) K → ℂ)
    (hcont : Continuous x') (hα : IsFactorizableTestFn K α) (l : List ArchDirComplex) :
    ∃ γ : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K γ ∧
      l.foldr (archDerivAtComplex hw) (rightConv K x' α) = rightConv K x' γ := by
  induction l with
  | nil => exact ⟨α, hα, rfl⟩
  | cons d l ih =>
    obtain ⟨γ, hγ, hfold⟩ := ih
    refine ⟨fun y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0,
      isFactorizableTestFn_leftDeriv K hw d γ hγ, ?_⟩
    rw [List.foldr_cons, hfold]
    exact ((AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).1 x' γ hcont hγ).2

theorem rightTranslate_one' (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

def dirs : List ArchDirComplex := [.H, .E, .Fm, .iH, .iE, .iFm]

theorem mem_dirs (d : ArchDirComplex) : d ∈ dirs := by
  cases d <;> simp [dirs]

end CoreSupplyC

end

open CoreSupplyC in

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
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) (l : List ArchDirComplex) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖(l.foldr (archDerivAtComplex hw) x) g‖ ≤ B := by
  classical

  obtain ⟨x', hx', α, hα, -, -, hxeq⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys x hx
  have hx'V : x' ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx').1).1
  obtain ⟨hx'cont, hx'sm⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
      K _ _ _ ξ x' (hV.1.le hx'V)
  have hx'cusp := (hx'sm 1).1
  rw [CoreSupplyC.rightTranslate_one'] at hx'cusp

  obtain ⟨γ, hγ, hfold⟩ := CoreSupplyC.exists_foldr_eq_rightConv K hw x' α hx'cont hα l
  obtain ⟨M, hM⟩ := AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc K c u d₁ d₂ T hd hcov ξ x'
    hx'cusp hx'cont γ hγ e₁ e₂ he₁
  refine ⟨M, fun g hg => ?_⟩
  rw [hxeq, hfold]
  exact hM g hg

end S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut (solution)
