-- Prove2me | solution 1 for AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/41ddae2c-4731-5b00-8bd6-95146f0712c6

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_AutomorphicForm_isClosed_adelicUnipotent
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
import Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_AutomorphicForm_lintegral_adelicGLHaar_eq_mul_lintegral_unipotentQuotientMeasure
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_valuation_eq_exp_neg_count
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_RepTheory_SmoothVectors
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_HaarQuotient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_AutomorphicForm_ClassSumGrowth_exists_forall_classBlock_le_and_classSum_le
import Theorems.Thm_AutomorphicForm_ClassSumGrowth_exists_forall_le_classSum_of_classCarriesMass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv"
p2m_attr_erase "simp" "LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal
open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace WindowMultiplicity

variable (K : Type) [Field K] [NumberField K]

private def unipotentShadow (W : Set (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K) :=
  {h | ∃ x : AdeleRing (𝓞 K) K, unipotentGL2 x * h ∈ W}

private def principalIdele (γ : Kˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom γ

private def windowWeight (W : Set (AdelicGL2 (𝓞 K) K)) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  ∑' γ : Kˣ, ∫⁻ z, (unipotentShadow K W).indicator 1
      (centralScalar (𝓞 K) K z * diagOne ((principalIdele K γ)⁻¹ * t) * k) * m z
    ∂(NumberField.Idele.idelicHaar K)

private def GoodIdeal (S : Finset (HeightOneSpectrum (𝓞 K))) : Type :=
  {𝔫 : Ideal (𝓞 K) // 𝔫 ≠ 0 ∧ ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔫}

private def GoodIdeal.cls {S : Finset (HeightOneSpectrum (𝓞 K))} (𝔫 : GoodIdeal K S) :
    ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨𝔫.1, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔫.2.1⟩

private def recValue (Ψ : HeckeEigensystem K ℂ) (𝔫 : Ideal (𝓞 K)) : ℂ :=
  open scoped Classical in
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
      (Ψ.toRawCentral.b v) ((Associates.mk v.asIdeal).count (Associates.mk 𝔫).factors)

private def massSeq (Ψ : HeckeEigensystem K ℂ) (e : ℝ) (𝔫 : Ideal (𝓞 K)) : ℝ≥0∞ :=
  (‖recValue K Ψ 𝔫‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((Ideal.absNorm 𝔫 : ℝ) ^ e)

private def classSum (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) (e : ℝ)
    (𝒞 : ClassGroup (𝓞 K)) (Y : ℝ) : ℝ≥0∞ :=
  ∑' 𝔫 : {𝔫 : GoodIdeal K S // GoodIdeal.cls K 𝔫 = 𝒞 ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ Y},
    massSeq K Ψ e 𝔫.1.1

private def classBlock (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) (e : ℝ)
    (𝒞 : ClassGroup (𝓞 K)) (Y : ℝ) : ℝ≥0∞ :=
  ∑' 𝔫 : {𝔫 : GoodIdeal K S //
      GoodIdeal.cls K 𝔫 = 𝒞 ∧ Y < (Ideal.absNorm 𝔫.1 : ℝ) ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y},
    massSeq K Ψ e 𝔫.1.1

private def ClassCarriesMass (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (𝒞 : ClassGroup (𝓞 K)) : Prop :=
  ∃ 𝔫 : GoodIdeal K S, GoodIdeal.cls K 𝔫 = 𝒞 ∧ recValue K Ψ 𝔫.1 ≠ 0

private def shadowWeight (E : Set (AdelicGL2 (𝓞 K) K)) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  ∑' γ : Kˣ, ∫⁻ z, E.indicator 1 (centralScalar (𝓞 K) K z * diagOne ((principalIdele K γ)⁻¹ * t) * k) * m z
    ∂(NumberField.Idele.idelicHaar K)

private theorem windowWeight_eq_shadowWeight (W : Set (AdelicGL2 (𝓞 K) K))
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    windowWeight K W m t k = shadowWeight K (unipotentShadow K W) m t k := rfl

private def idealIdele (𝔫 : Ideal (𝓞 K)) : (AdeleRing (𝓞 K) K)ˣ :=
  open scoped Classical in
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    uniformizerIdele K v ^ (Associates.mk v.asIdeal).count (Associates.mk 𝔫).factors

private def unitsOff (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 K) K)ˣ :=
  {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Valued.v ((t : AdeleRing (𝓞 K) K).2 v) = 1}

private def boxGenCount (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ) : ℝ≥0∞ :=
  ∑' γ : Kˣ,
    {γ : Kˣ | FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
      ∀ w : InfinitePlace K, w (γ : K) ≤ H w}.indicator 1 γ

private def boxGenCountBal (κ : ℝ) (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ) : ℝ≥0∞ :=
  ∑' γ : Kˣ,
    {γ : Kˣ | (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
        ∀ w : InfinitePlace K, w (γ : K) ≤ H w) ∧
      ∀ w w' : InfinitePlace K, H w * w' (γ : K) ≤ κ * (H w' * w (γ : K))}.indicator 1 γ

private theorem mem_unipotentShadow_image_mul_right_iff (E : Set (AdelicGL2 (𝓞 K) K))
    (x₀ h : AdelicGL2 (𝓞 K) K) :
    h ∈ unipotentShadow K ((· * x₀) '' E) ↔ h * x₀⁻¹ ∈ unipotentShadow K E := by
  simp only [unipotentShadow, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, y, hy, hyx⟩
    exact ⟨x, by rwa [← mul_assoc, ← hyx, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, unipotentGL2 x * (h * x₀⁻¹), hx, by rw [mul_assoc, inv_mul_cancel_right]⟩

private theorem windowWeight_image_mul_right (E : Set (AdelicGL2 (𝓞 K) K)) (x₀ : AdelicGL2 (𝓞 K) K)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    windowWeight K ((· * x₀) '' E) m t k = windowWeight K E m t (k * x₀⁻¹) := by
  have hset : unipotentShadow K ((· * x₀) '' E) = (fun h : AdelicGL2 (𝓞 K) K => h * x₀⁻¹) ⁻¹' unipotentShadow K E :=
    Set.ext fun h => mem_unipotentShadow_image_mul_right_iff K E x₀ h
  have hind : ∀ y : AdelicGL2 (𝓞 K) K, (unipotentShadow K ((· * x₀) '' E)).indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) y =
      (unipotentShadow K E).indicator 1 (y * x₀⁻¹) := fun y => by
    rw [hset]
    exact Set.indicator_comp_right (g := (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞)) fun h : AdelicGL2 (𝓞 K) K => h * x₀⁻¹
  unfold windowWeight
  refine tsum_congr fun γ => lintegral_congr fun z => ?_
  rw [hind, mul_assoc _ k x₀⁻¹]

section UnipotentWindowEntries

open NumberField.AdelicVolume

variable {K}

private theorem glArch_unipotentGL2_adeleArch (x : AdeleRing (𝓞 K) K) :
    AdelicLevel.glArch (𝓞 K) K (unipotentGL2 x) = unipotentGL2 (AdelicLevel.adeleArch (𝓞 K) K x) :=
  Units.ext (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl)

private theorem glFin_unipotentGL2_adeleFin (x : AdeleRing (𝓞 K) K) :
    AdelicLevel.glFin (𝓞 K) K (unipotentGL2 x) = unipotentGL2 (AdelicLevel.adeleFin (𝓞 K) K x) :=
  Units.ext (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl)

omit [NumberField K] in
private theorem archComponent_unipotentGL2 (w : InfinitePlace K) (z : InfiniteAdeleRing K) :
    AdelicLevel.archComponent K w (unipotentGL2 z) = unipotentGL2 (AdelicLevel.archEval K w z) :=
  Units.ext (Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl)

private theorem unipotentGL2_inv {R : Type*} [CommRing R] (x : R) :
    (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

omit [NumberField K] in

private theorem xWindowSq_unipotentGL2_mul (w : InfinitePlace K) (y : w.Completion)
    (g : GL (Fin 2) w.Completion) :
    xWindowSq (unipotentGL2 y * g) =
      ‖SiegelCoordinates.xCoord ((g : Matrix (Fin 2) (Fin 2) w.Completion).map
          (InfinitePlace.Completion.extensionEmbedding w)) +
        InfinitePlace.Completion.extensionEmbedding w y‖ ^ 2 := by
  set φ := InfinitePlace.Completion.extensionEmbedding w
  have hφ : ∀ t, ‖φ t‖ = ‖t‖ := SiegelCoordinates.norm_extensionEmbedding w
  rw [SiegelCoordinates.xWindowSq_eq_norm_xCoord_map_sq φ hφ,
    ← SiegelCoordinates.coe_map φ (unipotentGL2 y * g), map_mul,
    SiegelCoordinates.xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ (unipotentGL2 y))
      (a := 1) (b := φ y) (t := 1) one_ne_zero
      (by simp) (by simp)
      (by simp) (by simp)]
  simp

private theorem archComponent_glArch_unipotentGL2_mul (w : InfinitePlace K) (x : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) :
    AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K (unipotentGL2 x * g)) =
      unipotentGL2 (AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K x)) *
        AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g) := by
  rw [map_mul, glArch_unipotentGL2_adeleArch, map_mul, archComponent_unipotentGL2]

private theorem glFin_unipotentGL2_mul (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    AdelicLevel.glFin (𝓞 K) K (unipotentGL2 x * g) =
      unipotentGL2 (AdelicLevel.adeleFin (𝓞 K) K x) * AdelicLevel.glFin (𝓞 K) K g := by
  rw [map_mul, glFin_unipotentGL2_adeleFin]

omit [NumberField K] in
private theorem localHeight_unipotentGL2_mul (w : InfinitePlace K) (y : w.Completion)
    (g : GL (Fin 2) w.Completion) : localHeight (unipotentGL2 y * g) = localHeight g := by
  rw [SiegelCoordinates.localHeight_upper_entries_mul (s := unipotentGL2 y) (a := 1) (t := 1) one_ne_zero
    (by simp) (by simp) (by simp)]
  simp

private theorem archDetNorm_unipotentGL2_mul (w : InfinitePlace K) (x : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) : archDetNorm w (unipotentGL2 x * g) = archDetNorm w g := by
  unfold archDetNorm
  rw [archComponent_glArch_unipotentGL2_mul, Units.val_mul, Matrix.det_mul, unipotentGL2_coe,
    Matrix.det_fin_two_of]
  simp

end UnipotentWindowEntries

section Central

open NumberField.AdelicVolume

variable {K}

private theorem fst_apply_ne_zero (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ((z : AdeleRing (𝓞 K) K).1 w) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (a := (z : AdeleRing (𝓞 K) K).1 w) (b := ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K).1 w) (by
      have h := congrArg (fun a : AdeleRing (𝓞 K) K => a.1 w) z.mul_inv
      exact h)

private theorem archComponent_glArch_centralScalar_apply (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K)
    (i j : Fin 2) :
    ((archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K z)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then (z : AdeleRing (𝓞 K) K).1 w else 0 := by
  simp only [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

private theorem glFin_centralScalar_apply (z : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((glFin (𝓞 K) K (centralScalar (𝓞 K) K z) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
      = if i = j then (z : AdeleRing (𝓞 K) K).2 else 0 := by
  rw [glFin_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

private theorem localHeight_centralScalar_mul (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K)
    (g : AdelicGL2 (𝓞 K) K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K z * g)))
      = localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [map_mul, map_mul]
  rw [localHeight_scalar_entries_mul (fst_apply_ne_zero z w)
    (by rw [archComponent_glArch_centralScalar_apply, if_pos rfl])
    (by rw [archComponent_glArch_centralScalar_apply, if_neg (by decide)])
    (by rw [archComponent_glArch_centralScalar_apply, if_neg (by decide)])
    (by rw [archComponent_glArch_centralScalar_apply, if_pos rfl])]

private theorem archDetNorm_centralScalar_mul' (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K)
    (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (centralScalar (𝓞 K) K z * g)
      = ‖(z : AdeleRing (𝓞 K) K).1 w‖ ^ 2 * archDetNorm w g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul, sq]
  congr 1
  rw [Matrix.det_fin_two, archComponent_glArch_centralScalar_apply, archComponent_glArch_centralScalar_apply,
    archComponent_glArch_centralScalar_apply, archComponent_glArch_centralScalar_apply]
  simp [norm_mul]

private theorem localHeight_fibre (x : AdeleRing (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K)
    (h : AdelicGL2 (𝓞 K) K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (unipotentGL2 x * (centralScalar (𝓞 K) K z * h))))
      = localHeight (archComponent K w (glArch (𝓞 K) K h)) := by
  rw [archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul, localHeight_centralScalar_mul]

private theorem archDetNorm_fibre (x : AdeleRing (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K)
    (h : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (unipotentGL2 x * (centralScalar (𝓞 K) K z * h))
      = ‖(z : AdeleRing (𝓞 K) K).1 w‖ ^ 2 * archDetNorm w h := by
  rw [archDetNorm_unipotentGL2_mul, archDetNorm_centralScalar_mul']

private theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_val, ← Matrix.smul_eq_diagonal_mul, ← Matrix.smul_eq_mul_diagonal]

end Central

section Finite

variable {K}

private theorem centralScalar_mem_finiteIntegralGL2 {z : (AdeleRing (𝓞 K) K)ˣ}
    (hz : NumberField.AdeleRing.finitePartUnits (𝓞 K) K z ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K) :
    glFin (𝓞 K) K (centralScalar (𝓞 K) K z) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_centralScalar_apply]
    split_ifs
    · exact fun v => hz.1 v
    · exact fun v => zero_mem _
  · rw [← map_inv, ← map_inv, glFin_centralScalar_apply]
    split_ifs
    · exact fun v => by first | exact hz.2 v | simpa using hz.2 v
    · exact fun v => zero_mem _

private theorem snd_mul_inv_mem_integralFiniteAdeles {x x₀ : AdeleRing (𝓞 K) K}
    {z z₀ : (AdeleRing (𝓞 K) K)ˣ} {h : AdelicGL2 (𝓞 K) K}
    (hP : glFin (𝓞 K) K (unipotentGL2 x * (centralScalar (𝓞 K) K z * h)) ∈ finiteIntegralGL2 (𝓞 K) K)
    (hP₀ : glFin (𝓞 K) K (unipotentGL2 x₀ * (centralScalar (𝓞 K) K z₀ * h)) ∈ finiteIntegralGL2 (𝓞 K) K) :
    ((z * z₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hQ := (finiteIntegralGL2 (𝓞 K) K).mul_mem hP ((finiteIntegralGL2 (𝓞 K) K).inv_mem hP₀)
  have hprod : unipotentGL2 x * (centralScalar (𝓞 K) K z * h) *
      (unipotentGL2 x₀ * (centralScalar (𝓞 K) K z₀ * h))⁻¹
        = unipotentGL2 x * centralScalar (𝓞 K) K (z * z₀⁻¹) * (unipotentGL2 x₀)⁻¹ := by
    rw [map_mul, map_inv]
    group
  rw [← map_inv, ← map_mul, hprod, map_mul, map_mul, map_inv, glFin_unipotentGL2_adeleFin, glFin_unipotentGL2_adeleFin,
    unipotentGL2_inv] at hQ
  have h00 := (mem_finiteIntegralGL2_iff.1 hQ).1 0 0
  have hentry : ((unipotentGL2 (adeleFin (𝓞 K) K x) * glFin (𝓞 K) K (centralScalar (𝓞 K) K (z * z₀⁻¹)) *
      unipotentGL2 (-adeleFin (𝓞 K) K x₀) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 0 0
      = ((z * z₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, unipotentGL2_coe, glFin_centralScalar_apply,
      glFin_centralScalar_apply, glFin_centralScalar_apply, glFin_centralScalar_apply]
    simp
  rwa [hentry] at h00

private theorem finitePartUnits_mul_inv_mem_unitIdeles {x x₀ : AdeleRing (𝓞 K) K}
    {z z₀ : (AdeleRing (𝓞 K) K)ˣ} {h : AdelicGL2 (𝓞 K) K}
    (hP : glFin (𝓞 K) K (unipotentGL2 x * (centralScalar (𝓞 K) K z * h)) ∈ finiteIntegralGL2 (𝓞 K) K)
    (hP₀ : glFin (𝓞 K) K (unipotentGL2 x₀ * (centralScalar (𝓞 K) K z₀ * h)) ∈ finiteIntegralGL2 (𝓞 K) K) :
    NumberField.AdeleRing.finitePartUnits (𝓞 K) K (z * z₀⁻¹) ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have h1 := snd_mul_inv_mem_integralFiniteAdeles hP hP₀
    rw [NumberField.AdeleRing.val_finitePartUnits]
    exact h1 v
  · have h2 := snd_mul_inv_mem_integralFiniteAdeles hP₀ hP
    rw [← map_inv, NumberField.AdeleRing.val_finitePartUnits]
    have : ((z * z₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) = z₀ * z⁻¹ := by
      rw [_root_.mul_inv_rev, inv_inv]
    rw [this]
    exact h2 v

end Finite

section PlaceEmbedding

open AutomorphicForm.SiegelCoordinates

variable {K}

open scoped Classical in

private noncomputable def placeEmb (w : InfinitePlace K) : w.Completion →+* ℂ :=
  if hw : w.IsReal then Complex.ofRealHom.comp (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)
  else InfinitePlace.Completion.extensionEmbedding w
omit [NumberField K] in
private theorem norm_placeEmb (w : InfinitePlace K) (x : w.Completion) : ‖placeEmb w x‖ = ‖x‖ := by
  unfold placeEmb
  split_ifs with hw
  · rw [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

private noncomputable def xAtP (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  xCoord (((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) w.Completion).map (placeEmb w))
private theorem xWindowSq_eq_norm_xAtP_sq (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    xWindowSq (archComponent K w (glArch (𝓞 K) K g)) = ‖xAtP w g‖ ^ 2 :=
  xWindowSq_eq_norm_xCoord_map_sq (placeEmb w) (norm_placeEmb w) _

private theorem exists_placeEmb_eq_xAtP (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    ∃ x : w.Completion, placeEmb w x = xAtP w g := by
  by_cases hw : w.IsReal
  ·
    have hsurj : Function.Surjective (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw).surjective
    have hreal : ∀ z : w.Completion,
        placeEmb w z = ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hw z : ℝ) : ℂ) := by
      intro z; simp only [placeEmb, dif_pos hw, RingHom.comp_apply, Complex.ofRealHom_eq_coe]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = xAtP w g := by
      refine ⟨(xAtP w g).re, ?_⟩
      unfold xAtP xCoord
      simp only [hreal, Matrix.map_apply]
      apply Complex.ext <;>
        simp [Complex.ofReal_re, Complex.ofReal_im, -InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    obtain ⟨x, hx⟩ := hsurj r
    exact ⟨x, by rw [hreal, hx, hr]⟩
  · have hsurj : Function.Surjective (InfinitePlace.Completion.extensionEmbedding w) :=
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    obtain ⟨x, hx⟩ := hsurj (xAtP w g)
    exact ⟨x, by simp only [placeEmb, dif_neg hw]; exact hx⟩

end PlaceEmbedding

section Separation

open NumberField.AdelicVolume AutomorphicForm.SiegelCoordinates

variable {K}

omit [NumberField K] in

private theorem xWindowSq_unipotentGL2_mul_placeEmb (w : InfinitePlace K) (y : w.Completion)
    (g : GL (Fin 2) w.Completion) :
    xWindowSq (unipotentGL2 y * g) =
      ‖xCoord ((g : Matrix (Fin 2) (Fin 2) w.Completion).map (placeEmb w)) + placeEmb w y‖ ^ 2 := by
  rw [xWindowSq_eq_norm_xCoord_map_sq (placeEmb w) (norm_placeEmb w), ← coe_map, map_mul,
    xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map (placeEmb w) (unipotentGL2 y))
      (a := 1) (b := placeEmb w y) (t := 1) one_ne_zero (by simp) (by simp) (by simp) (by simp)]
  simp

private theorem exists_forall_xWindowSq_eq_zero (g : AdelicGL2 (𝓞 K) K) (xf : FiniteAdeleRing (𝓞 K) K) :
    ∃ x : AdeleRing (𝓞 K) K, adeleFin (𝓞 K) K x = xf ∧
      ∀ w : InfinitePlace K, xWindowSq (archComponent K w (glArch (𝓞 K) K (unipotentGL2 x * g))) = 0 := by
  choose y hy using fun w : InfinitePlace K => exists_placeEmb_eq_xAtP w g
  refine ⟨((fun w => -y w : InfiniteAdeleRing K), xf), rfl, fun w => ?_⟩
  rw [archComponent_glArch_unipotentGL2_mul, xWindowSq_unipotentGL2_mul_placeEmb]
  have h : archEval K w (adeleArch (𝓞 K) K ((fun w => -y w : InfiniteAdeleRing K), xf)) = -y w := rfl
  rw [h, map_neg, hy w]
  simp [xAtP]

private theorem glFin_unipotentGL2_mul_congr {x x' : AdeleRing (𝓞 K) K}
    (hx : adeleFin (𝓞 K) K x = adeleFin (𝓞 K) K x') (g : AdelicGL2 (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 x * g) = glFin (𝓞 K) K (unipotentGL2 x' * g) := by
  rw [glFin_unipotentGL2_mul, glFin_unipotentGL2_mul, hx]

private theorem centralScalar_mul_mem_unipotentShadow_iff (c u d₁ d₂ : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * h ∈ unipotentShadow K (centreCutSiegelSet K c u d₁ d₂) ↔
      (∃ x : AdeleRing (𝓞 K) K,
          glFin (𝓞 K) K (unipotentGL2 x * (centralScalar (𝓞 K) K z * h)) ∈ finiteIntegralGL2 (𝓞 K) K) ∧
        (∀ w : InfinitePlace K, c ≤ localHeight (archComponent K w (glArch (𝓞 K) K h))) ∧
        ∀ w : InfinitePlace K, ‖(z : AdeleRing (𝓞 K) K).1 w‖ ^ 2 * archDetNorm w h ∈ Set.Icc d₁ d₂ := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_centreCutSiegelSet_iff] at hx
    obtain ⟨hfin, hht, -, hdet⟩ := hx
    refine ⟨⟨x, hfin⟩, fun w => ?_, fun w => ?_⟩
    · have := hht w
      rwa [localHeight_fibre] at this
    · have := hdet w
      rwa [archDetNorm_fibre] at this
  · rintro ⟨⟨x₀, hx₀⟩, hht, hdet⟩
    obtain ⟨x, hxf, hxw⟩ :=
      exists_forall_xWindowSq_eq_zero (centralScalar (𝓞 K) K z * h) (adeleFin (𝓞 K) K x₀)
    refine ⟨x, ?_⟩
    rw [mem_centreCutSiegelSet_iff]
    refine ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rwa [glFin_unipotentGL2_mul_congr hxf]
    · rw [localHeight_fibre]; exact hht w
    · rw [hxw w]; exact sq_nonneg u
    · rw [archDetNorm_fibre]; exact hdet w

private theorem centralScalar_mul_mem_unipotentShadow_ample_iff (c u d₁ d₂ κ : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * h ∈ unipotentShadow K (centreCutSiegelSetAmple K c u d₁ d₂ κ) ↔
      (centralScalar (𝓞 K) K z * h ∈ unipotentShadow K (centreCutSiegelSet K c u d₁ d₂)) ∧
        ∀ w w' : InfinitePlace K,
          localHeight (archComponent K w (glArch (𝓞 K) K h)) ≤
            κ * localHeight (archComponent K w' (glArch (𝓞 K) K h)) := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_centreCutSiegelSetAmple_iff] at hx
    refine ⟨⟨x, hx.1⟩, fun w w' => ?_⟩
    have := hx.2 w w'
    rwa [localHeight_fibre, localHeight_fibre] at this
  · rintro ⟨⟨x, hx⟩, hbal⟩
    refine ⟨x, ?_⟩
    rw [mem_centreCutSiegelSetAmple_iff]
    refine ⟨hx, fun w w' => ?_⟩
    rw [localHeight_fibre, localHeight_fibre]
    exact hbal w w'

private theorem exists_glFin_mem_iff_of_mem {x₀ : AdeleRing (𝓞 K) K} {z₀ : (AdeleRing (𝓞 K) K)ˣ}
    {h : AdelicGL2 (𝓞 K) K}
    (hP₀ : glFin (𝓞 K) K (unipotentGL2 x₀ * (centralScalar (𝓞 K) K z₀ * h)) ∈ finiteIntegralGL2 (𝓞 K) K)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    (∃ x : AdeleRing (𝓞 K) K,
        glFin (𝓞 K) K (unipotentGL2 x * (centralScalar (𝓞 K) K z * h)) ∈ finiteIntegralGL2 (𝓞 K) K) ↔
      NumberField.AdeleRing.finitePartUnits (𝓞 K) K (z * z₀⁻¹) ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  constructor
  · rintro ⟨x, hx⟩
    exact finitePartUnits_mul_inv_mem_unitIdeles hx hP₀
  · intro hz
    refine ⟨x₀, ?_⟩
    have hsplit : unipotentGL2 x₀ * (centralScalar (𝓞 K) K z * h)
        = centralScalar (𝓞 K) K (z * z₀⁻¹) * (unipotentGL2 x₀ * (centralScalar (𝓞 K) K z₀ * h)) := by
      have hc₁ : Commute (centralScalar (𝓞 K) K z) (unipotentGL2 x₀) := centralScalar_mul_comm z (unipotentGL2 x₀)
      have hc₂ : Commute (centralScalar (𝓞 K) K z₀) (unipotentGL2 x₀) := centralScalar_mul_comm z₀ (unipotentGL2 x₀)
      have hc : Commute (centralScalar (𝓞 K) K z * (centralScalar (𝓞 K) K z₀)⁻¹) (unipotentGL2 x₀) :=
        hc₁.mul_left hc₂.inv_left
      rw [map_mul, map_inv]
      calc unipotentGL2 x₀ * (centralScalar (𝓞 K) K z * h)
          = unipotentGL2 x₀ * (centralScalar (𝓞 K) K z * (centralScalar (𝓞 K) K z₀)⁻¹ *
              (centralScalar (𝓞 K) K z₀ * h)) := by
            rw [mul_assoc (centralScalar (𝓞 K) K z), inv_mul_cancel_left]
        _ = _ := by rw [← mul_assoc, ← hc.eq, mul_assoc]
    rw [hsplit, map_mul]
    exact (finiteIntegralGL2 (𝓞 K) K).mul_mem (centralScalar_mem_finiteIntegralGL2 hz) hP₀

end Separation

section Shadows

open NumberField.AdelicVolume

variable {K}

private theorem mem_unipotentShadow_centreCutSiegelSet_iff (c u d₁ d₂ : ℝ) (h : AdelicGL2 (𝓞 K) K) :
    h ∈ unipotentShadow K (centreCutSiegelSet K c u d₁ d₂) ↔
      (∃ x : AdeleRing (𝓞 K) K, glFin (𝓞 K) K (unipotentGL2 x * h) ∈ finiteIntegralGL2 (𝓞 K) K) ∧
        (∀ w : InfinitePlace K, c ≤ localHeight (archComponent K w (glArch (𝓞 K) K h))) ∧
        ∀ w : InfinitePlace K, archDetNorm w h ∈ Set.Icc d₁ d₂ := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_centreCutSiegelSet_iff] at hx
    obtain ⟨hfin, hht, -, hdet⟩ := hx
    refine ⟨⟨x, hfin⟩, fun w => ?_, fun w => ?_⟩
    · have := hht w
      rwa [archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul] at this
    · have := hdet w
      rwa [archDetNorm_unipotentGL2_mul] at this
  · rintro ⟨⟨x₀, hx₀⟩, hht, hdet⟩
    obtain ⟨x, hxf, hxw⟩ := exists_forall_xWindowSq_eq_zero h (adeleFin (𝓞 K) K x₀)
    refine ⟨x, ?_⟩
    rw [mem_centreCutSiegelSet_iff]
    refine ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rwa [glFin_unipotentGL2_mul_congr hxf]
    · rw [archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul]
      exact hht w
    · rw [hxw w]
      exact sq_nonneg u
    · rw [archDetNorm_unipotentGL2_mul]
      exact hdet w

private theorem mem_unipotentShadow_centreCutSiegelSetAmple_iff (c u d₁ d₂ κ : ℝ) (h : AdelicGL2 (𝓞 K) K) :
    h ∈ unipotentShadow K (centreCutSiegelSetAmple K c u d₁ d₂ κ) ↔
      h ∈ unipotentShadow K (centreCutSiegelSet K c u d₁ d₂) ∧
        ∀ w w' : InfinitePlace K,
          localHeight (archComponent K w (glArch (𝓞 K) K h)) ≤
            κ * localHeight (archComponent K w' (glArch (𝓞 K) K h)) := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_centreCutSiegelSetAmple_iff] at hx
    refine ⟨⟨x, hx.1⟩, fun w w' => ?_⟩
    have := hx.2 w w'
    rwa [archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul,
      archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul] at this
  · rintro ⟨⟨x, hx⟩, hbal⟩
    refine ⟨x, ?_⟩
    rw [mem_centreCutSiegelSetAmple_iff]
    refine ⟨hx, fun w w' => ?_⟩
    rw [archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul,
      archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul]
    exact hbal w w'

private theorem isOpen_finiteIntegralGL2' :
    IsOpen (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  have hset : (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) =
      (⋂ i : Fin 2, ⋂ j : Fin 2, {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) |
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
            ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K}) ∩
        ⋂ i : Fin 2, ⋂ j : Fin 2, {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) |
          ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
            ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K} := by
    ext g
    simp only [SetLike.mem_coe, mem_finiteIntegralGL2_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
      NumberField.AdelicLevel.integralFiniteAdeles]
  rw [hset]
  refine (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact (NumberField.AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K).preimage (Units.continuous_val.matrix_elem i j)
  · exact (NumberField.AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K).preimage
      (Units.continuous_coe_inv.matrix_elem i j)

private theorem measurableSet_setOf_exists_glFin_unipotentGL2_mul_mem :
    MeasurableSet {h : AdelicGL2 (𝓞 K) K |
      ∃ x : AdeleRing (𝓞 K) K, glFin (𝓞 K) K (unipotentGL2 x * h) ∈ finiteIntegralGL2 (𝓞 K) K} := by
  have hset : {h : AdelicGL2 (𝓞 K) K |
        ∃ x : AdeleRing (𝓞 K) K, glFin (𝓞 K) K (unipotentGL2 x * h) ∈ finiteIntegralGL2 (𝓞 K) K}
      = glFin (𝓞 K) K ⁻¹' ⋃ y : FiniteAdeleRing (𝓞 K) K,
          (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => unipotentGL2 y * g) ⁻¹'
            (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, glFin_unipotentGL2_mul]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨adeleFin (𝓞 K) K x, hx⟩
    · rintro ⟨y, hy⟩
      exact ⟨((0 : InfiniteAdeleRing K), y), hy⟩
  rw [hset]
  exact ((continuous_glFin (𝓞 K) K).isOpen_preimage _
    (isOpen_iUnion fun y => isOpen_finiteIntegralGL2'.preimage (continuous_const_mul _))).measurableSet

private theorem measurableSet_unipotentShadow_centreCutSiegelSet (c u d₁ d₂ : ℝ) :
    MeasurableSet (unipotentShadow K (centreCutSiegelSet K c u d₁ d₂)) := by
  have hset : unipotentShadow K (centreCutSiegelSet K c u d₁ d₂) =
      {h : AdelicGL2 (𝓞 K) K |
          ∃ x : AdeleRing (𝓞 K) K, glFin (𝓞 K) K (unipotentGL2 x * h) ∈ finiteIntegralGL2 (𝓞 K) K} ∩
        ((⋂ w : InfinitePlace K, {h : AdelicGL2 (𝓞 K) K | c ≤ localHeight (archComponent K w (glArch (𝓞 K) K h))}) ∩
          ⋂ w : InfinitePlace K, {h : AdelicGL2 (𝓞 K) K | archDetNorm w h ∈ Set.Icc d₁ d₂}) := by
    ext h
    simp only [mem_unipotentShadow_centreCutSiegelSet_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine measurableSet_setOf_exists_glFin_unipotentGL2_mul_mem.inter (MeasurableSet.inter ?_ ?_)
  · exact MeasurableSet.iInter fun w =>
      (isClosed_le continuous_const (continuous_localHeight_place w)).measurableSet
  · exact MeasurableSet.iInter fun w => (isClosed_Icc.preimage (continuous_archDetNorm w)).measurableSet

private theorem measurableSet_unipotentShadow_centreCutSiegelSetAmple (c u d₁ d₂ κ : ℝ) :
    MeasurableSet (unipotentShadow K (centreCutSiegelSetAmple K c u d₁ d₂ κ)) := by
  have hset : unipotentShadow K (centreCutSiegelSetAmple K c u d₁ d₂ κ) =
      unipotentShadow K (centreCutSiegelSet K c u d₁ d₂) ∩
        ⋂ w : InfinitePlace K, ⋂ w' : InfinitePlace K, {h : AdelicGL2 (𝓞 K) K |
          localHeight (archComponent K w (glArch (𝓞 K) K h)) ≤
            κ * localHeight (archComponent K w' (glArch (𝓞 K) K h))} := by
    ext h
    simp only [mem_unipotentShadow_centreCutSiegelSetAmple_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  exact (measurableSet_unipotentShadow_centreCutSiegelSet c u d₁ d₂).inter
    (MeasurableSet.iInter fun w => MeasurableSet.iInter fun w' =>
      (isClosed_setOf_localHeight_le_mul κ w w').measurableSet)

end Shadows

private theorem measurableSet_unipotentShadow_image_centreCutSiegelSet (c u d₁ d₂ : ℝ)
    (x₀ : AdelicGL2 (𝓞 K) K) :
    MeasurableSet (unipotentShadow K ((· * x₀) '' centreCutSiegelSet K c u d₁ d₂)) := by
  rw [show unipotentShadow K ((· * x₀) '' centreCutSiegelSet K c u d₁ d₂)
      = (fun h => h * x₀⁻¹) ⁻¹' unipotentShadow K (centreCutSiegelSet K c u d₁ d₂) from
    Set.ext fun h => mem_unipotentShadow_image_mul_right_iff K _ x₀ h]
  exact (continuous_mul_const x₀⁻¹).measurable (measurableSet_unipotentShadow_centreCutSiegelSet c u d₁ d₂)

private theorem measurableSet_unipotentShadow_image_centreCutSiegelSetAmple (c u d₁ d₂ κ : ℝ)
    (x₀ : AdelicGL2 (𝓞 K) K) :
    MeasurableSet (unipotentShadow K ((· * x₀) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)) := by
  rw [show unipotentShadow K ((· * x₀) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
      = (fun h => h * x₀⁻¹) ⁻¹' unipotentShadow K (centreCutSiegelSetAmple K c u d₁ d₂ κ) from
    Set.ext fun h => mem_unipotentShadow_image_mul_right_iff K _ x₀ h]
  exact (continuous_mul_const x₀⁻¹).measurable
    (measurableSet_unipotentShadow_centreCutSiegelSetAmple c u d₁ d₂ κ)

section PeriodParseval

open scoped ComplexConjugate
open MeasureTheory Finset

section Abstract

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

private theorem norm_sub_sum_inner_smul_sq {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) (s : Finset ι) :
    ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 := by
  have h₂ : (∑ i ∈ s, ∑ j ∈ s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫)
      = (∑ k ∈ s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) := by
    classical exact hv.inner_left_right_finset
  have h₃ : ∀ z : 𝕜, RCLike.re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [RCLike.mul_conj]
    norm_cast
  rw [@norm_sub_sq 𝕜, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, h₂,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]

private theorem norm_sub_sum_inner_smul_le {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) (s : Finset ι)
    (c : ι → 𝕜) :
    ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ≤ ‖x - ∑ i ∈ s, c i • v i‖ := by
  classical
  set P : E := ∑ i ∈ s, ⟪v i, x⟫ • v i with hP
  set y : E := ∑ i ∈ s, c i • v i with hy

  have horth : ∀ j ∈ s, ⟪v j, x - P⟫ = 0 := by
    intro j hj
    have hite := orthonormal_iff_ite.mp hv
    rw [inner_sub_right, hP, inner_sum]
    simp [inner_smul_right, hite, hj]

  have horth' : ⟪P - y, x - P⟫ = 0 := by
    rw [hP, hy, ← Finset.sum_sub_distrib]
    rw [sum_inner]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← sub_smul, inner_smul_left, horth j hj, mul_zero]
  have hdecomp : x - y = (P - y) + (x - P) := by abel
  have hpyth : ‖x - y‖ ^ 2 = ‖x - P‖ ^ 2 + ‖P - y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (P - y) (x - P) horth'
    rw [hdecomp, sq, sq, sq, h]
    ring
  have h1 : ‖x - P‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [hpyth]; exact le_add_of_nonneg_right (by positivity)
  exact le_of_sq_le_sq (by simpa using h1) (norm_nonneg _)

private theorem norm_sq_le_tsum_inner_sq_of_forall_exists_sum_norm_sub_lt {v : ι → E}
    (hv : Orthonormal 𝕜 v) (x : E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ι) (c : ι → 𝕜), ‖x - ∑ i ∈ s, c i • v i‖ < ε) :
    ‖x‖ ^ 2 ≤ ∑' i, ‖⟪v i, x⟫‖ ^ 2 := by
  have hsumm : Summable fun i => ‖⟪v i, x⟫‖ ^ 2 := hv.inner_products_summable x

  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨s, c, hsc⟩ := happrox (Real.sqrt δ) (Real.sqrt_pos.mpr hδ)
  have hmin := norm_sub_sum_inner_smul_le hv x s c
  have hid := norm_sub_sum_inner_smul_sq hv x s
  have hpart : ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 ≤ ∑' i, ‖⟪v i, x⟫‖ ^ 2 :=
    hsumm.sum_le_tsum s (fun i _ => by positivity)
  have hlt : ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ^ 2 < δ := by
    have h0 : 0 ≤ ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ := norm_nonneg _
    have h1 : ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ < Real.sqrt δ := lt_of_le_of_lt hmin hsc
    calc ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ^ 2
        < Real.sqrt δ ^ 2 := by gcongr
      _ = δ := Real.sq_sqrt hδ.le

  have hx : ‖x‖ ^ 2 = ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ^ 2 + ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 := by
    rw [hid]; ring
  rw [hx]
  linarith

end Abstract

section Integral

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

private theorem memLp_two_of_bound {g : X → ℂ} (hg : AEStronglyMeasurable g μ) (C : ℝ)
    (hC : ∀ x, ‖g x‖ ≤ C) : MemLp g 2 μ :=
  MemLp.of_bound hg C (Filter.Eventually.of_forall hC)

private theorem integral_norm_sq_le_tsum_norm_integral_conj_mul_sq
    (e : ι → X → ℂ) (he : ∀ i, AEStronglyMeasurable (e i) μ) (heb : ∀ i x, ‖e i x‖ ≤ 1)
    (horth₁ : ∀ i, ∫ x, conj (e i x) * e i x ∂μ = 1)
    (horth₀ : ∀ i j, i ≠ j → ∫ x, conj (e i x) * e j x ∂μ = 0)
    (f : X → ℂ) (hf : AEStronglyMeasurable f μ) (M : ℝ) (hfM : ∀ x, ‖f x‖ ≤ M)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ι) (c : ι → ℂ),
      ∀ x, ‖f x - ∑ i ∈ s, c i * e i x‖ ≤ ε) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ ∑' i, ‖∫ x, conj (e i x) * f x ∂μ‖ ^ 2 := by
  classical
  have heL : ∀ i, MemLp (e i) 2 μ := fun i => memLp_two_of_bound (he i) 1 (heb i)
  have hfL : MemLp f 2 μ := memLp_two_of_bound hf M hfM
  set v : ι → Lp ℂ 2 μ := fun i => (heL i).toLp (e i) with hv_def
  set xL : Lp ℂ 2 μ := hfL.toLp f with hx_def

  have hinner : ∀ i, inner ℂ (v i) xL = ∫ y, conj (e i y) * f y ∂μ := by
    intro i
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(heL i).coeFn_toLp, hfL.coeFn_toLp] with y hy₁ hy₂
    rw [hy₁, hy₂]
    simp [RCLike.inner_apply, mul_comm]
  have hvint : ∀ i j, inner ℂ (v i) (v j) = ∫ y, conj (e i y) * e j y ∂μ := by
    intro i j
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(heL i).coeFn_toLp, (heL j).coeFn_toLp] with y hy₁ hy₂
    rw [hy₁, hy₂]
    simp [RCLike.inner_apply, mul_comm]
  have hvon : Orthonormal ℂ v := by
    refine orthonormal_iff_ite.mpr fun i j => ?_
    rw [hvint]
    by_cases hij : i = j
    · subst hij
      simp [horth₁ i]
    · simp [hij, horth₀ i j hij]

  have hxnorm : ‖xL‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂μ := by
    rw [← @inner_self_eq_norm_sq ℂ, MeasureTheory.L2.inner_def]
    have hint : Integrable (fun y => inner ℂ (xL y) (xL y)) μ :=
      MeasureTheory.L2.integrable_inner xL xL
    rw [← integral_re hint]
    refine integral_congr_ae ?_
    filter_upwards [hfL.coeFn_toLp] with y hy
    rw [hy]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]

  have happL : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ι) (c : ι → ℂ), ‖xL - ∑ i ∈ s, c i • v i‖ < ε := by
    intro ε hε
    obtain ⟨s, c, hsc⟩ := happrox (ε / 2) (by positivity)
    refine ⟨s, c, ?_⟩
    have hae : ∀ᵐ y ∂μ, ‖(xL - ∑ i ∈ s, c i • v i : Lp ℂ 2 μ) y‖ ≤ ε / 2 := by
      have h₁ := MeasureTheory.Lp.coeFn_sub xL (∑ i ∈ s, c i • v i)
      have h₂ : ∀ t : Finset ι,
          ∀ᵐ y ∂μ, (∑ i ∈ t, c i • v i : Lp ℂ 2 μ) y = ∑ i ∈ t, c i * e i y := by
        intro t
        refine Finset.induction_on t ?_ ?_
        · simp only [Finset.sum_empty]
          filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with y _
          simp
        · intro a t hat ih
          simp only [Finset.sum_insert hat]
          filter_upwards [MeasureTheory.Lp.coeFn_add (c a • v a) (∑ i ∈ t, c i • v i),
            MeasureTheory.Lp.coeFn_smul (c a) (v a), (heL a).coeFn_toLp, ih] with y hy₁ hy₂ hy₃ hy₄
          rw [hy₁, Pi.add_apply, hy₂, Pi.smul_apply, hy₃, hy₄, smul_eq_mul]
      filter_upwards [h₁, h₂ s, hfL.coeFn_toLp] with y hy₁ hy₂ hy₃
      rw [hy₁, Pi.sub_apply, hy₂, hy₃]
      exact hsc y
    have hle := MeasureTheory.Lp.norm_le_of_ae_bound (by positivity) hae
    have hmeas : (MeasureTheory.measureUnivNNReal μ : ℝ) = 1 := by
      simp [MeasureTheory.measureUnivNNReal]
    rw [hmeas, Real.one_rpow, one_mul] at hle
    linarith
  rw [← hxnorm]
  simp_rw [← hinner]
  exact norm_sq_le_tsum_inner_sq_of_forall_exists_sum_norm_sub_lt hvon xL happL

end Integral

section Adelic

open NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

variable {F}

private scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine Function.Surjective.countable
    (f := fun a : F => (⟨algebraMap F 𝔸 a, RingHom.mem_range.mpr ⟨a, rfl⟩⟩ :
      AdeleRing.principalSubgroup (𝓞 F) F)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hx
  exact ⟨a, rfl⟩

private def principalChar (ψ : AddChar 𝔸 ℂ) (γ : F) : 𝔸 → ℂ :=
  fun x => ψ (algebraMap F 𝔸 γ * x)

private abbrev PrincipalInvariant (f : 𝔸 → ℂ) : Prop :=
  ∀ (ξ : AdeleRing.principalSubgroup (𝓞 F) F) (x : 𝔸), f (ξ +ᵥ x) = f x

private theorem principalChar_apply (ψ : AddChar 𝔸 ℂ) (γ : F) (x : 𝔸) :
    principalChar ψ γ x = ψ (algebraMap F 𝔸 γ * x) := rfl

private theorem continuous_principalChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (γ : F) :
    Continuous (principalChar ψ γ) :=
  hψ.continuous.comp (continuous_const.mul continuous_id)

private theorem norm_principalChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (γ : F) (x : 𝔸) :
    ‖principalChar ψ γ x‖ = 1 :=
  NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _

private theorem principalChar_zero (ψ : AddChar 𝔸 ℂ) (x : 𝔸) : principalChar ψ 0 x = 1 := by
  simp [principalChar_apply]

private theorem principalChar_add (ψ : AddChar 𝔸 ℂ) (γ δ : F) (x : 𝔸) :
    principalChar ψ (γ + δ) x = principalChar ψ γ x * principalChar ψ δ x := by
  simp only [principalChar_apply, map_add, add_mul, AddChar.map_add_eq_mul]

private theorem principalChar_neg {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (γ : F) (x : 𝔸) :
    principalChar ψ (-γ) x = conj (principalChar ψ γ x) := by
  have h1 : principalChar ψ (-γ) x * principalChar ψ γ x = 1 := by
    rw [← principalChar_add, neg_add_cancel, principalChar_zero]
  have h2 : principalChar ψ γ x * conj (principalChar ψ γ x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_principalChar hψ, one_pow,
      Complex.ofReal_one]
  calc principalChar ψ (-γ) x
      = principalChar ψ (-γ) x * (principalChar ψ γ x * conj (principalChar ψ γ x)) := by
        rw [h2, mul_one]
    _ = (principalChar ψ (-γ) x * principalChar ψ γ x) * conj (principalChar ψ γ x) := by ring
    _ = conj (principalChar ψ γ x) := by rw [h1, one_mul]

private theorem principalChar_principal_add {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (γ : F)
    (ξ : AdeleRing.principalSubgroup (𝓞 F) F) (x : 𝔸) :
    principalChar ψ γ (ξ +ᵥ x) = principalChar ψ γ x := by
  obtain ⟨ξ, hξ⟩ := ξ
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hξ
  change principalChar ψ γ (algebraMap F 𝔸 a + x) = principalChar ψ γ x
  simp only [principalChar_apply, mul_add, AddChar.map_add_eq_mul]
  rw [← map_mul (algebraMap F 𝔸) γ a, hψ.principalInvariant, one_mul]

private theorem setIntegral_adelicBox_comp_add {f : 𝔸 → ℂ} (hf : PrincipalInvariant f) (x₀ : 𝔸) :
    ∫ x in adelicBox F, f (x₀ + x) ∂(adelicAddHaar (𝓞 F) F) =
      ∫ x in adelicBox F, f x ∂(adelicAddHaar (𝓞 F) F) := by
  have hs := isAddFundamentalDomain_adelicBox_adelicAddHaar F
  have hpres : MeasurePreserving (fun x : 𝔸 => x₀ + x) (adelicAddHaar (𝓞 F) F)
      (adelicAddHaar (𝓞 F) F) := measurePreserving_add_left _ x₀
  have hpres' : MeasurePreserving (fun x : 𝔸 => -x₀ + x) (adelicAddHaar (𝓞 F) F)
      (adelicAddHaar (𝓞 F) F) := measurePreserving_add_left _ (-x₀)
  have ht : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x : 𝔸 => x₀ + x) '' adelicBox F) (adelicAddHaar (𝓞 F) F) := by
    have h := hs.image_of_equiv (Equiv.addLeft x₀) (by simpa using hpres'.quasiMeasurePreserving)
      (Equiv.refl _) (fun ξ x => ?_)
    · simpa using h
    · change x₀ + (↑ξ + x) = ↑ξ + (x₀ + x)
      exact add_left_comm _ _ _
  have hemb : MeasurableEmbedding fun x : 𝔸 => x₀ + x :=
    (MeasurableEquiv.addLeft x₀).measurableEmbedding
  rw [hs.setIntegral_eq ht hf, hpres.setIntegral_image_emb hemb]

private theorem setIntegral_principalChar_eq_zero {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {η : F}
    (hη : η ≠ 0) :
    ∫ x in adelicBox F, principalChar ψ η x ∂(adelicAddHaar (𝓞 F) F) = 0 := by
  obtain ⟨y, hy⟩ : ∃ y : 𝔸, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ.nontrivial (AddChar.ext ψ 1 fun a => by simpa using h a)
  set x₀ : 𝔸 := algebraMap F 𝔸 η⁻¹ * y with hx₀
  have hval : principalChar ψ η x₀ = ψ y := by
    rw [principalChar_apply, hx₀, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hη, map_one, one_mul]
  have htrans := setIntegral_adelicBox_comp_add (principalChar_principal_add hψ η) x₀
  have hmul : ∀ x, principalChar ψ η (x₀ + x) = ψ y * principalChar ψ η x := by
    intro x
    rw [← hval]
    simp only [principalChar_apply, mul_add, AddChar.map_add_eq_mul]
  simp_rw [hmul] at htrans
  rw [integral_const_mul] at htrans
  have h2 : (ψ y - 1) * ∫ x in adelicBox F, principalChar ψ η x ∂(adelicAddHaar (𝓞 F) F) = 0 := by
    rw [sub_mul, one_mul, htrans, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hy)

private theorem integral_conj_principalChar_mul_self {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (γ : F) :
    ∫ x, conj (principalChar ψ γ x) * principalChar ψ γ x ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F])
      = 1 := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  have h : ∀ x, conj (principalChar ψ γ x) * principalChar ψ γ x = 1 := by
    intro x
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_principalChar hψ, one_pow,
      Complex.ofReal_one]
  simp [h]

private theorem integral_conj_principalChar_mul_of_ne {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {γ δ : F}
    (hγδ : γ ≠ δ) :
    ∫ x, conj (principalChar ψ γ x) * principalChar ψ δ x ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F])
      = 0 := by
  have h : ∀ x, conj (principalChar ψ γ x) * principalChar ψ δ x = principalChar ψ (δ - γ) x := by
    intro x
    rw [← principalChar_neg hψ, ← principalChar_add, neg_add_eq_sub]
  simp_rw [h]
  rw [ProbabilityTheory.cond, integral_smul_measure,
    setIntegral_principalChar_eq_zero hψ (sub_ne_zero.mpr hγδ.symm), smul_zero]

variable (F) in

private abbrev PeriodQuot : Type := 𝔸 ⧸ AdeleRing.principalSubgroup (𝓞 F) F

variable (F) in
private theorem compactSpace_periodQuot : CompactSpace (PeriodQuot F) := by
  exact NumberField.AdeleRing.compactSpace_quotient_principalSubgroup F

private noncomputable def descend (f : 𝔸 → ℂ) (hf : PrincipalInvariant f) : PeriodQuot F → ℂ :=
  Quotient.lift f fun a b hab => by
    have hab' : -a + b ∈ AdeleRing.principalSubgroup (𝓞 F) F := QuotientAddGroup.leftRel_apply.mp hab
    have := hf ⟨-a + b, hab'⟩ a
    simp only [AddSubgroup.mk_vadd, vadd_eq_add] at this
    rw [add_comm, ← add_assoc, add_neg_cancel, zero_add] at this
    exact this.symm

private theorem descend_mk (f : 𝔸 → ℂ) (hf : PrincipalInvariant f) (x : 𝔸) :
    descend f hf (QuotientAddGroup.mk x : PeriodQuot F) = f x := rfl

private theorem continuous_descend {f : 𝔸 → ℂ} (hfc : Continuous f) (hf : PrincipalInvariant f) :
    Continuous (descend f hf) :=
  continuous_quot_lift _ hfc

private noncomputable def descendCM (f : 𝔸 → ℂ) (hfc : Continuous f) (hf : PrincipalInvariant f) :
    C(PeriodQuot F, ℂ) :=
  ⟨descend f hf, continuous_descend hfc hf⟩

private noncomputable def charCM {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (γ : F) :
    C(PeriodQuot F, ℂ) :=
  descendCM (principalChar ψ γ) (continuous_principalChar hψ γ) (principalChar_principal_add hψ γ)

private theorem charCM_mk {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (γ : F) (x : 𝔸) :
    charCM hψ γ (QuotientAddGroup.mk x : PeriodQuot F) = principalChar ψ γ x := rfl

private theorem span_charCM_mul_mem {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {p q : C(PeriodQuot F, ℂ)}
    (hp : p ∈ Submodule.span ℂ (Set.range (charCM hψ)))
    (hq : q ∈ Submodule.span ℂ (Set.range (charCM hψ))) :
    p * q ∈ Submodule.span ℂ (Set.range (charCM hψ)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨γ, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨δ, rfl⟩ := hq
      refine Submodule.subset_span ⟨γ + δ, ?_⟩
      ext z
      induction z using QuotientAddGroup.induction_on with
      | H x => simp [charCM_mk, principalChar_add]
    | zero => simp
    | add q₁ q₂ _ _ h₁ h₂ => rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
    | smul c q _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => simp
  | add p₁ p₂ _ _ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  | smul c p _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

private theorem span_charCM_star_mem {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {p : C(PeriodQuot F, ℂ)}
    (hp : p ∈ Submodule.span ℂ (Set.range (charCM hψ))) :
    star p ∈ Submodule.span ℂ (Set.range (charCM hψ)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨γ, rfl⟩ := hp
    refine Submodule.subset_span ⟨-γ, ?_⟩
    ext z
    induction z using QuotientAddGroup.induction_on with
    | H x => simp [charCM_mk, principalChar_neg hψ]
  | zero => simp
  | add p₁ p₂ _ _ h₁ h₂ => rw [star_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c p _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h

private theorem one_mem_span_charCM {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    (1 : C(PeriodQuot F, ℂ)) ∈ Submodule.span ℂ (Set.range (charCM hψ)) := by
  refine Submodule.subset_span ⟨0, ?_⟩
  ext z
  induction z using QuotientAddGroup.induction_on with
  | H x => simp [charCM_mk, principalChar_zero]

private noncomputable def charAlgebra {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    StarSubalgebra ℂ C(PeriodQuot F, ℂ) where
  carrier := Submodule.span ℂ (Set.range (charCM hψ))
  mul_mem' := span_charCM_mul_mem hψ
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  algebraMap_mem' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (one_mem_span_charCM hψ)
  star_mem' := span_charCM_star_mem hψ

private theorem mem_charAlgebra_iff {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (p : C(PeriodQuot F, ℂ)) :
    p ∈ charAlgebra hψ ↔ p ∈ Submodule.span ℂ (Set.range (charCM hψ)) := Iff.rfl

private theorem charAlgebra_separatesPoints {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    (charAlgebra hψ).SeparatesPoints := by
  intro q₁ q₂ hne
  induction q₁ using QuotientAddGroup.induction_on with
  | H x₁ =>
  induction q₂ using QuotientAddGroup.induction_on with
  | H x₂ =>
  have hx : x₁ - x₂ ∉ Set.range (algebraMap F 𝔸) := by
    intro ⟨a, ha⟩
    apply hne
    rw [QuotientAddGroup.eq]
    exact ⟨-a, by rw [map_neg, ha]; abel⟩
  have hsep : ∃ ξ : F, ψ ((x₁ - x₂) * algebraMap F 𝔸 ξ) ≠ 1 := by
    by_contra h
    push Not at h
    exact hx (NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one F hψ _ h)
  obtain ⟨ξ, hξ⟩ := hsep
  refine ⟨_, ⟨charCM hψ ξ, Submodule.subset_span ⟨ξ, rfl⟩, rfl⟩, ?_⟩
  simp only [charCM_mk]
  intro heq
  apply hξ
  have h1 : principalChar ψ ξ x₁ = principalChar ψ ξ x₂ * ψ ((x₁ - x₂) * algebraMap F 𝔸 ξ) := by
    simp only [principalChar_apply]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [heq] at h1
  have hne0 : principalChar ψ ξ x₂ ≠ 0 := by
    intro h0
    have := norm_principalChar hψ ξ x₂
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact (mul_right_eq_self₀.mp h1.symm).resolve_right hne0

private theorem exists_finset_norm_sub_sum_le {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {f : 𝔸 → ℂ}
    (hfc : Continuous f) (hf : PrincipalInvariant f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset F) (c : F → ℂ), ∀ x, ‖f x - ∑ γ ∈ s, c γ * principalChar ψ γ x‖ ≤ ε := by
  haveI := compactSpace_periodQuot F
  have hdense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (charAlgebra hψ) (charAlgebra_separatesPoints hψ)
  set g : C(PeriodQuot F, ℂ) := descendCM f hfc hf with hg
  have hg_mem : g ∈ (charAlgebra hψ).topologicalClosure := by rw [hdense]; trivial
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hg_mem
  obtain ⟨p, hp, hdist⟩ := hg_mem ε hε
  rw [SetLike.mem_coe, mem_charAlgebra_iff, Finsupp.mem_span_range_iff_exists_finsupp] at hp
  obtain ⟨c, hc⟩ := hp
  refine ⟨c.support, c, fun x => ?_⟩
  have hpt : p (QuotientAddGroup.mk x : PeriodQuot F) = ∑ γ ∈ c.support, c γ * principalChar ψ γ x := by
    rw [← hc, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp [charCM_mk]
  have hgx : g (QuotientAddGroup.mk x : PeriodQuot F) = f x := rfl
  have hd := ContinuousMap.dist_apply_le_dist (f := g) (g := p) (QuotientAddGroup.mk x : PeriodQuot F)
  rw [hgx, hpt, dist_eq_norm] at hd
  exact hd.trans hdist.le

open scoped ENNReal

variable (F) in

private theorem integral_norm_sq_le_tsum_norm_whittakerCoefficient_sq
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : 𝔸 => φ (unipotentGL2 u * g))
    (hper : ∀ (ξ : F) (u : 𝔸), φ (unipotentGL2 (algebraMap F 𝔸 ξ + u) * g) = φ (unipotentGL2 u * g)) :
    ∫ u, ‖φ (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν ≤
      ∑' α : F, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 := by
  set f : 𝔸 → ℂ := fun u => φ (unipotentGL2 u * g) with hf_def
  have hfper : PrincipalInvariant f := by
    rintro ⟨ξ, hξ⟩ u
    obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hξ
    exact hper a u

  haveI := isProbabilityMeasure_cond_adelicBox F

  haveI := compactSpace_periodQuot F
  set fQ : C(PeriodQuot F, ℂ) := descendCM f hcont hfper with hfQ
  have hbound : ∀ u, ‖f u‖ ≤ ‖fQ‖ := fun u =>
    ContinuousMap.norm_coe_le_norm fQ (QuotientAddGroup.mk u : PeriodQuot F)

  have key := integral_norm_sq_le_tsum_norm_integral_conj_mul_sq
    (μ := (adelicAddHaar (𝓞 F) F)[|adelicBox F]) (principalChar ψ)
    (fun γ => (continuous_principalChar hψ γ).aestronglyMeasurable)
    (fun γ x => (norm_principalChar hψ γ x).le)
    (fun γ => integral_conj_principalChar_mul_self hψ γ)
    (fun γ δ hγδ => integral_conj_principalChar_mul_of_ne hψ hγδ)
    f hcont.aestronglyMeasurable ‖fQ‖ hbound
    (fun ε hε => exists_finset_norm_sub_sum_le hψ hcont hfper hε)

  have hcoef : ∀ α : F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g =
        ∫ x, conj (principalChar ψ α x) * f x ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F]) := by
    intro α
    show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F 𝔸 α * x))
        ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F])) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ψ (-(algebraMap F 𝔸 α * x)) = conj (principalChar ψ α x) := by
      rw [← principalChar_neg hψ, principalChar_apply, map_neg (algebraMap F 𝔸) α, neg_mul]
    beta_reduce
    rw [h1, mul_comm]
  simp_rw [hcoef]
  exact key

variable (F) in

private theorem integral_norm_sq_eq_tsum_norm_whittakerCoefficient_sq
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : 𝔸 => φ (unipotentGL2 u * g))
    (hper : ∀ (ξ : F) (u : 𝔸), φ (unipotentGL2 (algebraMap F 𝔸 ξ + u) * g) = φ (unipotentGL2 u * g)) :
    ∫ u, ‖φ (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' α : F, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 := by
  refine le_antisymm
    (integral_norm_sq_le_tsum_norm_whittakerCoefficient_sq F D U gen ψ hψ φ g hcont hper) ?_
  refine tsum_le_of_sum_le' (integral_nonneg fun u => by positivity) fun A => ?_
  exact AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq F D U gen ψ hψ φ g
    hcont A

end Adelic

end PeriodParseval

section AdelicBoxMassIdentity

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ProbabilityTheory ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

private theorem globalPoints_unipotentGL2_eq (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F 𝔸 β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, Matrix.GeneralLinearGroup.map]

private theorem coe_nnnorm_sq_eq_ofReal_norm_sq (a : ℂ) :
    ((‖a‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖a‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg a), ofReal_norm, enorm_eq_nnnorm]

private theorem restrict_adelicBox_eq_smul_cond :
    (adelicAddHaar (𝓞 F) F).restrict (adelicBox F)
      = adelicAddHaar (𝓞 F) F (adelicBox F) • (adelicAddHaar (𝓞 F) F)[|adelicBox F] := by
  rw [ProbabilityTheory.cond, smul_smul,
    ENNReal.mul_inv_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne,
    one_smul]

variable {F}

private theorem setLIntegral_adelicBox_nnnorm_sq_eq (f : 𝔸 → ℂ) (hfc : Continuous f)
    (hf : PrincipalInvariant f) :
    ∫⁻ x in adelicBox F, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicAddHaar (𝓞 F) F)
      = adelicAddHaar (𝓞 F) F (adelicBox F)
          * ENNReal.ofReal (∫ u, ‖f u‖ ^ 2 ∂(adelicAddHaar (𝓞 F) F)[|adelicBox F]) := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  haveI := compactSpace_periodQuot F
  have hbound : ∀ u, ‖f u‖ ≤ ‖descendCM f hfc hf‖ := fun u =>
    ContinuousMap.norm_coe_le_norm (descendCM f hfc hf) (QuotientAddGroup.mk u : PeriodQuot F)
  have hint : Integrable (fun u => ‖f u‖ ^ 2) ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) :=
    Integrable.of_bound (hfc.norm.pow 2).aestronglyMeasurable (‖descendCM f hfc hf‖ ^ 2)
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound u) 2)
  rw [restrict_adelicBox_eq_smul_cond F, lintegral_smul_measure, smul_eq_mul,
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun u => sq_nonneg _)]
  simp only [coe_nnnorm_sq_eq_ofReal_norm_sq]

variable (F)

private theorem setLIntegral_adelicBox_nnnorm_sq_eq_mul_tsum_units
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar 𝔸 ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hcusp : ∀ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g = 0)
    (g : AdelicGL2 (𝓞 F) F) :
    ∫⁻ x in adelicBox F, (‖φ (unipotentGL2 x * g)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicAddHaar (𝓞 F) F) =
      adelicAddHaar (𝓞 F) F (adelicBox F) *
        ∑' α : Fˣ, (‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (globalPoints (𝓞 F) F (NumberField.AdelicLevel.diagOne α) * g)‖₊ : ℝ≥0∞) ^ 2 := by

  have hcont : Continuous fun u : 𝔸 => φ (unipotentGL2 u * g) :=
    hφ.comp ((AutomorphicForm.continuous_unipotentGL2 (R := 𝔸)).mul continuous_const)
  have hper : ∀ (ξ : F) (u : 𝔸),
      φ (unipotentGL2 (algebraMap F 𝔸 ξ + u) * g) = φ (unipotentGL2 u * g) := by
    intro ξ u
    rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2_eq F ξ, hleft]
  have hfper : PrincipalInvariant fun u : 𝔸 => φ (unipotentGL2 u * g) := by
    rintro ⟨ξ, hξ⟩ u
    obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hξ
    exact hper a u

  have hpars : ∫ u, ‖φ (unipotentGL2 u * g)‖ ^ 2 ∂(adelicAddHaar (𝓞 F) F)[|adelicBox F]
      = ∑' α : F, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 :=
    integral_norm_sq_eq_tsum_norm_whittakerCoefficient_sq F D U gen ψ hψ φ g hcont hper

  have hsum : Summable fun α : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 :=
    summable_of_sum_le (fun α => sq_nonneg _) fun A =>
      AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq F D U gen ψ hψ φ g hcont A

  have hsupp : Function.support (fun α : F => ENNReal.ofReal
      (‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2))
        ⊆ Set.range (Units.val : Fˣ → F) := by
    intro α hα
    by_contra hr
    refine Function.mem_support.1 hα ?_
    obtain rfl : α = 0 := Classical.byContradiction fun h0 => hr ⟨Units.mk0 α h0, rfl⟩
    simp [hcusp g]

  have hdiag : ∀ α : Fˣ,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ (α : F) g
        = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
            (globalPoints (𝓞 F) F (NumberField.AdelicLevel.diagOne α) * g) := fun α => by
    have key := AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
      F D U gen ψ hψ φ hleft (α : F) α.ne_zero g
    rwa [Units.mk0_val] at key
  rw [setLIntegral_adelicBox_nnnorm_sq_eq _ hcont hfper, hpars,
    ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) hsum, ← Units.val_injective.tsum_eq hsupp]
  congr 1
  refine tsum_congr fun α => ?_
  rw [hdiag α, coe_nnnorm_sq_eq_ofReal_norm_sq]

end AdelicBoxMassIdentity

private theorem setLIntegral_adelicBox_nnnorm_sq_eq_mul_tsum_nnnorm_whittakerCoefficient_sq
    (D : Set (AdelicGL2 (𝓞 K) K)) (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (hcusp : ∀ h : AdelicGL2 (𝓞 K) K,
      whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 0 h = 0)
    (h : AdelicGL2 (𝓞 K) K) :
    ∫⁻ x in adelicBox K, (‖φ (unipotentGL2 x * h)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicAddHaar (𝓞 K) K) =
      adelicAddHaar (𝓞 K) K (adelicBox K) *
        ∑' α : Kˣ, (‖whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) φ 1 (globalPoints (𝓞 K) K (diagOne α) * h)‖₊ : ℝ≥0∞) ^ 2 := by
  exact setLIntegral_adelicBox_nnnorm_sq_eq_mul_tsum_units K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (NumberField.StandardAddChar.stdAddChar K) (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K)
    φ hφ hleft hcusp h

section UnipotentQuotientCovering

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_measurable_density {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw : Measurable (HaarQuotient.weight H μH) := by
    unfold HaarQuotient.weight
    rw [dif_pos ⟨inferInstance, inferInstance⟩]
    refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  have hL : Measurable fun g : G => ∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH :=
    Measurable.lintegral_prod_right (f := fun (g : G) (x : H) => HaarQuotient.weight H μH ((x : G) * g))
      (hw.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst))
  have hρ : HaarQuotient.density H μH = fun g =>
      HaarQuotient.weight H μH g * (∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH)⁻¹ := by
    funext g
    rw [HaarQuotient.density, div_eq_mul_inv]
  rw [hρ]
  exact hw.mul hL.inv

private theorem cov_secondCountableTopology_adelicGL2 : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

private theorem cov_secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

private theorem cov_isHaarMeasure_adelicGLHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private theorem cov_isHaarMeasure_unipotentHaar : (unipotentHaar K).IsHaarMeasure :=
  (isHaarMeasure_and_isMulRightInvariant_unipotentHaar K).1

private theorem cov_isMulRightInvariant_unipotentHaar : (unipotentHaar K).IsMulRightInvariant :=
  (isHaarMeasure_and_isMulRightInvariant_unipotentHaar K).2

private theorem cov_isHaarMeasure_rationalTorusUnipotentHaar : (rationalTorusUnipotentHaar K).IsHaarMeasure :=
  (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).1

private theorem cov_isMulRightInvariant_rationalTorusUnipotentHaar :
    (rationalTorusUnipotentHaar K).IsMulRightInvariant :=
  (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).2

attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar

private theorem cov_regular_adelicAddHaar : (adelicAddHaar (𝓞 K) K).Regular := by
  unfold adelicAddHaar Measure.addHaar
  infer_instance

private theorem cov_sFinite_unipotentHaar : SFinite (unipotentHaar K) := by
  unfold unipotentHaar
  infer_instance

private theorem cov_secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ :=
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : AdeleRing (𝓞 K) K ≃ₜ (AdeleRing (𝓞 K) K)ᵐᵒᵖ).symm.isInducing.secondCountableTopology
  Units.isInducing_embedProduct.secondCountableTopology

attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele

private theorem cov_sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  unfold NumberField.Idele.idelicHaar Measure.haar
  infer_instance

attribute [local instance] cov_sigmaFinite_idelicHaar

private theorem cov_countable_units : Countable Kˣ :=
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  Units.val_injective.countable

attribute [local instance] cov_countable_units

private theorem cov_val_globalPoints (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((globalPoints (𝓞 K) K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      (g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (AdeleRing (𝓞 K) K)) :=
  rfl

private theorem cov_val_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(a : A), 1] :=
  rfl

omit [NumberField K] in
private theorem cov_val_unitsMap_scalar (z : Kˣ) :
    ((Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom z :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal fun _ => (z : K) :=
  rfl

private theorem cov_torus_mul_unipotentGL2 (z a : Kˣ) (x : AdeleRing (𝓞 K) K) :
    globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom z) *
        globalPoints (𝓞 K) K (diagOne a) * unipotentGL2 x =
      unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) a * x) *
        (globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom z) *
          globalPoints (𝓞 K) K (diagOne a)) := by
  apply Units.ext
  simp only [Units.val_mul, cov_val_globalPoints, cov_val_diagOne, cov_val_unitsMap_scalar, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.map_apply]
  ring

private theorem cov_torus_mul_centralScalar_mul_diagOne (ζ β : Kˣ) (z t : (AdeleRing (𝓞 K) K)ˣ) :
    globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom ζ) *
        globalPoints (𝓞 K) K (diagOne β) * (centralScalar (𝓞 K) K z * diagOne t) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ * z) *
        diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) β * t) := by
  apply Units.ext
  simp only [Units.val_mul, cov_val_globalPoints, cov_val_diagOne, NumberField.AdelicVolume.centralScalar_val,
    Units.coe_map, MonoidHom.coe_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.map_apply]
  ring

private theorem cov_det_diagOne (t : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne t : AdelicGL2 (𝓞 K) K) = t := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.det, cov_val_diagOne, Matrix.det_diagonal, Fin.prod_univ_two]

private theorem cov_continuous_unipotentGL2 :
    Continuous fun x : AdeleRing (𝓞 K) K => (unipotentGL2 x : AdelicGL2 (𝓞 K) K) := by
  exact AutomorphicForm.continuous_unipotentGL2

private theorem cov_measurable_toAdelicUnipotent : Measurable (toAdelicUnipotent K) :=
  ((cov_continuous_unipotentGL2 K).subtype_mk fun x => ⟨Multiplicative.ofAdd x, rfl⟩).measurable

private theorem cov_continuous_diagOne :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => (diagOne t : AdelicGL2 (𝓞 K) K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 K) K)ˣ =>
      Matrix.diagonal ![(t : AdeleRing (𝓞 K) K), (1 : AdeleRing (𝓞 K) K)]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  · have h : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (((diagOne t)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] := fun t => rfl
    simp_rw [h]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_coe_inv
    · exact continuous_const

private theorem cov_continuous_centralScalar :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => Matrix.diagonal fun _ : Fin 2 => (z : AdeleRing (𝓞 K) K)
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
  · have h : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        (((centralScalar (𝓞 K) K z)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          Matrix.diagonal fun _ => ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) := fun z => rfl
    simp_rw [h]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)

private theorem cov_measurable_weight :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) :=
  ENNReal.measurable_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm K).measurable.inv)

private theorem cov_map_smul_principal_adelicAddHaar (a : Kˣ) :
    Measure.map (fun x : AdeleRing (𝓞 K) K =>
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) • x)
        (adelicAddHaar (𝓞 K) K) = adelicAddHaar (𝓞 K) K := by
  have h := (NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar K (a : K) a.ne_zero).map_eq
  refine Eq.trans (congrArg (fun f : AdeleRing (𝓞 K) K → AdeleRing (𝓞 K) K => Measure.map f (adelicAddHaar (𝓞 K) K))
    (funext fun x => ?_)) h
  simp only [Units.smul_def, smul_eq_mul, Units.coe_map, MonoidHom.coe_coe]

private theorem cov_ideleNorm_principal_mul (β : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) β * t) =
      NumberField.TateGlobal.ideleNorm K t := by
  rw [NumberField.TateGlobal.ideleNorm_mul]
  have h0 : distribHaarChar (AdeleRing (𝓞 K) K)
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) β) = 1 := by
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap K β
    rwa [RingHom.toMonoidHom_eq_coe] at h
  have h : NumberField.TateGlobal.ideleNorm K
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) β) = 1 := by
    unfold NumberField.TateGlobal.ideleNorm
    rw [h0]
    rfl
  rw [h, one_mul]

private noncomputable def cov_torusElt (za : Kˣ × Kˣ) : AdelicGL2 (𝓞 K) K :=
  globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1) *
    globalPoints (𝓞 K) K (diagOne za.2)

omit [NumberField K] in

private theorem cov_unitsMap_scalar_mul_comm (ζ : Kˣ) (m : Matrix.GeneralLinearGroup (Fin 2) K) :
    Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom ζ * m =
      m * Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom ζ := by
  apply Units.ext
  simp only [Units.val_mul, cov_val_unitsMap_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal] <;> ring

private theorem cov_tsum_torus_mul_invariant (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hfN : ∀ x ∈ adelicUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K,
      (∑' za : Kˣ × Kˣ, f (cov_torusElt K za * (x * g))) = ∑' za : Kˣ × Kˣ, f (cov_torusElt K za * g) := by
  let S : Subgroup (AdelicGL2 (𝓞 K) K) :=
    { carrier := {x | ∀ g : AdelicGL2 (𝓞 K) K,
        (∑' za : Kˣ × Kˣ, f (cov_torusElt K za * (x * g))) = ∑' za : Kˣ × Kˣ, f (cov_torusElt K za * g)}
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      one_mem' := fun g => by rw [one_mul]
      inv_mem' := fun {x} hx g => by rw [← hx (x⁻¹ * g), mul_inv_cancel_left] }
  suffices h : rationalTorusUnipotent K ≤ S from fun x hx g => h hx g
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨ζ, rfl⟩ g
    show (∑' za : Kˣ × Kˣ, f (cov_torusElt K za * (globalPoints (𝓞 K) K
        (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom ζ) * g))) = _
    have hre : ∀ za : Kˣ × Kˣ, cov_torusElt K za * (globalPoints (𝓞 K) K
        (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom ζ) * g) =
          cov_torusElt K (za.1 * ζ, za.2) * g := by
      intro za
      simp only [cov_torusElt, map_mul, mul_assoc]
      rw [← mul_assoc (globalPoints (𝓞 K) K (diagOne za.2)), ← map_mul (globalPoints (𝓞 K) K),
        ← cov_unitsMap_scalar_mul_comm K ζ (diagOne za.2), map_mul, mul_assoc]
    simp_rw [hre]
    exact Equiv.tsum_eq (Equiv.prodCongr (Equiv.mulRight ζ) (Equiv.refl Kˣ))
      (fun za : Kˣ × Kˣ => f (cov_torusElt K za * g))
  · rintro _ ⟨β, rfl⟩ g
    show (∑' za : Kˣ × Kˣ, f (cov_torusElt K za * (globalPoints (𝓞 K) K (diagOne β) * g))) = _
    have hre : ∀ za : Kˣ × Kˣ, cov_torusElt K za * (globalPoints (𝓞 K) K (diagOne β) * g) =
        cov_torusElt K (za.1, za.2 * β) * g := by
      intro za
      simp only [cov_torusElt, map_mul, mul_assoc]
    simp_rw [hre]
    exact Equiv.tsum_eq (Equiv.prodCongr (Equiv.refl Kˣ) (Equiv.mulRight β))
      (fun za : Kˣ × Kˣ => f (cov_torusElt K za * g))
  · intro x hx g
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hx
    refine tsum_congr fun za => ?_
    rw [← hy, ← mul_assoc]
    show f (cov_torusElt K za * unipotentGL2 (Multiplicative.toAdd y) * g) = _
    rw [show cov_torusElt K za * unipotentGL2 (Multiplicative.toAdd y) =
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) za.2 * Multiplicative.toAdd y) * cov_torusElt K za from
      cov_torus_mul_unipotentGL2 K za.1 za.2 _, mul_assoc]
    exact hfN _ ⟨Multiplicative.ofAdd (algebraMap K (AdeleRing (𝓞 K) K) za.2 * Multiplicative.toAdd y), rfl⟩ _

private theorem cov_lintegral_unipotentHaar_torus_mul (za : Kˣ × Kˣ) (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ n, G (cov_torusElt K za * (n : AdelicGL2 (𝓞 K) K)) ∂(unipotentHaar K) =
      ∫⁻ n, G ((n : AdelicGL2 (𝓞 K) K) * cov_torusElt K za) ∂(unipotentHaar K) := by
  set τ : AdelicGL2 (𝓞 K) K := cov_torusElt K za with hτ
  set u : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.2
    with hu
  have hcoe : ∀ x : AdeleRing (𝓞 K) K,
      ((toAdelicUnipotent K x : adelicUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 x := fun x => rfl
  have hconj : ∀ x : AdeleRing (𝓞 K) K, τ * unipotentGL2 x = unipotentGL2 (u • x) * τ := fun x => by
    rw [hτ, hu, Units.smul_def, smul_eq_mul, Units.coe_map, MonoidHom.coe_coe]
    exact cov_torus_mul_unipotentGL2 K za.1 za.2 x
  have hm1 : Measurable fun n : adelicUnipotent K => G (τ * (n : AdelicGL2 (𝓞 K) K)) :=
    hG.comp (measurable_const.mul measurable_subtype_coe)
  have hm2 : Measurable fun n : adelicUnipotent K => G ((n : AdelicGL2 (𝓞 K) K) * τ) :=
    hG.comp (measurable_subtype_coe.mul measurable_const)
  have hm3 : Measurable fun y : AdeleRing (𝓞 K) K => G (unipotentGL2 y * τ) :=
    hG.comp ((cov_continuous_unipotentGL2 K).measurable.mul measurable_const)
  unfold unipotentHaar
  rw [lintegral_map hm1 (cov_measurable_toAdelicUnipotent K), lintegral_map hm2 (cov_measurable_toAdelicUnipotent K),
    lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  simp_rw [hcoe, hconj]
  calc ∫⁻ x, G (unipotentGL2 (u • x) * τ) ∂(adelicAddHaar (𝓞 K) K)
      = ∫⁻ y, G (unipotentGL2 y * τ) ∂(Measure.map (fun x : AdeleRing (𝓞 K) K => u • x) (adelicAddHaar (𝓞 K) K)) :=
        (lintegral_map hm3 (measurable_const_smul u)).symm
    _ = ∫⁻ y, G (unipotentGL2 y * τ) ∂(adelicAddHaar (𝓞 K) K) := by
        rw [hu, cov_map_smul_principal_adelicAddHaar K za.2]

private noncomputable def cov_iwasawaSlice (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (z t : (AdeleRing (𝓞 K) K)ˣ) :
    ℝ≥0∞ :=
  ∫⁻ k, f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(maximalCompactHaar K)

private theorem cov_measurable_iwasawaIntegrand (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun p : ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) × adelicMaximalCompact K =>
      f (centralScalar (𝓞 K) K p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 K) K)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K p.1.2)⁻¹) := by
  refine (hf.comp ?_).mul ((cov_measurable_weight K).comp (measurable_snd.comp measurable_fst))
  exact (((cov_continuous_centralScalar K).measurable.comp (measurable_fst.comp measurable_fst)).mul
    ((cov_continuous_diagOne K).measurable.comp (measurable_snd.comp measurable_fst))).mul
      (measurable_subtype_coe.comp measurable_snd)

private theorem cov_measurable_iwasawaSlice (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => cov_iwasawaSlice K f p.1 p.2 := by
  unfold cov_iwasawaSlice
  exact Measurable.lintegral_prod_right
    (f := fun (p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K) =>
      f (centralScalar (𝓞 K) K p.1 * diagOne p.2 * (k : AdelicGL2 (𝓞 K) K)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K p.2)⁻¹))
    (cov_measurable_iwasawaIntegrand K f hf)

private theorem cov_tsum_setLIntegral_principal_mul (D : Set (AdeleRing (𝓞 K) K)ˣ)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) :
    (∑' ζ : Kˣ, ∫⁻ x in D, g (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ * x)
        ∂(NumberField.Idele.idelicHaar K)) = ∫⁻ x, g x ∂(NumberField.Idele.idelicHaar K) := by
  have hinj : Function.Injective
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) :=
    Units.map_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K))
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 K) K) :=
    Countable.of_equiv Kˣ (MonoidHom.ofInjective hinj).toEquiv
  haveI : SMulInvariantMeasure (M4aHerbrand.principalIdeles (𝓞 K) K) (AdeleRing (𝓞 K) K)ˣ
      (NumberField.Idele.idelicHaar K) :=
    ⟨fun γ s _ => measure_preimage_mul (NumberField.Idele.idelicHaar K) (γ : (AdeleRing (𝓞 K) K)ˣ) s⟩
  rw [hDF.lintegral_eq_tsum'' g]
  refine (Equiv.tsum_eq (MonoidHom.ofInjective hinj).toEquiv
    (fun γ : M4aHerbrand.principalIdeles (𝓞 K) K =>
      ∫⁻ x in D, g (γ • x) ∂(NumberField.Idele.idelicHaar K))).symm.trans ?_ |>.symm
  exact tsum_congr fun ζ => rfl

private theorem cov_lintegral_tsum_torus_eq_tsum_iwasawaSlice (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hf : Measurable f) (z t : (AdeleRing (𝓞 K) K)ˣ) :
    ∫⁻ k, (∑' za : Kˣ × Kˣ, f (cov_torusElt K za *
        (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)))) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(maximalCompactHaar K) =
      ∑' za : Kˣ × Kˣ, cov_iwasawaSlice K f
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.1 * z)
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.2 * t) := by
  have hpt : ∀ za : Kˣ × Kˣ, ∀ k : adelicMaximalCompact K,
      cov_torusElt K za * (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) =
        centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.1 * z) *
          diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.2 * t) *
            (k : AdelicGL2 (𝓞 K) K) := by
    intro za k
    rw [← mul_assoc, show cov_torusElt K za * (centralScalar (𝓞 K) K z * diagOne t) = _ from
      cov_torus_mul_centralScalar_mul_diagOne K za.1 za.2 z t]
  unfold cov_iwasawaSlice
  simp_rw [cov_ideleNorm_principal_mul]
  rw [← lintegral_tsum fun za => ?_]
  · refine lintegral_congr fun k => ?_
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun za => by rw [hpt]
  · exact ((hf.comp (measurable_const.mul measurable_subtype_coe)).mul measurable_const).aemeasurable

private theorem cov_lintegral_unipotentQuotientMeasure_eq_lintegral_tsum_torus
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hfN : ∀ x ∈ adelicUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(unipotentQuotientMeasure K) =
      ∫⁻ q, ∑' za : Kˣ × Kˣ,
          f (globalPoints (𝓞 K) K
                (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1) *
              globalPoints (𝓞 K) K (diagOne za.2) * q.out)
        ∂(rationalTorusUnipotentQuotientMeasure K) := by
  have hρm : Measurable (HaarQuotient.density (adelicUnipotent K) (unipotentHaar K)) :=
    cov_measurable_density (adelicUnipotent K) (unipotentHaar K)
  have hfρ : Measurable fun g => f g * HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) g :=
    hf.mul hρm

  have hA := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out (adelicGLHaar (Fin 2) (𝓞 K) K)
    (adelicUnipotent K) (isClosed_adelicUnipotent K) (unipotentHaar K)
    (fun g => f g * HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) g) hfρ
  have hB := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out (adelicGLHaar (Fin 2) (𝓞 K) K)
    (rationalTorusUnipotent K) (isClosed_rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
    (fun g => f g * HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) g) hfρ
  beta_reduce at hA hB

  have hA' : ∀ g : AdelicGL2 (𝓞 K) K,
      ∫⁻ x : adelicUnipotent K, f ((x : AdelicGL2 (𝓞 K) K) * g) *
          HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) ((x : AdelicGL2 (𝓞 K) K) * g)
        ∂(unipotentHaar K) = f g := by
    intro g
    have h1 : ∀ x : adelicUnipotent K, f ((x : AdelicGL2 (𝓞 K) K) * g) = f g := fun x => hfN x x.2 g
    simp_rw [h1]
    rw [lintegral_const_mul (f g) (f := fun x : adelicUnipotent K =>
        HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) ((x : AdelicGL2 (𝓞 K) K) * g))
        (hρm.comp (measurable_subtype_coe.mul measurable_const)),
      HaarQuotient.lintegral_density_mul_eq_one (adelicUnipotent K) (isClosed_adelicUnipotent K)
        (unipotentHaar K) g, mul_one]

  have hB' : ∀ g : AdelicGL2 (𝓞 K) K,
      ∫⁻ x : rationalTorusUnipotent K, f ((x : AdelicGL2 (𝓞 K) K) * g) *
          HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) ((x : AdelicGL2 (𝓞 K) K) * g)
        ∂(rationalTorusUnipotentHaar K) = ∑' za : Kˣ × Kˣ, f (cov_torusElt K za * g) := by
    intro g
    have hint : Measurable fun x : rationalTorusUnipotent K => f ((x : AdelicGL2 (𝓞 K) K) * g) *
        HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) ((x : AdelicGL2 (𝓞 K) K) * g) :=
      (hf.comp (measurable_subtype_coe.mul measurable_const)).mul
        (hρm.comp (measurable_subtype_coe.mul measurable_const))
    unfold rationalTorusUnipotentHaar
    rw [lintegral_sum_measure]
    refine tsum_congr fun za => ?_
    rw [lintegral_map hint ((measurable_const.fun_mul measurable_subtype_coe).subtype_mk)]
    show ∫⁻ n : adelicUnipotent K, f (cov_torusElt K za * (n : AdelicGL2 (𝓞 K) K) * g) *
        HaarQuotient.density (adelicUnipotent K) (unipotentHaar K)
          (cov_torusElt K za * (n : AdelicGL2 (𝓞 K) K) * g) ∂(unipotentHaar K) = f (cov_torusElt K za * g)
    have h2 : ∀ n : adelicUnipotent K,
        f (cov_torusElt K za * (n : AdelicGL2 (𝓞 K) K) * g) = f (cov_torusElt K za * g) := by
      intro n
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp n.2
      rw [← hy]
      show f (cov_torusElt K za * unipotentGL2 (Multiplicative.toAdd y) * g) = _
      rw [show cov_torusElt K za * unipotentGL2 (Multiplicative.toAdd y) =
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) za.2 * Multiplicative.toAdd y) * cov_torusElt K za from
        cov_torus_mul_unipotentGL2 K za.1 za.2 _, mul_assoc]
      exact hfN _ ⟨Multiplicative.ofAdd (algebraMap K (AdeleRing (𝓞 K) K) za.2 * Multiplicative.toAdd y), rfl⟩ _
    simp_rw [h2]
    rw [lintegral_const_mul (f (cov_torusElt K za * g)) (f := fun n : adelicUnipotent K =>
        HaarQuotient.density (adelicUnipotent K) (unipotentHaar K)
          (cov_torusElt K za * (n : AdelicGL2 (𝓞 K) K) * g))
        (hρm.comp ((measurable_const.mul measurable_subtype_coe).mul measurable_const))]
    have h3 := cov_lintegral_unipotentHaar_torus_mul K za
      (fun h => HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) (h * g))
      (hρm.comp (measurable_id.mul measurable_const))
    beta_reduce at h3
    rw [h3]
    simp_rw [mul_assoc]
    rw [HaarQuotient.lintegral_density_mul_eq_one (adelicUnipotent K) (isClosed_adelicUnipotent K)
        (unipotentHaar K) (cov_torusElt K za * g), mul_one]

  calc ∫⁻ q, f q.out ∂(unipotentQuotientMeasure K)
      = ∫⁻ q, ∫⁻ x : adelicUnipotent K, f ((x : AdelicGL2 (𝓞 K) K) * q.out) *
          HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) ((x : AdelicGL2 (𝓞 K) K) * q.out)
            ∂(unipotentHaar K) ∂(unipotentQuotientMeasure K) := by simp_rw [hA']
    _ = ∫⁻ g, f g * HaarQuotient.density (adelicUnipotent K) (unipotentHaar K) g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          hA.symm
    _ = _ := hB
    _ = ∫⁻ q, ∑' za : Kˣ × Kˣ, f (cov_torusElt K za * q.out)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
            (rationalTorusUnipotentHaar K)) := by
          simp_rw [hB']
    _ = _ := rfl

private theorem cov_exists_lintegral_unipotentQuotientMeasure_eq_mul_lintegral_iwasawa
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ adelicUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(unipotentQuotientMeasure K) =
          c * ∫⁻ z, ∫⁻ t, ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa K
  refine ⟨c, hc0, hctop, fun f hf hfN => ?_⟩
  obtain ⟨D, hDm, hDF, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K
      (NumberField.Idele.idelicHaar K)
  have hFm : Measurable fun g : AdelicGL2 (𝓞 K) K => ∑' za : Kˣ × Kˣ, f (cov_torusElt K za * g) :=
    Measurable.tsum fun za => hf.comp (measurable_const.mul measurable_id)
  have hslice := cov_measurable_iwasawaSlice K f hf

  rw [cov_lintegral_unipotentQuotientMeasure_eq_lintegral_tsum_torus K f hf hfN]
  have hmain := hc D D hDm hDm hDF hDF (fun g => ∑' za : Kˣ × Kˣ, f (cov_torusElt K za * g)) hFm
    (cov_tsum_torus_mul_invariant K f hfN)
  beta_reduce at hmain
  rw [show (∫⁻ q, ∑' za : Kˣ × Kˣ, f (globalPoints (𝓞 K) K
        (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1) *
      globalPoints (𝓞 K) K (diagOne za.2) * q.out) ∂(rationalTorusUnipotentQuotientMeasure K)) =
      ∫⁻ q, ∑' za : Kˣ × Kˣ, f (cov_torusElt K za * q.out) ∂(rationalTorusUnipotentQuotientMeasure K) from rfl,
    hmain]
  congr 1

  simp_rw [cov_lintegral_tsum_torus_eq_tsum_iwasawaSlice K f hf]

  have ht : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ∫⁻ t in D, ∑' za : Kˣ × Kˣ, cov_iwasawaSlice K f
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.1 * z)
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.2 * t)
        ∂(NumberField.Idele.idelicHaar K) =
      ∑' ζ : Kˣ, ∫⁻ t, cov_iwasawaSlice K f
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ * z) t
        ∂(NumberField.Idele.idelicHaar K) := by
    intro z
    rw [lintegral_tsum (f := fun (za : Kˣ × Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ) => cov_iwasawaSlice K f
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.1 * z)
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) za.2 * t))
        fun za => ((hslice.comp measurable_prodMk_left).comp (measurable_const.mul measurable_id)).aemeasurable,
      ENNReal.tsum_prod']
    exact tsum_congr fun ζ => cov_tsum_setLIntegral_principal_mul K D hDF (cov_iwasawaSlice K f
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ * z))
  simp_rw [ht]

  rw [lintegral_tsum (f := fun (ζ : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) => ∫⁻ t, cov_iwasawaSlice K f
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ * z) t
        ∂(NumberField.Idele.idelicHaar K))
      fun ζ => ((Measurable.lintegral_prod_right (ν := NumberField.Idele.idelicHaar K)
        (f := fun z t => cov_iwasawaSlice K f z t) hslice).comp (measurable_const.mul measurable_id)).aemeasurable,
    cov_tsum_setLIntegral_principal_mul K D hDF
      (fun z => ∫⁻ t, cov_iwasawaSlice K f z t ∂(NumberField.Idele.idelicHaar K))]
  rfl

end UnipotentQuotientCovering

section IwasawaShadowMass

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel NumberField.Idele.ideleBorel
  NumberField.Idele.borelSpace_ideleBorel

attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_secondCountableTopology_idele cov_sigmaFinite_idelicHaar cov_countable_units
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem iwasawa_principalIdele_eq (γ : Kˣ) :
    principalIdele K γ = Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) γ :=
  Units.ext rfl

private theorem iwasawa_ideleNorm_principalIdele_mul (β : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K (principalIdele K β * t) = NumberField.TateGlobal.ideleNorm K t := by
  rw [iwasawa_principalIdele_eq]
  exact cov_ideleNorm_principal_mul K β t

private theorem iwasawa_globalPoints_diagOne_mul_unipotentGL2_mul (α : Kˣ) (x : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) :
    globalPoints (𝓞 K) K (diagOne α) * (unipotentGL2 x * g) =
      unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) α * x) * (globalPoints (𝓞 K) K (diagOne α) * g) := by
  have h := cov_torus_mul_unipotentGL2 K 1 α x
  simp only [_root_.map_one, one_mul] at h
  rw [← mul_assoc, h, mul_assoc]

private theorem iwasawa_globalPoints_diagOne_mul_centralScalar_mul_diagOne (α : Kˣ) (z t : (AdeleRing (𝓞 K) K)ˣ) :
    globalPoints (𝓞 K) K (diagOne α) * (centralScalar (𝓞 K) K z * diagOne t) =
      centralScalar (𝓞 K) K z * diagOne (principalIdele K α * t) := by
  have h := cov_torus_mul_centralScalar_mul_diagOne K 1 α z t
  simp only [_root_.map_one, one_mul] at h
  rw [iwasawa_principalIdele_eq]
  exact h

private theorem iwasawa_unipotentGL2_mul_centralScalar_mul (x : AdeleRing (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    unipotentGL2 x * (centralScalar (𝓞 K) K z * g) = centralScalar (𝓞 K) K z * (unipotentGL2 x * g) := by
  have h : unipotentGL2 x * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * unipotentGL2 x := by
    apply Units.ext
    simp only [Units.val_mul, NumberField.AdelicVolume.centralScalar_val, unipotentGL2_coe]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  rw [← mul_assoc, h, mul_assoc]

private theorem iwasawa_globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  apply Units.ext
  rw [cov_val_globalPoints, unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem iwasawa_whittakerCoefficient_centralScalar_mul (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hχ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), φ (centralScalar (𝓞 K) K z * g) = χ z * φ g)
    (a : K) (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ a (centralScalar (𝓞 K) K z * g) = χ z * whittakerCoefficient K pins ψ φ a g := by
  unfold whittakerCoefficient
  simp only [iwasawa_unipotentGL2_mul_centralScalar_mul, hχ, mul_assoc]
  exact integral_const_mul (χ z) _

private noncomputable def iwasawa_torusFn (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (t : (AdeleRing (𝓞 K) K)ˣ)
    (k : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  G (diagOne t * k) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)

private noncomputable def iwasawa_shadowFn (E : Set (AdelicGL2 (𝓞 K) K)) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (γ : Kˣ) (z t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  E.indicator 1 (centralScalar (𝓞 K) K z * diagOne ((principalIdele K γ)⁻¹ * t) * k) * m z

private noncomputable def iwasawa_tripleFn (E : Set (AdelicGL2 (𝓞 K) K)) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (z t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  E.indicator 1 (centralScalar (𝓞 K) K z * diagOne t * k) * m z *
    ((∑' α : Kˣ, G (diagOne (principalIdele K α * t) * k)) *
      ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))

private theorem iwasawa_measurable_shadowFn_at {X : Type*} [MeasurableSpace X] (E : Set (AdelicGL2 (𝓞 K) K))
    (hEm : MeasurableSet E) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (γ : Kˣ) (k : AdelicGL2 (𝓞 K) K)
    {fz ft : X → (AdeleRing (𝓞 K) K)ˣ} (hz : Measurable fz) (ht : Measurable ft) :
    Measurable fun x : X => iwasawa_shadowFn K E m γ (fz x) (ft x) k := by
  unfold iwasawa_shadowFn
  have h1 : Measurable fun x : X => centralScalar (𝓞 K) K (fz x) * diagOne ((principalIdele K γ)⁻¹ * ft x) * k :=
    (((cov_continuous_centralScalar K).measurable.comp hz).mul
      ((cov_continuous_diagOne K).measurable.comp (ht.const_mul (principalIdele K γ)⁻¹))).mul_const k
  exact ((measurable_one.indicator hEm).comp h1).mul (hm.comp hz)

private theorem iwasawa_measurable_torusFn_at {X : Type*} [MeasurableSpace X] (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hGm : Measurable G) {ft : X → (AdeleRing (𝓞 K) K)ˣ} {fk : X → AdelicGL2 (𝓞 K) K} (ht : Measurable ft)
    (hk : Measurable fk) : Measurable fun x : X => iwasawa_torusFn K G (ft x) (fk x) := by
  unfold iwasawa_torusFn
  have h1 : Measurable fun x : X => diagOne (ft x) * fk x := ((cov_continuous_diagOne K).measurable.comp ht).mul hk
  exact (hGm.comp h1).mul ((cov_measurable_weight K).comp ht)

private theorem iwasawa_measurable_tripleFn_at {X : Type*} [MeasurableSpace X] (E : Set (AdelicGL2 (𝓞 K) K))
    (hEm : MeasurableSet E) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hGm : Measurable G) {fz ft : X → (AdeleRing (𝓞 K) K)ˣ} {fk : X → AdelicGL2 (𝓞 K) K} (hz : Measurable fz)
    (ht : Measurable ft) (hk : Measurable fk) :
    Measurable fun x : X => iwasawa_tripleFn K E m G (fz x) (ft x) (fk x) := by
  unfold iwasawa_tripleFn
  have h1 : Measurable fun x : X => centralScalar (𝓞 K) K (fz x) * diagOne (ft x) * fk x :=
    (((cov_continuous_centralScalar K).measurable.comp hz).mul ((cov_continuous_diagOne K).measurable.comp ht)).mul hk
  have h2 : ∀ α : Kˣ, Measurable fun x : X => G (diagOne (principalIdele K α * ft x) * fk x) := fun α =>
    hGm.comp (((cov_continuous_diagOne K).measurable.comp (ht.const_mul (principalIdele K α))).mul hk)
  exact (((measurable_one.indicator hEm).comp h1).mul (hm.comp hz)).mul
    ((Measurable.tsum h2).mul ((cov_measurable_weight K).comp ht))

private theorem iwasawa_measurable_summand (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hGm : Measurable G) (α : Kˣ)
    (z : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ =>
      E.indicator 1 (centralScalar (𝓞 K) K z * diagOne t * k) * m z *
        iwasawa_torusFn K G (principalIdele K α * t) k := by
  have h1 : Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => centralScalar (𝓞 K) K z * diagOne t * k :=
    ((cov_continuous_diagOne K).measurable.const_mul (centralScalar (𝓞 K) K z)).mul_const k
  have ht : Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => principalIdele K α * t :=
    measurable_const_mul (principalIdele K α)
  have hk : Measurable fun _ : (AdeleRing (𝓞 K) K)ˣ => k := measurable_const
  exact (((measurable_one.indicator hEm).comp h1).mul_const (m z)).mul (iwasawa_measurable_torusFn_at K G hGm ht hk)

private theorem iwasawa_measurable_shadowFn_mul_torusFn (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hGm : Measurable G)
    (α : Kˣ) (k : AdelicGL2 (𝓞 K) K) :
    Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      iwasawa_shadowFn K E m α p.1 p.2 k * iwasawa_torusFn K G p.2 k := by
  have hz : Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => p.1 := measurable_fst
  have ht : Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => p.2 := measurable_snd
  have hk : Measurable fun _ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => k := measurable_const
  exact (iwasawa_measurable_shadowFn_at K E hEm m hm α k hz ht).mul (iwasawa_measurable_torusFn_at K G hGm ht hk)

private theorem iwasawa_measurable_lintegral_shadowFn (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (α : Kˣ) (k : AdelicGL2 (𝓞 K) K) :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ =>
      ∫⁻ z, iwasawa_shadowFn K E m α z t k ∂(NumberField.Idele.idelicHaar K) := by
  have hz : Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => p.1 := measurable_fst
  have ht : Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => p.2 := measurable_snd
  have h := iwasawa_measurable_shadowFn_at K E hEm m hm α k hz ht
  simpa only using Measurable.lintegral_prod_left' (μ := NumberField.Idele.idelicHaar K) h

private theorem iwasawa_tripleFn_eq_tsum (E : Set (AdelicGL2 (𝓞 K) K)) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (z t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    iwasawa_tripleFn K E m G z t k =
      ∑' α : Kˣ, E.indicator 1 (centralScalar (𝓞 K) K z * diagOne t * k) * m z *
        iwasawa_torusFn K G (principalIdele K α * t) k := by
  unfold iwasawa_tripleFn iwasawa_torusFn
  simp_rw [iwasawa_ideleNorm_principalIdele_mul]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]

private theorem iwasawa_lintegral_summand_eq (E : Set (AdelicGL2 (𝓞 K) K)) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (α : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    ∫⁻ t, E.indicator 1 (centralScalar (𝓞 K) K z * diagOne t * k) * m z *
        iwasawa_torusFn K G (principalIdele K α * t) k ∂(NumberField.Idele.idelicHaar K) =
      ∫⁻ t, iwasawa_shadowFn K E m α z t k * iwasawa_torusFn K G t k ∂(NumberField.Idele.idelicHaar K) := by
  rw [← lintegral_mul_left_eq_self _ (principalIdele K α)⁻¹]
  refine lintegral_congr fun t => ?_
  unfold iwasawa_shadowFn
  rw [mul_inv_cancel_left]

private theorem iwasawa_lintegral_lintegral_tripleFn_eq_tsum (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hGm : Measurable G)
    (k : AdelicGL2 (𝓞 K) K) :
    ∫⁻ z, ∫⁻ t, iwasawa_tripleFn K E m G z t k ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) =
      ∑' α : Kˣ, ∫⁻ z, ∫⁻ t, iwasawa_shadowFn K E m α z t k * iwasawa_torusFn K G t k
        ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  have hJ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ), AEMeasurable (fun t : (AdeleRing (𝓞 K) K)ˣ =>
      E.indicator 1 (centralScalar (𝓞 K) K z * diagOne t * k) * m z * iwasawa_torusFn K G (principalIdele K α * t) k)
      (NumberField.Idele.idelicHaar K) := fun z α =>
    (iwasawa_measurable_summand K E hEm m G hGm α z k).aemeasurable
  have hI : ∀ α : Kˣ, AEMeasurable (fun z : (AdeleRing (𝓞 K) K)ˣ =>
      ∫⁻ t, iwasawa_shadowFn K E m α z t k * iwasawa_torusFn K G t k ∂(NumberField.Idele.idelicHaar K))
      (NumberField.Idele.idelicHaar K) := fun α => by
    simpa only using (Measurable.lintegral_prod_right' (ν := NumberField.Idele.idelicHaar K)
      (iwasawa_measurable_shadowFn_mul_torusFn K E hEm m hm G hGm α k)).aemeasurable
  have hz : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ∫⁻ t, iwasawa_tripleFn K E m G z t k ∂(NumberField.Idele.idelicHaar K) =
        ∑' α : Kˣ, ∫⁻ t, iwasawa_shadowFn K E m α z t k * iwasawa_torusFn K G t k
          ∂(NumberField.Idele.idelicHaar K) := by
    intro z
    simp_rw [iwasawa_tripleFn_eq_tsum]
    rw [lintegral_tsum (hJ z)]
    exact tsum_congr fun α => iwasawa_lintegral_summand_eq K E m G α z k
  simp_rw [hz]
  exact lintegral_tsum hI

private theorem iwasawa_tsum_lintegral_lintegral_eq (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hGm : Measurable G)
    (k : AdelicGL2 (𝓞 K) K) :
    ∑' α : Kˣ, ∫⁻ z, ∫⁻ t, iwasawa_shadowFn K E m α z t k * iwasawa_torusFn K G t k
        ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) =
      ∫⁻ t, G (diagOne t * k) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * shadowWeight K E m t k
        ∂(NumberField.Idele.idelicHaar K) := by
  have hBA : ∀ α : Kˣ, AEMeasurable (Function.uncurry fun z t : (AdeleRing (𝓞 K) K)ˣ =>
      iwasawa_shadowFn K E m α z t k * iwasawa_torusFn K G t k)
      ((NumberField.Idele.idelicHaar K).prod (NumberField.Idele.idelicHaar K)) := fun α => by
    simpa only [Function.uncurry_def] using
      (iwasawa_measurable_shadowFn_mul_torusFn K E hEm m hm G hGm α k).aemeasurable
  have hB : ∀ (α : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ),
      Measurable fun z : (AdeleRing (𝓞 K) K)ˣ => iwasawa_shadowFn K E m α z t k := by
    intro α t
    have hz : Measurable fun z : (AdeleRing (𝓞 K) K)ˣ => z := measurable_id'
    have ht : Measurable fun _ : (AdeleRing (𝓞 K) K)ˣ => t := measurable_const
    exact iwasawa_measurable_shadowFn_at K E hEm m hm α k hz ht
  have hP : ∀ α : Kˣ, AEMeasurable (fun t : (AdeleRing (𝓞 K) K)ˣ =>
      (∫⁻ z, iwasawa_shadowFn K E m α z t k ∂(NumberField.Idele.idelicHaar K)) * iwasawa_torusFn K G t k)
      (NumberField.Idele.idelicHaar K) := by
    intro α
    have ht : Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => t := measurable_id'
    have hk : Measurable fun _ : (AdeleRing (𝓞 K) K)ˣ => k := measurable_const
    exact ((iwasawa_measurable_lintegral_shadowFn K E hEm m hm α k).mul
      (iwasawa_measurable_torusFn_at K G hGm ht hk)).aemeasurable
  have h1 : ∀ α : Kˣ,
      ∫⁻ z, ∫⁻ t, iwasawa_shadowFn K E m α z t k * iwasawa_torusFn K G t k
          ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) =
        ∫⁻ t, (∫⁻ z, iwasawa_shadowFn K E m α z t k ∂(NumberField.Idele.idelicHaar K)) * iwasawa_torusFn K G t k
          ∂(NumberField.Idele.idelicHaar K) := by
    intro α
    rw [lintegral_lintegral_swap (hBA α)]
    exact lintegral_congr fun t => lintegral_mul_const _ (hB α t)
  have h2 : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
      ∑' α : Kˣ, (∫⁻ z, iwasawa_shadowFn K E m α z t k ∂(NumberField.Idele.idelicHaar K)) * iwasawa_torusFn K G t k =
        G (diagOne t * k) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * shadowWeight K E m t k := by
    intro t
    rw [ENNReal.tsum_mul_right, mul_comm]
    simp only [iwasawa_torusFn, iwasawa_shadowFn, shadowWeight]
  simp_rw [h1]
  rw [← lintegral_tsum hP]
  exact lintegral_congr h2

private theorem iwasawa_lintegral_indicator_tsum_eq_mul_lintegral_shadowWeight (c : ℝ≥0∞)
    (hc : ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
      (∀ x ∈ adelicUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂(unipotentQuotientMeasure K) =
        c * ∫⁻ z, ∫⁻ t, ∫⁻ k,
              f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
            ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K))
    (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (hE : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), unipotentGL2 x * g ∈ E ↔ g ∈ E)
    (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hGm : Measurable G)
    (hGN : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), G (unipotentGL2 x * g) = G g)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m)
    (hGZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), G (centralScalar (𝓞 K) K z * g) = m z * G g) :
    ∫⁻ q, E.indicator (fun g => ∑' α : Kˣ, G (globalPoints (𝓞 K) K (diagOne α) * g)) q.out
        ∂(unipotentQuotientMeasure K) =
      c * ∫⁻ k, ∫⁻ t, G (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * shadowWeight K E m t (k : AdelicGL2 (𝓞 K) K)
        ∂(NumberField.Idele.idelicHaar K) ∂(maximalCompactHaar K) := by

  have hFm : Measurable (E.indicator fun g : AdelicGL2 (𝓞 K) K =>
      ∑' α : Kˣ, G (globalPoints (𝓞 K) K (diagOne α) * g)) :=
    (Measurable.tsum fun α => hGm.comp (measurable_const_mul (globalPoints (𝓞 K) K (diagOne α)))).indicator hEm
  have hFN : ∀ x ∈ adelicUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K,
      E.indicator (fun g : AdelicGL2 (𝓞 K) K => ∑' α : Kˣ, G (globalPoints (𝓞 K) K (diagOne α) * g)) (x * g) =
        E.indicator (fun g : AdelicGL2 (𝓞 K) K => ∑' α : Kˣ, G (globalPoints (𝓞 K) K (diagOne α) * g)) g := by
    intro x hx g
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    show E.indicator (fun g : AdelicGL2 (𝓞 K) K => ∑' α : Kˣ, G (globalPoints (𝓞 K) K (diagOne α) * g))
        (unipotentGL2 (Multiplicative.toAdd y) * g) = _
    by_cases hg : g ∈ E
    · rw [Set.indicator_of_mem ((hE _ g).mpr hg), Set.indicator_of_mem hg]
      refine tsum_congr fun α => ?_
      rw [iwasawa_globalPoints_diagOne_mul_unipotentGL2_mul, hGN]
    · rw [Set.indicator_of_notMem (fun h => hg ((hE _ g).mp h)), Set.indicator_of_notMem hg]

  have hpt : ∀ (z t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K),
      E.indicator (fun g : AdelicGL2 (𝓞 K) K => ∑' α : Kˣ, G (globalPoints (𝓞 K) K (diagOne α) * g))
          (centralScalar (𝓞 K) K z * diagOne t * k) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) =
        iwasawa_tripleFn K E m G z t k := by
    intro z t k
    unfold iwasawa_tripleFn
    by_cases h : centralScalar (𝓞 K) K z * diagOne t * k ∈ E
    · have hα : ∀ α : Kˣ, G (globalPoints (𝓞 K) K (diagOne α) * (centralScalar (𝓞 K) K z * diagOne t * k)) =
          m z * G (diagOne (principalIdele K α * t) * k) := fun α => by
        rw [← mul_assoc (globalPoints (𝓞 K) K (diagOne α)), iwasawa_globalPoints_diagOne_mul_centralScalar_mul_diagOne,
          mul_assoc, hGZ]
      simp only [Set.indicator_of_mem h, Pi.one_apply, one_mul]
      simp_rw [hα]
      rw [ENNReal.tsum_mul_left, mul_assoc]
    · simp only [Set.indicator_of_notMem h, zero_mul]

  have hS1 : ∀ z : (AdeleRing (𝓞 K) K)ˣ, AEMeasurable (Function.uncurry fun (t : (AdeleRing (𝓞 K) K)ˣ)
      (k : adelicMaximalCompact K) => iwasawa_tripleFn K E m G z t (k : AdelicGL2 (𝓞 K) K))
      ((NumberField.Idele.idelicHaar K).prod (maximalCompactHaar K)) := by
    intro z
    have hz : Measurable fun _ : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K => z := measurable_const
    have ht : Measurable fun q : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K => q.1 := measurable_fst
    have hk : Measurable fun q : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K => (q.2 : AdelicGL2 (𝓞 K) K) :=
      measurable_snd.subtype_coe
    simpa only [Function.uncurry_def] using (iwasawa_measurable_tripleFn_at K E hEm m hm G hGm hz ht hk).aemeasurable
  have hS2 : AEMeasurable (Function.uncurry fun (z : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K) =>
      ∫⁻ t, iwasawa_tripleFn K E m G z t (k : AdelicGL2 (𝓞 K) K) ∂(NumberField.Idele.idelicHaar K))
      ((NumberField.Idele.idelicHaar K).prod (maximalCompactHaar K)) := by
    have hz : Measurable fun q : ((AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K) × (AdeleRing (𝓞 K) K)ˣ => q.1.1 :=
      measurable_fst.fst
    have ht : Measurable fun q : ((AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K) × (AdeleRing (𝓞 K) K)ˣ => q.2 :=
      measurable_snd
    have hk : Measurable fun q : ((AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K) × (AdeleRing (𝓞 K) K)ˣ =>
        (q.1.2 : AdelicGL2 (𝓞 K) K) := measurable_fst.snd.subtype_coe
    have hq := iwasawa_measurable_tripleFn_at K E hEm m hm G hGm hz ht hk
    simpa only [Function.uncurry_def] using
      (Measurable.lintegral_prod_right' (ν := NumberField.Idele.idelicHaar K) hq).aemeasurable
  have hE1 : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ∫⁻ t, ∫⁻ k, iwasawa_tripleFn K E m G z t (k : AdelicGL2 (𝓞 K) K) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) =
        ∫⁻ k, ∫⁻ t, iwasawa_tripleFn K E m G z t (k : AdelicGL2 (𝓞 K) K) ∂(NumberField.Idele.idelicHaar K)
          ∂(maximalCompactHaar K) := fun z => lintegral_lintegral_swap (hS1 z)

  rw [hc _ hFm hFN]
  congr 1
  simp_rw [hpt, hE1]
  rw [lintegral_lintegral_swap hS2]
  refine lintegral_congr fun k => ?_
  rw [iwasawa_lintegral_lintegral_tripleFn_eq_tsum K E hEm m hm G hGm,
    iwasawa_tsum_lintegral_lintegral_eq K E hEm m hm G hGm]

end IwasawaShadowMass

private theorem lintegral_unipotentQuotient_indicator_tsum_eq_mul_lintegral_shadowWeight
    (D : Set (AdelicGL2 (𝓞 K) K)) (c : ℝ≥0∞)
    (hc : ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
      (∀ x ∈ adelicUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂(unipotentQuotientMeasure K) =
        c * ∫⁻ z, ∫⁻ t, ∫⁻ k,
              f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
            ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K))
    (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (hE : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), unipotentGL2 x * g ∈ E ↔ g ∈ E)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hχ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), φ (centralScalar (𝓞 K) K z * g) = χ z * φ g) :
    ∫⁻ q, E.indicator (fun g => ∑' α : Kˣ, (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (globalPoints (𝓞 K) K (diagOne α) * g)‖₊ : ℝ≥0∞) ^ 2)
        q.out ∂(unipotentQuotientMeasure K) =
      c * ∫⁻ k, ∫⁻ t, (‖whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) *
            shadowWeight K E (fun z => (‖χ z‖₊ : ℝ≥0∞) ^ 2) t (k : AdelicGL2 (𝓞 K) K)
        ∂(NumberField.Idele.idelicHaar K) ∂(maximalCompactHaar K) := by
  by_cases hφ0 : ∀ g : AdelicGL2 (𝓞 K) K, φ g = 0
  ·
    have h1 : ∀ g : AdelicGL2 (𝓞 K) K, (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖₊ : ℝ≥0∞) ^ 2 = 0 := by
      intro g
      unfold whittakerCoefficient
      simp only [hφ0, zero_mul, integral_zero, nnnorm_zero, ENNReal.coe_zero]
      exact zero_pow two_ne_zero
    have hL : ∀ g : AdelicGL2 (𝓞 K) K, E.indicator (fun g => ∑' α : Kˣ, (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (globalPoints (𝓞 K) K (diagOne α) * g)‖₊ : ℝ≥0∞) ^ 2)
        g = 0 := fun g =>
      Set.indicator_apply_eq_zero.mpr fun _ => (tsum_congr fun α => h1 _).trans tsum_zero
    have hR : ∀ (k : adelicMaximalCompact K) (t : (AdeleRing (𝓞 K) K)ˣ), (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) *
            shadowWeight K E (fun z => (‖χ z‖₊ : ℝ≥0∞) ^ 2) t (k : AdelicGL2 (𝓞 K) K) = 0 := fun k t => by
      rw [h1, zero_mul, zero_mul]
    simp_rw [hL, hR, lintegral_zero, mul_zero]
  ·
    obtain ⟨g₀, hg₀⟩ := not_forall.mp hφ0
    have hψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K
    have hχm : Measurable fun z : (AdeleRing (𝓞 K) K)ˣ => (‖χ z‖₊ : ℝ≥0∞) ^ 2 := by
      have hχ' : χ = fun z => φ (centralScalar (𝓞 K) K z * g₀) / φ g₀ := by
        funext z
        rw [hχ z g₀, mul_div_cancel_right₀ _ hg₀]
      rw [hχ']
      exact (((hφ.comp ((cov_continuous_centralScalar K).mul continuous_const)).div_const
        (φ g₀)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
    have hGm : Measurable fun g : AdelicGL2 (𝓞 K) K => (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖₊ : ℝ≥0∞) ^ 2 :=
      ((AutomorphicForm.continuous_whittakerCoefficient K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K) hψ.continuous φ hφ
        1).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
    have hψ1 : ∀ y : AdeleRing (𝓞 K) K, ‖NumberField.StandardAddChar.stdAddChar K y‖₊ = 1 := fun y =>
      NNReal.eq ((coe_nnnorm _).trans (NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K hψ y))
    have hper : ∀ (g : AdelicGL2 (𝓞 K) K) (β : K) (u : AdeleRing (𝓞 K) K),
        φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = φ (unipotentGL2 u * g) := by
      intro g β u
      rw [unipotentGL2_add, ← iwasawa_globalPoints_unipotentGL2, mul_assoc, hleft]
    have hGN : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (unipotentGL2 x * g)‖₊ : ℝ≥0∞) ^ 2 =
          (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖₊ : ℝ≥0∞) ^ 2 := by
      intro x g
      rw [AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K) hψ.principalInvariant φ g (hper g) 1 x, nnnorm_mul, hψ1, one_mul]
    have hGZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (centralScalar (𝓞 K) K z * g)‖₊ : ℝ≥0∞) ^ 2 =
          (‖χ z‖₊ : ℝ≥0∞) ^ 2 * (‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖₊ : ℝ≥0∞) ^ 2 := by
      intro z g
      rw [iwasawa_whittakerCoefficient_centralScalar_mul K _ _ φ χ hχ 1 z g, nnnorm_mul, ENNReal.coe_mul, mul_pow]
    exact iwasawa_lintegral_indicator_tsum_eq_mul_lintegral_shadowWeight K c hc E hEm hE _ hGm hGN _ hχm hGZ

section SinglePlaceUnipotentsAndLocalCharacter

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm

variable {K}

private theorem neg_mem_idealBall {N : Ideal (𝓞 K)} {x : FiniteAdeleRing (𝓞 K) K}
    (hx : x ∈ idealBall (𝓞 K) K N) : -x ∈ idealBall (𝓞 K) K N := fun w => by
  rw [show (-x) w = -(x w) from rfl, Valuation.map_neg]
  exact hx w

private theorem neg_mem_integralFiniteAdeles' {x : FiniteAdeleRing (𝓞 K) K}
    (hx : x ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    -x ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := fun w => by
  rw [show (-x) w = -(x w) from rfl]
  exact neg_mem (hx w)

private theorem finAdeleSingleAt_mem_idealBall {N : Ideal (𝓞 K)} (hN : N ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ N) {y : v.adicCompletion K}
    (hy : Valued.v y ≤ 1) : finAdeleSingleAt K v y ∈ idealBall (𝓞 K) K N := fun w => by
  by_cases hw : w = v
  · subst hw
    rw [finAdeleSingleAt_apply_self, idealBound_eq_one_of_not_dvd hN hv]
    exact hy
  · rw [finAdeleSingleAt_apply_of_ne K v y hw]
    simp

private theorem unipotentGL2_mem_finiteIntegralGL2 {z : FiniteAdeleRing (𝓞 K) K}
    (hz : z ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) : unipotentGL2 z ∈ finiteIntegralGL2 (𝓞 K) K := by
  have hinv : (unipotentGL2 z)⁻¹ = unipotentGL2 (-z) :=
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  refine mem_finiteIntegralGL2_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;>
      simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, hz]
  · rw [hinv, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;>
      simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, neg_mem_integralFiniteAdeles' hz]

private theorem entry_conj_unipotent_sub_one_mem_idealBall {N : Ideal (𝓞 K)}
    {a : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (ha : a ∈ finiteIntegralGL2 (𝓞 K) K)
    {z : FiniteAdeleRing (𝓞 K) K} (hz : z ∈ idealBall (𝓞 K) K N) (i j : Fin 2) :
    ((a⁻¹ * unipotentGL2 z * a : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ idealBall (𝓞 K) K N := by
  have hai := (mem_finiteIntegralGL2_iff.1 ha).2
  have hav := (mem_finiteIntegralGL2_iff.1 ha).1
  have hid : ((a⁻¹ * unipotentGL2 z * a : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
      = ((a⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) i 0 * z
          * (a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 j := by
    have hone : (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
        = ((a⁻¹ * a : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j := by
      rw [inv_mul_cancel, Units.val_one]
    rw [hone, Units.val_mul, Units.val_mul, Units.val_mul, unipotentGL2_coe]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hid]
  exact mul_mem_idealBall_right (mul_mem_idealBall_left (hai i 0) hz) (hav 1 j)

private theorem conj_unipotent_mem_finiteLevelOne {N : Ideal (𝓞 K)}
    {a : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (ha : a ∈ finiteIntegralGL2 (𝓞 K) K)
    {z : FiniteAdeleRing (𝓞 K) K} (hz : z ∈ idealBall (𝓞 K) K N) :
    a⁻¹ * unipotentGL2 z * a ∈ finiteLevelOne (𝓞 K) K N := by
  have hzi : z ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := idealBall_subset_integralFiniteAdeles N hz
  have hm : a⁻¹ * unipotentGL2 z * a ∈ finiteIntegralGL2 (𝓞 K) K :=
    mul_mem (mul_mem (inv_mem ha) (unipotentGL2_mem_finiteIntegralGL2 hzi)) ha
  have hm' : a⁻¹ * unipotentGL2 (-z) * a ∈ finiteIntegralGL2 (𝓞 K) K :=
    mul_mem (mul_mem (inv_mem ha) (unipotentGL2_mem_finiteIntegralGL2 (neg_mem_integralFiniteAdeles' hzi)))
      ha
  have hminv : (a⁻¹ * unipotentGL2 z * a)⁻¹ = a⁻¹ * unipotentGL2 (-z) * a := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc a⁻¹ * unipotentGL2 z * a * (a⁻¹ * unipotentGL2 (-z) * a)
        = a⁻¹ * (unipotentGL2 z * (a * a⁻¹) * unipotentGL2 (-z)) * a := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [mul_inv_cancel, mul_one, ← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero, mul_one,
            inv_mul_cancel]
  have hball := entry_conj_unipotent_sub_one_mem_idealBall ha hz
  have hball' := entry_conj_unipotent_sub_one_mem_idealBall ha (neg_mem_idealBall hz)
  refine mem_finiteLevelOne_iff.2 ⟨⟨⟨(mem_finiteIntegralGL2_iff.1 hm).1, ?_⟩, ?_⟩, ?_⟩
  · simpa [Matrix.one_apply] using hball 1 0
  · simpa [Matrix.one_apply] using hball 1 1
  · rw [hminv]
    refine ⟨⟨(mem_finiteIntegralGL2_iff.1 hm').1, ?_⟩, ?_⟩
    · simpa [Matrix.one_apply] using hball' 1 0
    · simpa [Matrix.one_apply] using hball' 1 1

private theorem glFin_unipotentGL2 (a : AdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 a) = unipotentGL2 a.2 := by
  ext i j
  rw [glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

private theorem glArch_unipotentGL2 (a : AdeleRing (𝓞 K) K) :
    glArch (𝓞 K) K (unipotentGL2 a) = unipotentGL2 a.1 := by
  ext i j
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

private theorem conj_unipotent_adeleSingleAt_mem {N : Ideal (𝓞 K)} (hN : N ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ N) {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ adelicMaximalCompact K) {y : v.adicCompletion K} (hy : Valued.v y ≤ 1) :
    k⁻¹ * unipotentGL2 (adeleSingleAt K v y) * k
      ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, map_mul, map_mul, map_inv, glFin_unipotentGL2, adeleSingleAt_apply]
    exact conj_unipotent_mem_finiteLevelOne (glFin_mem_finiteIntegralGL2 hk)
      (finAdeleSingleAt_mem_idealBall hN hv hy)
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_unipotentGL2,
      adeleSingleAt_apply]
    simp

private theorem diagOne_mul_unipotentGL2 (t : (AdeleRing (𝓞 K) K)ˣ) (a : AdeleRing (𝓞 K) K) :
    diagOne t * unipotentGL2 a = unipotentGL2 ((t : AdeleRing (𝓞 K) K) * a) * diagOne t := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem finAdele_mul_apply (a b : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 K)) :
    (a * b) w = a w * b w := rfl

private theorem coe_mul_adeleSingleAt (t : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    (t : AdeleRing (𝓞 K) K) * adeleSingleAt K v y
      = adeleSingleAt K v ((t : AdeleRing (𝓞 K) K).2 v * y) := by
  rw [adeleSingleAt_apply, adeleSingleAt_apply]
  refine Prod.ext ?_ ?_
  · show (t : AdeleRing (𝓞 K) K).1 * 0 = 0
    exact mul_zero _
  show (t : AdeleRing (𝓞 K) K).2 * finAdeleSingleAt K v y = finAdeleSingleAt K v _
  ext w
  by_cases hw : w = v
  · subst hw
    simp only [finAdele_mul_apply, finAdeleSingleAt_apply_self]
  · simp only [finAdele_mul_apply, finAdeleSingleAt_apply_of_ne K v _ hw, mul_zero]

private theorem exp_one_le_of_one_lt {g : WithZero (Multiplicative ℤ)} (hg : 1 < g) :
    WithZero.exp (1 : ℤ) ≤ g := by
  have hg0 : g ≠ 0 := (zero_le'.trans_lt hg).ne'
  rw [← WithZero.exp_log hg0] at hg ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hg
  rw [WithZero.exp_le_exp]
  omega

private theorem count_differentIdeal_eq_zero_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K)) :
    FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
  classical
  by_cases hd : differentIdeal ℤ (𝓞 K) = 0
  · rw [hd, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot, FractionalIdeal.count_zero]
  · rw [FractionalIdeal.count_coe K v hd]
    exact_mod_cast not_not.mp ((Associates.count_ne_zero_iff_dvd hd v.irreducible).not.mpr hv)

private theorem addCharLevel_psiLocal_eq_zero_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K)) :
    LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0 := by
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K v]
  exact count_differentIdeal_eq_zero_of_not_dvd hv

private theorem exists_valued_le_exp_one_and_psiLocal_ne_one {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K)) :
    ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ psiLocal K v x ≠ 1 := by
  have hball : ∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → psiLocal K v x = 1 :=
    ⟨0, fun x hx => psiLocal_eq_one_of_mem_integers K v x
      ((mem_adicCompletionIntegers (𝓞 K) K v).2 (by rw [WithZero.exp_zero] at hx; exact hx))⟩
  obtain ⟨x, hx, hx1⟩ :=
    (forall_eq_one_and_exists_ne_one_of_addCharLevel K v (psiLocal K v) hball (psiLocal_ne_one K v)).2
  rw [addCharLevel_psiLocal_eq_zero_of_not_dvd hv, zero_add] at hx
  exact ⟨x, hx, hx1⟩

end SinglePlaceUnipotentsAndLocalCharacter

private theorem whittakerCoefficient_diagOne_mul_eq_zero_of_one_lt_valuation
    (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = φ (unipotentGL2 u * g))
    (hright : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (k : adelicMaximalCompact K)
    (t : (AdeleRing (𝓞 K) K)ˣ) (ht : 1 < Valued.v ((t : AdeleRing (𝓞 K) K).2 v)) :
    whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) = 0 := by

  have hN : N ≠ ⊥ := fun hbot => hv (hS v (by rw [hbot]; exact dvd_zero _))
  have hvN : ¬ v.asIdeal ∣ N := fun hdvd => hv (hS v hdvd)
  have hvd : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K) := fun hdvd => hv (hSψ v hdvd)

  obtain ⟨x, hx, hx1⟩ := exists_valued_le_exp_one_and_psiLocal_ne_one hvd
  have htv0 : (t : AdeleRing (𝓞 K) K).2 v ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht
    exact (not_lt_of_ge zero_le') ht

  have hy : Valued.v (x / (t : AdeleRing (𝓞 K) K).2 v) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ (hx.trans (exp_one_le_of_one_lt ht)) zero_le'
  have hty : (t : AdeleRing (𝓞 K) K).2 v * (x / (t : AdeleRing (𝓞 K) K).2 v) = x :=
    mul_div_cancel₀ x htv0

  have hu : (k : AdelicGL2 (𝓞 K) K)⁻¹
        * unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt K v (x / (t : AdeleRing (𝓞 K) K).2 v))
        * (k : AdelicGL2 (𝓞 K) K) ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K :=
    conj_unipotent_adeleSingleAt_mem hN hvN k.2 hy
  have hgu : diagOne t * (k : AdelicGL2 (𝓞 K) K)
        * ((k : AdelicGL2 (𝓞 K) K)⁻¹
          * unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt K v (x / (t : AdeleRing (𝓞 K) K).2 v))
          * (k : AdelicGL2 (𝓞 K) K))
      = unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt K v x)
          * (diagOne t * (k : AdelicGL2 (𝓞 K) K)) := by
    rw [mul_assoc (diagOne t), ← mul_assoc (k : AdelicGL2 (𝓞 K) K), ← mul_assoc (k : AdelicGL2 (𝓞 K) K),
      mul_inv_cancel, one_mul, ← mul_assoc, diagOne_mul_unipotentGL2, coe_mul_adeleSingleAt, hty, mul_assoc]

  have hinv : whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))
      = whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1
        (diagOne t * (k : AdelicGL2 (𝓞 K) K)
          * ((k : AdelicGL2 (𝓞 K) K)⁻¹
            * unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt K v (x / (t : AdeleRing (𝓞 K) K).2 v))
            * (k : AdelicGL2 (𝓞 K) K))) := by
    unfold whittakerCoefficient
    congr 1
    funext z
    rw [← mul_assoc (unipotentGL2 z) (diagOne t * (k : AdelicGL2 (𝓞 K) K)), hright _ _ hu]

  have hrow := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (NumberField.StandardAddChar.stdAddChar K)
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).principalInvariant φ
    (diagOne t * (k : AdelicGL2 (𝓞 K) K)) (fun β u => hper β u _) 1
    (NumberField.StandardAddChar.adeleSingleAt K v x)
  rw [hgu, hrow, map_one, one_mul] at hinv
  have hne : NumberField.StandardAddChar.stdAddChar K (NumberField.StandardAddChar.adeleSingleAt K v x) ≠ 1 := by
    rwa [NumberField.StandardAddChar.psiLocal_apply] at hx1
  have hzero : (NumberField.StandardAddChar.stdAddChar K (NumberField.StandardAddChar.adeleSingleAt K v x) - 1)
      * whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) = 0 := by
    rw [sub_mul, one_mul, ← hinv, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left (sub_ne_zero.2 hne)

private theorem heckeGen_eq_diagOne (v : HeightOneSpectrum (𝓞 K)) :
    heckeGen (𝓞 K) K v = diagOne (uniformizerIdele K v) := rfl

private theorem diagOne_mul_apply_one (a : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) (j : Fin 2) :
    ((diagOne a * g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 j =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply]

private theorem det_diagOne_mul (a : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    ((Matrix.GeneralLinearGroup.det (diagOne a * g) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      a * ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) := by
  rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    show ((diagOne a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.diagonal ![(a : AdeleRing (𝓞 K) K), 1] from rfl,
    Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_apply_snd (g : AdelicGL2 (𝓞 K) K) :
    (((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 =
      ((Matrix.GeneralLinearGroup.det (glFin (𝓞 K) K g) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    show ((glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) =
        (adeleFin (𝓞 K) K).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      from Matrix.ext fun i j => glFin_apply (𝓞 K) K g i j,
    ← RingHom.map_det]
  rfl

private theorem valued_det_apply_eq_one_and_max_eq_one {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hg : g ∈ finiteIntegralGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((((Matrix.GeneralLinearGroup.det g : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K)) v) = 1 ∧
      max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 0) v))
        (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) v)) = 1 := by
  have hint : ∀ g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K), g ∈ finiteIntegralGL2 (𝓞 K) K →
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K)) v) ≤ 1 := fun g hg => by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact valued_apply_le_one (sub_mem_integralFiniteAdeles
      (mul_mem_integralFiniteAdeles (hg.1.integral 0 0) (hg.1.integral 1 1))
      (mul_mem_integralFiniteAdeles (hg.1.integral 0 1) (hg.1.integral 1 0))) v
  have hprod : Valued.v ((((Matrix.GeneralLinearGroup.det g : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K)) v) *
      Valued.v ((((Matrix.GeneralLinearGroup.det g⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K)) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      coe_one_apply, map_one]
  have hdet : Valued.v ((((Matrix.GeneralLinearGroup.det g : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K)) v) = 1 :=
    le_antisymm (hint g hg)
      (calc (1 : _) = _ := hprod.symm
        _ ≤ _ * 1 := mul_le_mul_right (hint g⁻¹ (inv_mem hg)) _
        _ = _ := mul_one _)
  refine ⟨hdet, le_antisymm (max_le (valued_apply_le_one (hg.1.integral 1 0) v)
    (valued_apply_le_one (hg.1.integral 1 1) v)) (not_lt.mp fun hlt => ?_)⟩
  have h10 := (le_max_left _ _).trans_lt hlt
  have h11 := (le_max_right _ _).trans_lt hlt
  have hlt1 : Valued.v ((((Matrix.GeneralLinearGroup.det g : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K)) v) < 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, coe_sub_apply, coe_mul_apply, coe_mul_apply]
    refine Valuation.map_sub_lt _ ?_ ?_
    · rw [map_mul]
      calc _ ≤ 1 * Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) v) :=
            mul_le_mul_left (valued_apply_le_one (hg.1.integral 0 0) v) _
        _ < 1 := by rwa [one_mul]
    · rw [map_mul]
      calc _ ≤ 1 * Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 0) v) :=
            mul_le_mul_left (valued_apply_le_one (hg.1.integral 0 1) v) _
        _ < 1 := by rwa [one_mul]
  exact hlt1.ne hdet

private theorem valued_uniformizerIdele_pow_apply_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) :
    ∀ n : ℕ, Valued.v ((((uniformizerIdele K w ^ n : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v) = 1
  | 0 => by rw [pow_zero, Units.val_one, ← adeleFin_apply (𝓞 K) K, map_one, coe_one_apply, map_one]
  | n + 1 => by
    rw [pow_succ, Units.val_mul, ← adeleFin_apply (𝓞 K) K, map_mul, coe_mul_apply, map_mul, adeleFin_apply,
      adeleFin_apply, valued_uniformizerIdele_pow_apply_of_ne hvw n, one_mul, uniformizerIdele, Units.coe_map,
      finIncl_apply_snd,
      localUnit_apply_of_ne (R := 𝓞 K) (K := K) (v := w) (uniformizerUnit K w) hvw, map_one]

private theorem valued_prod_uniformizerIdele_pow_apply_of_notMem (e : HeightOneSpectrum (𝓞 K) → ℕ)
    {v : HeightOneSpectrum (𝓞 K)} (s : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ s) :
    Valued.v ((((∏ w ∈ s, uniformizerIdele K w ^ e w : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, ← adeleFin_apply (𝓞 K) K, map_one, coe_one_apply, map_one]
  | insert w s hw ih =>
    rw [Finset.mem_insert, not_or] at hv
    rw [Finset.prod_insert hw, Units.val_mul, ← adeleFin_apply (𝓞 K) K, map_mul, coe_mul_apply, map_mul,
      adeleFin_apply, adeleFin_apply, ih hv.2, mul_one]
    exact valued_uniformizerIdele_pow_apply_of_ne K hv.1 (e w)

private theorem norm_whittakerCoefficient_diagOne_prod_pow_mul_sq
    (D : Set (AdelicGL2 (𝓞 K) K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hrec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      ∀ y : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
            (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          ‖whittakerCoefficient K
              (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) φ 1 ((heckeGen (𝓞 K) K v) ^ m * y * k)‖ ^ 2 =
            ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
                (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2 *
              ‖whittakerCoefficient K
                  (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                  (NumberField.StandardAddChar.stdAddChar K) φ 1 (y * k)‖ ^ 2)
    (k : adelicMaximalCompact K) (e : HeightOneSpectrum (𝓞 K) → ℕ) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ v ∈ s, v ∉ S) (t : (AdeleRing (𝓞 K) K)ˣ) (ht : t ∈ unitsOff K S) :
    ‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1
        (diagOne ((∏ v ∈ s, uniformizerIdele K v ^ e v) * t) * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2 =
      (∏ v ∈ s, ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
          (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) (e v)‖ ^ 2) *
        ‖whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_mul, one_mul]
  | insert v₀ s hv₀ ih =>
    have hv₀S : v₀ ∉ S := hs v₀ (Finset.mem_insert_self v₀ s)
    have hs' : ∀ v ∈ s, v ∉ S := fun v hv => hs v (Finset.mem_insert_of_mem hv)
    have hk : glFin (𝓞 K) K (k : AdelicGL2 (𝓞 K) K) ∈ finiteIntegralGL2 (𝓞 K) K :=
      (mem_adelicMaximalCompact_iff.mp k.2).1
    have hy : Valued.v ((((Matrix.GeneralLinearGroup.det
          (diagOne ((∏ v ∈ s, uniformizerIdele K v ^ e v) * t) * (k : AdelicGL2 (𝓞 K) K)) :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v₀) =
        (max (Valued.v ((((diagOne ((∏ v ∈ s, uniformizerIdele K v ^ e v) * t) * (k : AdelicGL2 (𝓞 K) K) :
              AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v₀))
          (Valued.v ((((diagOne ((∏ v ∈ s, uniformizerIdele K v ^ e v) * t) * (k : AdelicGL2 (𝓞 K) K) :
              AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v₀))) ^ 2 := by
      obtain ⟨hdet, hmax⟩ := valued_det_apply_eq_one_and_max_eq_one K hk v₀
      rw [diagOne_mul_apply_one, diagOne_mul_apply_one, ← glFin_apply (𝓞 K) K (k : AdelicGL2 (𝓞 K) K) 1 0,
        ← glFin_apply (𝓞 K) K (k : AdelicGL2 (𝓞 K) K) 1 1, hmax, one_pow, det_diagOne_mul,
        ← adeleFin_apply (𝓞 K) K, map_mul, coe_mul_apply, map_mul, adeleFin_apply, adeleFin_apply, det_apply_snd,
        hdet, mul_one, Units.val_mul, ← adeleFin_apply (𝓞 K) K, map_mul, coe_mul_apply, map_mul, adeleFin_apply,
        adeleFin_apply, ht v₀ hv₀S, mul_one]
      exact valued_prod_uniformizerIdele_pow_apply_of_notMem K e s hv₀
    have h := hrec v₀ hv₀S 1 (map_one _) _ hy (e v₀)
    rw [mul_one, mul_one, ← mul_assoc] at h
    rw [Finset.prod_insert hv₀, Finset.prod_insert hv₀, mul_assoc (uniformizerIdele K v₀ ^ e v₀),
      map_mul diagOne (uniformizerIdele K v₀ ^ e v₀), map_pow diagOne (uniformizerIdele K v₀) (e v₀),
      ← heckeGen_eq_diagOne K v₀, h, ih hs', ← mul_assoc]

private theorem norm_whittakerCoefficient_diagOne_idealIdele_mul_sq
    (D : Set (AdelicGL2 (𝓞 K) K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hrec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      ∀ y : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
            (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          ‖whittakerCoefficient K
              (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) φ 1 ((heckeGen (𝓞 K) K v) ^ m * y * k)‖ ^ 2 =
            ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
                (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2 *
              ‖whittakerCoefficient K
                  (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                  (NumberField.StandardAddChar.stdAddChar K) φ 1 (y * k)‖ ^ 2)
    (k : adelicMaximalCompact K) (t : (AdeleRing (𝓞 K) K)ˣ) (ht : t ∈ unitsOff K S) (𝔫 : GoodIdeal K S) :
    ‖whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1
        (diagOne (idealIdele K 𝔫.1 * t) * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2 =
      ‖recValue K Ψ 𝔫.1‖ ^ 2 *
        ‖whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2 := by
  classical
  have h0 : 𝔫.1 ≠ 0 := 𝔫.2.1
  have hmem : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ (Ideal.finite_factors h0).toFinset ↔ v.asIdeal ∣ 𝔫.1 :=
    fun v => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hcount : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ (Ideal.finite_factors h0).toFinset →
      (Associates.mk v.asIdeal).count (Associates.mk 𝔫.1).factors = 0 := fun v hv =>
    not_not.mp ((Associates.count_ne_zero_iff_dvd h0 v.irreducible).not.mpr ((hmem v).not.mp hv))
  have hS : ∀ v ∈ (Ideal.finite_factors h0).toFinset, v ∉ S := fun v hv hvS => 𝔫.2.2 v hvS ((hmem v).mp hv)
  have hsub₁ : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      uniformizerIdele K v ^ (Associates.mk v.asIdeal).count (Associates.mk 𝔫.1).factors) ⊆
        ↑(Ideal.finite_factors h0).toFinset := fun v hv => by
    rw [Finset.mem_coe]
    by_contra hv'
    exact hv (by simp only [hcount v hv', pow_zero])
  have hsub₂ : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v)
        ((Associates.mk v.asIdeal).count (Associates.mk 𝔫.1).factors)) ⊆ ↑(Ideal.finite_factors h0).toFinset :=
    fun v hv => by
      rw [Finset.mem_coe]
      by_contra hv'
      exact hv (by simp only [hcount v hv', UnramifiedWhittaker.heckeRecursionSeq])
  unfold idealIdele recValue
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub₁, finprod_eq_prod_of_mulSupport_subset _ hsub₂, norm_prod,
    ← Finset.prod_pow]
  exact norm_whittakerCoefficient_diagOne_prod_pow_mul_sq K D S Ψ φ hrec k _ _ hS t ht

section IdelePartitionByGoodIdeals

open scoped Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_ord_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.Idele.ord K v t = 0 ↔ Valued.v ((t : AdeleRing (𝓞 K) K).2 v) = 1 :=
  (NumberField.Idele.ord_eq_zero_iff K v t).trans
    (IsDedekindDomain.FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one v _)

private theorem idelePartition_mem_unitsOff_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (t : (AdeleRing (𝓞 K) K)ˣ) :
    t ∈ unitsOff K S ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → NumberField.Idele.ord K v t = 0 :=
  forall_congr' fun v => imp_congr_right fun _ => (idelePartition_ord_eq_zero_iff K v t).symm

private theorem idelePartition_unitsOff_eq (S : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsOff K S =
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) :
        Set (AdeleRing (𝓞 K) K)ˣ) := by
  ext t
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff, idelePartition_mem_unitsOff_iff]
  exact forall_congr' fun v => imp_congr_right fun _ => NumberField.Idele.ord_eq_zero_iff K v t

private theorem idelePartition_measurableSet_unitsOff (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSet (unitsOff K S) := by
  rw [idelePartition_unitsOff_eq]
  exact (NumberField.Idele.isOpen_unitIdelesOutside K (↑S : Set (HeightOneSpectrum (𝓞 K)))).measurableSet

private def idelePartition_piece (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S) :
    Set (AdeleRing (𝓞 K) K)ˣ :=
  (fun t : (AdeleRing (𝓞 K) K)ˣ => (idealIdele K 𝔫.1)⁻¹ * t) ⁻¹' unitsOff K S

private theorem idelePartition_measurableSet_piece (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S) :
    MeasurableSet (idelePartition_piece K S 𝔫) :=
  (idelePartition_measurableSet_unitsOff K S).preimage (continuous_const.mul continuous_id).measurable

private theorem idelePartition_countable_goodIdeal (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Countable (GoodIdeal K S) := by
  have hu : (⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n}) = Set.univ :=
    Set.eq_univ_of_forall fun I => Set.mem_iUnion.mpr ⟨Ideal.absNorm I, Set.mem_setOf_eq ▸ rfl⟩
  have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
    rw [← hu]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_eq n).countable
  haveI : Countable (Ideal (𝓞 K)) := Set.countable_univ_iff.mp hc
  unfold GoodIdeal
  infer_instance

private theorem idelePartition_ord_prod (v : HeightOneSpectrum (𝓞 K)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (f : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.Idele.ord K v (∏ w ∈ s, f w) = ∑ w ∈ s, NumberField.Idele.ord K v (f w) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, NumberField.Idele.ord_one]
  | insert w s hw ih => rw [Finset.prod_insert hw, Finset.sum_insert hw, NumberField.Idele.ord_mul, ih]

private theorem idelePartition_ord_pow (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) :
    NumberField.Idele.ord K v (a ^ n) = n * NumberField.Idele.ord K v a := by
  induction n with
  | zero => rw [pow_zero, NumberField.Idele.ord_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, NumberField.Idele.ord_mul, ih, Nat.cast_succ, add_mul, one_mul]

private theorem idelePartition_ord_idealIdele (v : HeightOneSpectrum (𝓞 K)) {𝔫 : Ideal (𝓞 K)} (h0 : 𝔫 ≠ 0) :
    NumberField.Idele.ord K v (idealIdele K 𝔫) = ((Associates.mk v.asIdeal).count (Associates.mk 𝔫).factors : ℤ) := by
  have hcount : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ (Ideal.finite_factors h0).toFinset →
      (Associates.mk w.asIdeal).count (Associates.mk 𝔫).factors = 0 := fun w hw =>
    not_not.mp ((Associates.count_ne_zero_iff_dvd h0 w.irreducible).not.mpr
      (by rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw))
  have hsub : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 K) =>
      uniformizerIdele K w ^ (Associates.mk w.asIdeal).count (Associates.mk 𝔫).factors) ⊆
        ↑(Ideal.finite_factors h0).toFinset := fun w hw => by
    rw [Finset.mem_coe]
    by_contra hw'
    exact hw (by simp only [hcount w hw', pow_zero])
  unfold idealIdele
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, idelePartition_ord_prod, Finset.sum_eq_single v]
  · rw [idelePartition_ord_pow, NumberField.Idele.ord_uniformizerIdele_self, mul_one]
  · intro w _ hwv
    rw [idelePartition_ord_pow, NumberField.Idele.ord_uniformizerIdele_of_ne K (Ne.symm hwv), mul_zero]
  · intro hv
    rw [hcount v hv, pow_zero, NumberField.Idele.ord_one]

private theorem idelePartition_mem_piece_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S)
    (t : (AdeleRing (𝓞 K) K)ˣ) :
    t ∈ idelePartition_piece K S 𝔫 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      NumberField.Idele.ord K v t = ((Associates.mk v.asIdeal).count (Associates.mk 𝔫.1).factors : ℤ) := by
  rw [idelePartition_piece, Set.mem_preimage, idelePartition_mem_unitsOff_iff]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [NumberField.Idele.ord_mul, NumberField.Idele.ord_inv, idelePartition_ord_idealIdele K v 𝔫.2.1,
    neg_add_eq_zero, eq_comm]

private theorem idelePartition_goodIdeal_ext (S : Finset (HeightOneSpectrum (𝓞 K))) {𝔫 𝔪 : GoodIdeal K S}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (Associates.mk v.asIdeal).count (Associates.mk 𝔫.1).factors =
        (Associates.mk v.asIdeal).count (Associates.mk 𝔪.1).factors) : 𝔫 = 𝔪 := by
  have hall : ∀ v : HeightOneSpectrum (𝓞 K),
      (Associates.mk v.asIdeal).count (Associates.mk 𝔫.1).factors =
        (Associates.mk v.asIdeal).count (Associates.mk 𝔪.1).factors := fun v => by
    by_cases hv : v ∈ S
    · rw [not_not.mp ((Associates.count_ne_zero_iff_dvd 𝔫.2.1 v.irreducible).not.mpr (𝔫.2.2 v hv)),
        not_not.mp ((Associates.count_ne_zero_iff_dvd 𝔪.2.1 v.irreducible).not.mpr (𝔪.2.2 v hv))]
    · exact h v hv
  apply Subtype.ext
  rw [← Ideal.finprod_heightOneSpectrum_factorization 𝔫.2.1, ← Ideal.finprod_heightOneSpectrum_factorization 𝔪.2.1]
  exact finprod_congr fun v => by
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hall v]

private theorem idelePartition_pairwise_disjoint_piece (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise (Function.onFun Disjoint (idelePartition_piece K S)) := fun 𝔫 𝔪 hne => by
  show Disjoint (idelePartition_piece K S 𝔫) (idelePartition_piece K S 𝔪)
  rw [Set.disjoint_left]
  intro t h𝔫 h𝔪
  rw [idelePartition_mem_piece_iff] at h𝔫 h𝔪
  exact hne (idelePartition_goodIdeal_ext K S fun v hv => by exact_mod_cast (h𝔫 v hv).symm.trans (h𝔪 v hv))

private theorem idelePartition_finite_setOf_ord_ne_zero (t : (AdeleRing (𝓞 K) K)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) | NumberField.Idele.ord K v t ≠ 0}.Finite := by
  have hu : IsUnit ((t : AdeleRing (𝓞 K) K).2) := ⟨NumberField.AdeleRing.finitePartUnits (𝓞 K) K t, rfl⟩
  refine (Filter.eventually_cofinite.mp (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp hu).2).subset fun v hv => ?_
  exact fun h1 => hv ((idelePartition_ord_eq_zero_iff K v t).mpr h1)

private theorem idelePartition_count_prod_pow (s : Finset (HeightOneSpectrum (𝓞 K))) (e : HeightOneSpectrum (𝓞 K) → ℕ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((Associates.mk v.asIdeal).count (Associates.mk (∏ w ∈ s, w.asIdeal ^ e w)).factors : ℤ) =
      if v ∈ s then (e v : ℤ) else 0 := by
  have hne : (∏ w ∈ s, w.asIdeal ^ e w : Ideal (𝓞 K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ w.ne_bot
  rw [← FractionalIdeal.count_coe K v hne]
  have hcoe : ((∏ w ∈ s, w.asIdeal ^ e w : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ w ∈ s, (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ e w := by
    show FractionalIdeal.coeIdealHom (𝓞 K)⁰ K (∏ w ∈ s, w.asIdeal ^ e w) = _
    rw [map_prod]
    exact Finset.prod_congr rfl fun w _ => map_pow (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) w.asIdeal (e w)
  rw [hcoe, FractionalIdeal.count_prod K v _ _ fun w _ =>
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)]
  simp_rw [FractionalIdeal.count_pow]
  by_cases hv : v ∈ s
  · rw [if_pos hv, Finset.sum_eq_single v]
    · rw [FractionalIdeal.count_self, mul_one]
    · intro w _ hwv
      rw [FractionalIdeal.count_maximal_coprime K v hwv, mul_zero]
    · exact fun h => (h hv).elim
  · rw [if_neg hv]
    exact Finset.sum_eq_zero fun w hw =>
      by rw [FractionalIdeal.count_maximal_coprime K v (ne_of_mem_of_not_mem hw hv), mul_zero]

private theorem idelePartition_exists_mem_piece (S : Finset (HeightOneSpectrum (𝓞 K))) (t : (AdeleRing (𝓞 K) K)ˣ)
    (ht : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → 0 ≤ NumberField.Idele.ord K v t) :
    ∃ 𝔫 : GoodIdeal K S, t ∈ idelePartition_piece K S 𝔫 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      T = ((idelePartition_finite_setOf_ord_ne_zero K t).toFinset.filter fun v => v ∉ S) :=
    ⟨_, rfl⟩
  have hmemT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ T ↔ NumberField.Idele.ord K v t ≠ 0 ∧ v ∉ S := fun v => by
    rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (𝓞 K) → ℕ, e = fun v => (NumberField.Idele.ord K v t).toNat := ⟨_, rfl⟩
  have hcount : ∀ v : HeightOneSpectrum (𝓞 K),
      ((Associates.mk v.asIdeal).count (Associates.mk (∏ w ∈ T, w.asIdeal ^ e w)).factors : ℤ) =
        if v ∈ S then 0 else NumberField.Idele.ord K v t := fun v => by
    rw [idelePartition_count_prod_pow]
    by_cases hvS : v ∈ S
    · rw [if_pos hvS, if_neg fun hvT => ((hmemT v).mp hvT).2 hvS]
    · rw [if_neg hvS]
      by_cases hv0 : NumberField.Idele.ord K v t = 0
      · rw [hv0, if_neg fun hvT => ((hmemT v).mp hvT).1 hv0]
      · rw [if_pos ((hmemT v).mpr ⟨hv0, hvS⟩), he, Int.toNat_of_nonneg (ht v hvS)]
  refine ⟨⟨∏ w ∈ T, w.asIdeal ^ e w, Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ w.ne_bot,
    fun v hv hdvd => ?_⟩,
    ?_⟩
  · have h := hcount v
    rw [if_pos hv] at h
    exact (Associates.count_ne_zero_iff_dvd (Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ w.ne_bot)
      v.irreducible).mpr hdvd (by exact_mod_cast h)
  · rw [idelePartition_mem_piece_iff]
    intro v hv
    rw [hcount v, if_neg hv]

private theorem idelePartition_exists_one_lt_of_forall_notMem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t : (AdeleRing (𝓞 K) K)ˣ)
    (h : ∀ 𝔫 : GoodIdeal K S, t ∉ idelePartition_piece K S 𝔫) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ 1 < Valued.v ((t : AdeleRing (𝓞 K) K).2 v) := by
  by_contra hcon
  refine (fun ⟨𝔫, h𝔫⟩ => h 𝔫 h𝔫) (idelePartition_exists_mem_piece K S t fun v hv => ?_)
  by_contra hneg
  refine hcon ⟨v, hv, ?_⟩
  rw [NumberField.Idele.valued_snd_eq_exp_neg_ord, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  exact neg_pos.mpr (lt_of_not_ge hneg)

private theorem idelePartition_lintegral_eq_tsum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (F : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (hF : ∀ t : (AdeleRing (𝓞 K) K)ˣ, (∀ 𝔫 : GoodIdeal K S, t ∉ idelePartition_piece K S 𝔫) → F t = 0) :
    ∫⁻ t, F t ∂(NumberField.Idele.idelicHaar K) =
      ∑' 𝔫 : GoodIdeal K S, ∫⁻ t in idelePartition_piece K S 𝔫, F t ∂(NumberField.Idele.idelicHaar K) := by
  haveI := idelePartition_countable_goodIdeal K S
  have hU : MeasurableSet (⋃ 𝔫 : GoodIdeal K S, idelePartition_piece K S 𝔫) :=
    MeasurableSet.iUnion fun 𝔫 => idelePartition_measurableSet_piece K S 𝔫
  rw [← lintegral_add_compl F hU,
    lintegral_iUnion (idelePartition_measurableSet_piece K S) (idelePartition_pairwise_disjoint_piece K S),
    setLIntegral_congr_fun hU.compl (fun t ht => hF t fun 𝔫 h𝔫 => ht (Set.mem_iUnion.mpr ⟨𝔫, h𝔫⟩)), lintegral_zero,
    add_zero]

private theorem idelePartition_setLIntegral_piece (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S)
    (F : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) :
    ∫⁻ t in idelePartition_piece K S 𝔫, F t ∂(NumberField.Idele.idelicHaar K) =
      ∫⁻ t in unitsOff K S, F (idealIdele K 𝔫.1 * t) ∂(NumberField.Idele.idelicHaar K) := by
  rw [← lintegral_indicator (idelePartition_measurableSet_piece K S 𝔫),
    ← lintegral_indicator (idelePartition_measurableSet_unitsOff K S),
    ← lintegral_mul_left_eq_self (fun t => (idelePartition_piece K S 𝔫).indicator F t) (idealIdele K 𝔫.1)]
  refine lintegral_congr fun t => ?_
  simp only [Set.indicator, idelePartition_piece, Set.mem_preimage, inv_mul_cancel_left]

private theorem idelePartition_ideleNorm_idealIdele_mul {𝔫 : Ideal (𝓞 K)} (h0 : 𝔫 ≠ 0) (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫 * t) =
      NumberField.TateGlobal.ideleNorm K t / ((Ideal.absNorm 𝔫 : ℕ) : ℝ) := by
  have hcount : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ (Ideal.finite_factors h0).toFinset →
      (Associates.mk w.asIdeal).count (Associates.mk 𝔫).factors = 0 := fun w hw =>
    not_not.mp ((Associates.count_ne_zero_iff_dvd h0 w.irreducible).not.mpr
      (by rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw))
  have hsub : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 K) =>
      uniformizerIdele K w ^ (Associates.mk w.asIdeal).count (Associates.mk 𝔫).factors) ⊆
        ↑(Ideal.finite_factors h0).toFinset := fun w hw => by
    rw [Finset.mem_coe]
    by_contra hw'
    exact hw (by simp only [hcount w hw', pow_zero])
  have hsub' : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 K) => w.maxPowDividing 𝔫) ⊆
      ↑(Ideal.finite_factors h0).toFinset :=
    fun w hw => by
      rw [Finset.mem_coe]
      by_contra hw'
      exact hw (by simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount w hw', pow_zero])
  have hnorm : ((Ideal.absNorm 𝔫 : ℕ) : ℝ) = ∏ w ∈ (Ideal.finite_factors h0).toFinset,
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (Associates.mk w.asIdeal).count (Associates.mk 𝔫).factors := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization h0, finprod_eq_prod_of_mulSupport_subset _ hsub']
    rw [map_prod, Nat.cast_prod]
    exact Finset.prod_congr rfl fun w _ => by
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow]
  have hprod : ∀ s : Finset (HeightOneSpectrum (𝓞 K)), ∀ f : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ,
      NumberField.TateGlobal.ideleNorm K (∏ w ∈ s, f w) = ∏ w ∈ s, NumberField.TateGlobal.ideleNorm K (f w) := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      have h := NumberField.TateGlobal.ideleNorm_mul (F := K) 1 1
      rw [mul_one] at h
      exact (mul_right_eq_self₀.mp h.symm).resolve_right (NumberField.TateGlobal.ideleNorm_pos 1).ne'
    | insert w s hw ih => rw [Finset.prod_insert hw, Finset.prod_insert hw, NumberField.TateGlobal.ideleNorm_mul, ih]
  have hpow : ∀ (a : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ),
      NumberField.TateGlobal.ideleNorm K (a ^ n) = NumberField.TateGlobal.ideleNorm K a ^ n := by
    intro a n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      have h := NumberField.TateGlobal.ideleNorm_mul (F := K) 1 1
      rw [mul_one] at h
      exact (mul_right_eq_self₀.mp h.symm).resolve_right (NumberField.TateGlobal.ideleNorm_pos 1).ne'
    | succ n ih => rw [pow_succ, NumberField.TateGlobal.ideleNorm_mul, ih, pow_succ]
  rw [NumberField.TateGlobal.ideleNorm_mul, hnorm, div_eq_mul_inv, mul_comm, ← Finset.prod_inv_distrib]
  congr 1
  unfold idealIdele
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, hprod]
  exact Finset.prod_congr rfl fun w _ => by
    rw [hpow, NumberField.TateGlobal.ideleNorm_uniformizerIdele, inv_pow]

private theorem idelePartition_nnnorm_sq_eq {a b c : ℂ} (h : ‖a‖ ^ 2 = ‖b‖ ^ 2 * ‖c‖ ^ 2) :
    (‖a‖₊ : ℝ≥0∞) ^ 2 = (‖b‖₊ : ℝ≥0∞) ^ 2 * (‖c‖₊ : ℝ≥0∞) ^ 2 := by
  have h' : ‖a‖₊ ^ 2 = ‖b‖₊ ^ 2 * ‖c‖₊ ^ 2 :=
    NNReal.coe_injective (by simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using h)
  rw [← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul, h']

private theorem idelePartition_ofReal_inv_ideleNorm_idealIdele_mul {𝔫 : Ideal (𝓞 K)} (h0 : 𝔫 ≠ 0)
    (t : (AdeleRing (𝓞 K) K)ˣ) :
    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫 * t))⁻¹) =
      ((Ideal.absNorm 𝔫 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) := by
  rw [idelePartition_ideleNorm_idealIdele_mul K h0, inv_div, div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

end IdelePartitionByGoodIdeals

private theorem lintegral_nnnorm_whittakerCoefficient_diagOne_sq_mul_eq_tsum_goodIdeal
    (D : Set (AdelicGL2 (𝓞 K) K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hrec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      ∀ y : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
            (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          ‖whittakerCoefficient K
              (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) φ 1 ((heckeGen (𝓞 K) K v) ^ m * y * k)‖ ^ 2 =
            ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
                (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2 *
              ‖whittakerCoefficient K
                  (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                  (NumberField.StandardAddChar.stdAddChar K) φ 1 (y * k)‖ ^ 2)
    (hvan : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ (k : adelicMaximalCompact K) (t : (AdeleRing (𝓞 K) K)ˣ),
      1 < Valued.v ((t : AdeleRing (𝓞 K) K).2 v) →
        whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) = 0)
    (k : adelicMaximalCompact K) (ω : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) :
    ∫⁻ t, (‖whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * ω t ∂(NumberField.Idele.idelicHaar K) =
      ∑' 𝔫 : GoodIdeal K S, (‖recValue K Ψ 𝔫.1‖₊ : ℝ≥0∞) ^ 2 * ((Ideal.absNorm 𝔫.1 : ℕ) : ℝ≥0∞) *
        ∫⁻ t in unitsOff K S, (‖whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * ω (idealIdele K 𝔫.1 * t)
        ∂(NumberField.Idele.idelicHaar K) := by
  set W : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun t => whittakerCoefficient K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) with hW
  show ∫⁻ t, (‖W t‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * ω t
      ∂(NumberField.Idele.idelicHaar K) =
    ∑' 𝔫 : GoodIdeal K S, (‖recValue K Ψ 𝔫.1‖₊ : ℝ≥0∞) ^ 2 * ((Ideal.absNorm 𝔫.1 : ℕ) : ℝ≥0∞) *
      ∫⁻ t in unitsOff K S, (‖W t‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) *
        ω (idealIdele K 𝔫.1 * t)
        ∂(NumberField.Idele.idelicHaar K)

  have hS2 : ∀ (𝔫 : GoodIdeal K S) (t : (AdeleRing (𝓞 K) K)ˣ), t ∈ unitsOff K S →
      ‖W (idealIdele K 𝔫.1 * t)‖ ^ 2 = ‖recValue K Ψ 𝔫.1‖ ^ 2 * ‖W t‖ ^ 2 := fun 𝔫 t ht =>
    norm_whittakerCoefficient_diagOne_idealIdele_mul_sq K D S Ψ φ hrec k t ht 𝔫
  have hvanish : ∀ t : (AdeleRing (𝓞 K) K)ˣ, (∀ 𝔫 : GoodIdeal K S, t ∉ idelePartition_piece K S 𝔫) →
      (‖W t‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * ω t = 0 := fun t ht => by
    obtain ⟨v, hv, h1⟩ := idelePartition_exists_one_lt_of_forall_notMem K S t ht
    have hW0 : W t = 0 := hvan v hv k t h1
    rw [hW0, nnnorm_zero, ENNReal.coe_zero, zero_pow two_ne_zero, zero_mul, zero_mul]
  rw [idelePartition_lintegral_eq_tsum K S _ hvanish]
  refine tsum_congr fun 𝔫 => ?_
  rw [idelePartition_setLIntegral_piece]
  have hpt : Set.EqOn
      (fun t : (AdeleRing (𝓞 K) K)ˣ =>
        (‖W (idealIdele K 𝔫.1 * t)‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫.1 * t))⁻¹) * ω (idealIdele K 𝔫.1 * t))
      (fun t : (AdeleRing (𝓞 K) K)ˣ =>
        (‖recValue K Ψ 𝔫.1‖₊ : ℝ≥0∞) ^ 2 * ((Ideal.absNorm 𝔫.1 : ℕ) : ℝ≥0∞) *
        ((‖W t‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * ω (idealIdele K 𝔫.1 * t)))
      (unitsOff K S) := fun t ht => by
    dsimp only
    rw [idelePartition_nnnorm_sq_eq (hS2 𝔫 t ht), idelePartition_ofReal_inv_ideleNorm_idealIdele_mul K 𝔫.2.1]
    ring
  rw [setLIntegral_congr_fun (idelePartition_measurableSet_unitsOff K S) hpt,
    lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (ENNReal.natCast_ne_top _))]

section BalancingUnit

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem

variable {F : Type} [Field F] [NumberField F]

private theorem exists_forall_mem_fundamentalCone_abs_deviation_le :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ fundamentalCone F, ∀ w : InfinitePlace F,
      |Real.log (normAtPlace w x) - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹| ≤ R := by
  classical
  obtain ⟨R₀, hR₀⟩ :=
    (ZSpan.fundamentalDomain_isBounded ((basisUnitLattice F).ofZLatticeBasis ℝ _)).exists_norm_le
  refine ⟨(Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0, by positivity, fun x hx w => ?_⟩
  have hcone : logMap x ∈ ZSpan.fundamentalDomain ((basisUnitLattice F).ofZLatticeBasis ℝ _) := hx.1
  have hlog : ‖logMap x‖ ≤ R₀ := hR₀ _ hcone

  have hcomp : ∀ v : {v : InfinitePlace F // v ≠ w₀},
      |(mult v.1 : ℝ) * (Real.log (normAtPlace v.1 x)
        - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹)| ≤ max R₀ 0 := by
    intro v
    have h1 : ‖logMap x v‖ ≤ ‖logMap x‖ := norm_le_pi_norm (logMap x) v
    rw [logMap_apply, Real.norm_eq_abs] at h1
    exact h1.trans (hlog.trans (le_max_left _ _))

  have hne : ∀ v : InfinitePlace F, normAtPlace v x ≠ 0 :=
    fun v => (fundamentalCone.normAtPlace_pos_of_mem hx v).ne'
  have hfinrank : (Module.finrank ℚ F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hsum : ∑ v : InfinitePlace F, (mult v : ℝ) * (Real.log (normAtPlace v x)
      - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹) = 0 := by
    have hprod : Real.log (mixedEmbedding.norm x)
        = ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (normAtPlace v x) := by
      rw [mixedEmbedding.norm_apply, Real.log_prod (fun v _ => pow_ne_zero _ (hne v))]
      simp only [Real.log_pow]
    have hmult : ∑ v : InfinitePlace F, (mult v : ℝ) = (Module.finrank ℚ F : ℝ) := by
      exact_mod_cast sum_mult_eq (K := F)
    have hlin : ∑ v : InfinitePlace F, (mult v : ℝ) * (Real.log (normAtPlace v x)
          - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹)
        = (∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (normAtPlace v x))
          - (∑ v : InfinitePlace F, (mult v : ℝ))
            * (Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    have hcancel : (Module.finrank ℚ F : ℝ)
          * (Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹)
        = Real.log (mixedEmbedding.norm x) := by
      field_simp
    rw [hlin, ← hprod, hmult, hcancel, sub_self]

  set dev : InfinitePlace F → ℝ := fun v => Real.log (normAtPlace v x)
    - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹ with hdev
  have hweighted : |(mult w : ℝ) * dev w| ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := by
    by_cases hw : w = w₀
    ·
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset (InfinitePlace F))
        (fun v => (mult v : ℝ) * dev v) (Finset.mem_univ w)
      have hzero : ∑ v, (mult v : ℝ) * dev v = 0 := hsum
      have hw_eq : (mult w : ℝ) * dev w = - ∑ v ∈ Finset.univ.erase w, (mult v : ℝ) * dev v := by
        linarith [hsplit, hzero]
      rw [hw_eq, abs_neg]
      calc |∑ v ∈ Finset.univ.erase w, (mult v : ℝ) * dev v|
          ≤ ∑ v ∈ Finset.univ.erase w, |(mult v : ℝ) * dev v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v ∈ Finset.univ.erase w, max R₀ 0 := by
            refine Finset.sum_le_sum fun v hv => ?_
            have hv' : v ≠ w₀ := hw ▸ (Finset.mem_erase.mp hv).1
            exact hcomp ⟨v, hv'⟩
        _ = ((Finset.univ.erase w).card : ℝ) * max R₀ 0 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := by
            gcongr
            exact_mod_cast Finset.card_le_univ _
    · calc |(mult w : ℝ) * dev w| ≤ max R₀ 0 := hcomp ⟨w, hw⟩
        _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := by
            have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
              exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
            exact le_mul_of_one_le_left (le_max_right _ _) hcard
  have hmult_one : (1 : ℝ) ≤ mult w := one_le_mult
  calc |dev w| ≤ (mult w : ℝ) * |dev w| := le_mul_of_one_le_left (abs_nonneg _) hmult_one
    _ = |(mult w : ℝ) * dev w| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < mult w)]
    _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := hweighted

private theorem exists_forall_exists_unit_forall_mul_le_mul :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ h : InfinitePlace F → ℝ, (∀ w, 0 < h w) →
      ∃ u : (𝓞 F)ˣ, ∀ w w' : InfinitePlace F,
        (w (algebraMap (𝓞 F) F u)) ^ 2 * h w ≤ κ * ((w' (algebraMap (𝓞 F) F u)) ^ 2 * h w') := by
  obtain ⟨R, hR, hdev⟩ := exists_forall_mem_fundamentalCone_abs_deviation_le (F := F)
  refine ⟨Real.exp (4 * R), Real.one_le_exp_iff.mpr (by positivity), fun h hpos => ?_⟩

  set y : mixedSpace F := mixedSpaceOfRealSpace (fun w => Real.sqrt (h w)) with hy
  have hyw : ∀ w : InfinitePlace F, normAtPlace w y = Real.sqrt (h w) :=
    fun w => normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _)
  have hynorm : mixedEmbedding.norm y ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr fun w => by rw [hyw]; exact (Real.sqrt_pos.mpr (hpos w)).ne'
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem hynorm
  refine ⟨u, fun w w' => ?_⟩

  have hnorm_smul : ∀ v : InfinitePlace F,
      normAtPlace v (u • y) = v (algebraMap (𝓞 F) F u) * Real.sqrt (h v) := by
    intro v
    rw [unitSMul_smul, map_mul, normAtPlace_apply, hyw]
  have hpos_smul : ∀ v : InfinitePlace F, 0 < normAtPlace v (u • y) :=
    fundamentalCone.normAtPlace_pos_of_mem hu

  have hw := hdev _ hu w
  have hw' := hdev _ hu w'
  have hlog : Real.log (normAtPlace w (u • y)) ≤ Real.log (normAtPlace w' (u • y)) + 2 * R := by
    have h1 := (abs_le.mp hw).2
    have h2 := (abs_le.mp hw').1
    linarith
  have hle : normAtPlace w (u • y) ≤ Real.exp (2 * R) * normAtPlace w' (u • y) := by
    have h3 : normAtPlace w (u • y) = Real.exp (Real.log (normAtPlace w (u • y))) :=
      (Real.exp_log (hpos_smul w)).symm
    have h4 : normAtPlace w' (u • y) = Real.exp (Real.log (normAtPlace w' (u • y))) :=
      (Real.exp_log (hpos_smul w')).symm
    rw [h3, h4, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

  have hsq : normAtPlace w (u • y) ^ 2 ≤ (Real.exp (2 * R) * normAtPlace w' (u • y)) ^ 2 :=
    pow_le_pow_left₀ (normAtPlace_nonneg _ _) hle 2
  rw [hnorm_smul, hnorm_smul, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hpos w).le,
    Real.sq_sqrt (hpos w').le] at hsq
  have h4 : Real.exp (4 * R) = Real.exp (2 * R) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [h4]
  exact hsq

private theorem exists_one_le_forall_le_forall_exists_unit_forall_le_mul_and_forall_mul_le_mul :
    ∃ κ₀ : ℝ, 1 ≤ κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ → ∀ (c : ℝ) (h : InfinitePlace F → ℝ), (∀ w, 0 < h w) → (∀ w, c ≤ h w) →
      ∃ u : (𝓞 F)ˣ, (∀ w : InfinitePlace F, c ≤ (w (algebraMap (𝓞 F) F u)) ^ 2 * h w) ∧
        ∀ w w' : InfinitePlace F,
          (w (algebraMap (𝓞 F) F u)) ^ 2 * h w ≤ κ * ((w' (algebraMap (𝓞 F) F u)) ^ 2 * h w') := by
  classical
  obtain ⟨κb, hκb, hbal⟩ := exists_forall_exists_unit_forall_mul_le_mul (F := F)

  have hdeg : ∑ w : InfinitePlace F, (mult w : ℝ) = (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast sum_mult_eq (K := F)
  have hdeg_pos : (0 : ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  refine ⟨κb ^ Module.finrank ℚ F, one_le_pow₀ hκb, fun κ hκ c h hpos hfloor => ?_⟩
  have hκb_le : κb ≤ κ := (le_self_pow₀ hκb (Module.finrank_pos (R := ℚ) (M := F)).ne').trans hκ
  have hκ_one : 1 ≤ κ := hκb.trans hκb_le
  by_cases hb : ∀ w w' : InfinitePlace F, h w ≤ κ * h w'
  ·
    refine ⟨1, fun w => ?_, fun w w' => ?_⟩
    · simpa using hfloor w
    · simpa using hb w w'
  ·
    obtain ⟨w₁, hw₁⟩ := not_forall.mp hb
    obtain ⟨w₂, hw₂⟩ := not_forall.mp hw₁
    have hspread : κ * h w₂ < h w₁ := not_le.mp hw₂
    obtain ⟨u, hu⟩ := hbal h hpos
    set f : InfinitePlace F → ℝ := fun w => (w (algebraMap (𝓞 F) F u)) ^ 2 * h w with hf
    have hwu : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F u) := fun w => pos_at_place u w
    have hfpos : ∀ w, 0 < f w := fun w => mul_pos (pow_pos (hwu w) 2) (hpos w)
    have hfbal : ∀ w w', f w ≤ κb * f w' := fun w w' => hu w w'
    refine ⟨u, fun w => ?_, fun w w' => ?_⟩
    swap
    · show f w ≤ κ * f w'
      exact (hfbal w w').trans (mul_le_mul_of_nonneg_right hκb_le (hfpos w').le)
    show c ≤ f w
    by_cases hc : c ≤ 0
    · exact hc.trans (hfpos w).le
    have hc0 : 0 < c := not_le.mp hc
    have hκb_pos : 0 < κb := zero_lt_one.trans_le hκb

    have hlogf : ∀ v : InfinitePlace F,
        Real.log (f v) = ((2 : ℕ) : ℝ) * Real.log (v (algebraMap (𝓞 F) F u)) + Real.log (h v) := by
      intro v
      simp only [hf]
      rw [Real.log_mul (pow_ne_zero 2 (hwu v).ne') (hpos v).ne', Real.log_pow]
    have hunit : ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (v (algebraMap (𝓞 F) F u)) = 0 :=
      sum_mult_mul_log u
    have hsum_eq : ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (f v)
        = ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (h v) := by
      calc ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (f v)
          = ∑ v : InfinitePlace F, (2 * ((mult v : ℝ) * Real.log (v (algebraMap (𝓞 F) F u)))
              + (mult v : ℝ) * Real.log (h v)) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [hlogf v]
            ring
        _ = 2 * ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (v (algebraMap (𝓞 F) F u))
              + ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (h v) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (h v) := by
            rw [hunit]
            ring

    have hterm : ∀ v : InfinitePlace F, 0 ≤ (mult v : ℝ) * (Real.log (h v) - Real.log c) := fun v =>
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (Real.log_le_log hc0 (hfloor v)))
    have hw₁log : Real.log κ ≤ Real.log (h w₁) - Real.log c := by
      have h1 : Real.log (κ * c) ≤ Real.log (h w₁) := by
        apply Real.log_le_log (mul_pos (zero_lt_one.trans_le hκ_one) hc0)
        calc κ * c ≤ κ * h w₂ := mul_le_mul_of_nonneg_left (hfloor w₂) (zero_le_one.trans hκ_one)
          _ ≤ h w₁ := hspread.le
      rw [Real.log_mul (zero_lt_one.trans_le hκ_one).ne' hc0.ne'] at h1
      linarith
    have hlogκ : 0 ≤ Real.log κ := Real.log_nonneg hκ_one
    have hmult₁ : (1 : ℝ) ≤ mult w₁ := one_le_mult
    have hsingle : (mult w₁ : ℝ) * (Real.log (h w₁) - Real.log c)
        ≤ ∑ v : InfinitePlace F, (mult v : ℝ) * (Real.log (h v) - Real.log c) :=
      Finset.single_le_sum (fun v _ => hterm v) (Finset.mem_univ w₁)
    have hsplit : ∑ v : InfinitePlace F, (mult v : ℝ) * (Real.log (h v) - Real.log c)
        = ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (h v) - (Module.finrank ℚ F : ℝ) * Real.log c := by
      rw [← hdeg, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    have hw₁term : Real.log κ ≤ (mult w₁ : ℝ) * (Real.log (h w₁) - Real.log c) := by
      calc Real.log κ = 1 * Real.log κ := (one_mul _).symm
        _ ≤ (mult w₁ : ℝ) * (Real.log (h w₁) - Real.log c) :=
            mul_le_mul hmult₁ hw₁log hlogκ (zero_le_one.trans hmult₁)
    have hlower : (Module.finrank ℚ F : ℝ) * Real.log c + Real.log κ
        ≤ ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (h v) := by
      linarith [hsplit, hsingle, hw₁term]

    obtain ⟨wm, -, hwm⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    have hupper : ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (f v)
        ≤ (Module.finrank ℚ F : ℝ) * Real.log (f wm) := by
      rw [← hdeg, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (hfpos v) (hwm v (Finset.mem_univ v)))
        (Nat.cast_nonneg _)

    have hκlog : (Module.finrank ℚ F : ℝ) * Real.log κb ≤ Real.log κ := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hκb_pos _) hκ

    have hfm : c * κb ≤ f wm := by
      have h3 : (Module.finrank ℚ F : ℝ) * (Real.log c + Real.log κb)
          ≤ (Module.finrank ℚ F : ℝ) * Real.log (f wm) := by
        rw [mul_add]
        linarith [hsum_eq, hlower, hupper, hκlog]
      have hlog : Real.log (c * κb) ≤ Real.log (f wm) := by
        rw [Real.log_mul hc0.ne' hκb_pos.ne']
        exact le_of_mul_le_mul_left h3 hdeg_pos
      exact (Real.log_le_log_iff (mul_pos hc0 hκb_pos) (hfpos wm)).mp hlog

    have hchain : κb * c ≤ κb * f w := by
      calc κb * c = c * κb := mul_comm _ _
        _ ≤ f wm := hfm
        _ ≤ κb * f w := hfbal wm w
    exact le_of_mul_le_mul_left hchain hκb_pos

end BalancingUnit

section PlaceNormsOfGenerators

variable {F : Type} [Field F] [NumberField F]

private theorem absNorm_spanSingleton_eq_prod_apply_pow_mult (x : F) :
    ((FractionalIdeal.absNorm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers F)) x) : ℚ) : ℝ) =
      ∏ w : NumberField.InfinitePlace F, w x ^ w.mult := by
  rw [FractionalIdeal.absNorm_span_singleton, NumberField.InfinitePlace.prod_eq_abs_norm]

omit [NumberField F] in

private theorem normAtPlace_pair_inv_eq (H : NumberField.InfinitePlace F → ℝ) (hH : ∀ w, 0 < H w)
    (w : NumberField.InfinitePlace F) :
    NumberField.mixedEmbedding.normAtPlace w
        (((fun v : {v : NumberField.InfinitePlace F // v.IsReal} => (H v.1)⁻¹),
          (fun v : {v : NumberField.InfinitePlace F // v.IsComplex} => (((H v.1)⁻¹ : ℝ) : ℂ))) :
            NumberField.mixedEmbedding.mixedSpace F) =
      (H w)⁻¹ := by
  by_cases hw : w.IsReal
  · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isReal hw]
    exact Real.norm_of_nonneg (inv_nonneg.mpr (hH w).le)
  · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex
      (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw)]
    exact Complex.norm_of_nonneg (inv_nonneg.mpr (hH w).le)

end PlaceNormsOfGenerators

section UnitsInALogBox

open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private noncomputable def unitLatticePoint (u : (𝓞 F)ˣ) : unitLattice F :=
  ⟨logEmbedding F (Additive.ofMul u), Submodule.mem_map.mpr ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩⟩

private theorem coe_unitLatticePoint (u : (𝓞 F)ˣ) :
    (unitLatticePoint F u : logSpace F) = logEmbedding F (Additive.ofMul u) := rfl

private noncomputable def unitCoords (u : (𝓞 F)ˣ) : Fin (rank F) → ℤ :=
  fun i => (basisUnitLattice F).repr (unitLatticePoint F u) i

private theorem inv_mul_mem_torsion_of_unitCoords_eq {u v : (𝓞 F)ˣ} (h : unitCoords F u = unitCoords F v) :
    u⁻¹ * v ∈ torsion F := by
  have hpt : unitLatticePoint F u = unitLatticePoint F v := by
    apply (basisUnitLattice F).repr.injective
    ext i
    exact congrFun h i
  have hlog : logEmbedding F (Additive.ofMul u) = logEmbedding F (Additive.ofMul v) := by
    have := congrArg (fun x : unitLattice F => (x : logSpace F)) hpt
    simpa [coe_unitLatticePoint] using this
  rw [← logEmbedding_eq_zero_iff, ofMul_mul, ofMul_inv, map_add, map_neg, hlog, neg_add_cancel]

private theorem norm_logEmbedding_le {L : ℝ} (hL : 0 ≤ L) {u : (𝓞 F)ˣ}
    (hu : ∀ w : InfinitePlace F, |Real.log (w (algebraMap (𝓞 F) F u))| ≤ L) :
    ‖logEmbedding F (Additive.ofMul u)‖ ≤ 2 * L := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro w
  rw [logEmbedding_component, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have hmult : (mult w.1 : ℝ) ≤ 2 := by
    unfold mult
    split_ifs <;> norm_num
  have hw := hu w.1
  calc (mult w.1 : ℝ) * |Real.log (w.1 (algebraMap (𝓞 F) F u))| ≤ 2 * L :=
        mul_le_mul hmult hw (abs_nonneg _) (by norm_num)

private theorem exists_forall_abs_unitCoords_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : (𝓞 F)ˣ, ∀ i : Fin (rank F),
      |(unitCoords F u i : ℝ)| ≤ M * ‖logEmbedding F (Additive.ofMul u)‖ := by
  set b : Module.Basis (Fin (rank F)) ℝ (logSpace F) := (basisUnitLattice F).ofZLatticeBasis ℝ _ with hb
  set e : logSpace F →L[ℝ] (Fin (rank F) → ℝ) := LinearMap.toContinuousLinearMap b.equivFun.toLinearMap with he
  refine ⟨‖e‖, norm_nonneg _, fun u i => ?_⟩
  have hcoord : (unitCoords F u i : ℝ) = e (logEmbedding F (Additive.ofMul u)) i := by
    simp only [he, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, Module.Basis.equivFun_apply, hb,
      unitCoords]
    rw [← coe_unitLatticePoint, (basisUnitLattice F).ofZLatticeBasis_repr_apply (K := ℝ)]
  rw [hcoord, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm (e (logEmbedding F (Additive.ofMul u))) i).trans (e.le_opNorm _)

private theorem exists_forall_ncard_units_forall_abs_log_le_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
      (Set.ncard {u : (𝓞 F)ˣ | ∀ w : InfinitePlace F, |Real.log (w (algebraMap (𝓞 F) F u))| ≤ L} : ℝ)
        ≤ C * (1 + L) ^ rank F := by
  classical
  haveI : Fintype (torsion F) := Fintype.ofFinite _
  obtain ⟨M, hM, hcoords⟩ := exists_forall_abs_unitCoords_le F
  refine ⟨(Fintype.card (torsion F) : ℝ) * (4 * M + 1) ^ rank F, by positivity, fun L hL => ?_⟩

  set N : ℤ := ⌊2 * M * L⌋ with hN
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr (by positivity)
  set S : Set (𝓞 F)ˣ := {u | ∀ w : InfinitePlace F, |Real.log (w (algebraMap (𝓞 F) F u))| ≤ L} with hS
  set box : Finset (Fin (rank F) → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-N) N with hbox
  have hmem : ∀ u ∈ S, unitCoords F u ∈ box := by
    intro u hu
    rw [hbox, Fintype.mem_piFinset]
    intro i
    have h1 : |(unitCoords F u i : ℝ)| ≤ 2 * M * L := by
      calc |(unitCoords F u i : ℝ)| ≤ M * ‖logEmbedding F (Additive.ofMul u)‖ := hcoords u i
        _ ≤ M * (2 * L) := mul_le_mul_of_nonneg_left (norm_logEmbedding_le F hL hu) hM
        _ = 2 * M * L := by ring
    rw [abs_le] at h1
    rw [Finset.mem_Icc]
    constructor
    · rw [neg_le, hN, Int.le_floor]
      push_cast
      linarith [h1.1]
    · rw [hN, Int.le_floor]
      exact h1.2

  let rep : (Fin (rank F) → ℤ) → (𝓞 F)ˣ := Function.invFun (unitCoords F)
  have hrep : ∀ u : (𝓞 F)ˣ, unitCoords F (rep (unitCoords F u)) = unitCoords F u :=
    fun u => Function.invFun_eq ⟨u, rfl⟩
  let Φ : (𝓞 F)ˣ → (Fin (rank F) → ℤ) × torsion F := fun u =>
    (unitCoords F u, ⟨(rep (unitCoords F u))⁻¹ * u, inv_mul_mem_torsion_of_unitCoords_eq F (hrep u)⟩)
  have hΦ : ∀ u ∈ S, Φ u ∈ (↑(box ×ˢ (Finset.univ : Finset (torsion F))) : Set _) := by
    intro u hu
    rw [Finset.coe_product, Finset.coe_univ]
    exact ⟨hmem u hu, Set.mem_univ _⟩
  have hinj : Set.InjOn Φ S := by
    intro u _ v _ huv
    have h1 : unitCoords F u = unitCoords F v := congrArg Prod.fst huv
    have h2 := congrArg (fun p : (Fin (rank F) → ℤ) × torsion F => (p.2 : (𝓞 F)ˣ)) huv
    simp only [Φ, h1] at h2
    exact mul_left_cancel h2
  have hcount : S.ncard ≤ Fintype.card (torsion F) * (2 * N + 1).toNat ^ rank F := by
    refine (Set.ncard_le_ncard_of_injOn Φ hΦ hinj (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset, Finset.card_product, Finset.card_univ, hbox, Fintype.card_piFinset_const,
      Int.card_Icc, mul_comm]
    have : (N + 1 - -N).toNat = (2 * N + 1).toNat := by congr 1; ring
    rw [this]
  have hbox_real : ((2 * N + 1).toNat : ℝ) ≤ (4 * M + 1) * (1 + L) := by
    have h1 : ((2 * N + 1).toNat : ℤ) = 2 * N + 1 := Int.toNat_of_nonneg (by omega)
    have h2 : ((2 * N + 1).toNat : ℝ) = 2 * (N : ℝ) + 1 := by exact_mod_cast h1
    have h3 : (N : ℝ) ≤ 2 * M * L := Int.floor_le _
    rw [h2]
    nlinarith [h3, hM, hL, mul_nonneg hM hL]
  calc (S.ncard : ℝ) ≤ (Fintype.card (torsion F) : ℝ) * ((2 * N + 1).toNat : ℝ) ^ rank F := by
        exact_mod_cast hcount
    _ ≤ (Fintype.card (torsion F) : ℝ) * ((4 * M + 1) * (1 + L)) ^ rank F := by
        gcongr
    _ = (Fintype.card (torsion F) : ℝ) * (4 * M + 1) ^ rank F * (1 + L) ^ rank F := by
        rw [mul_pow, mul_assoc]

end UnitsInALogBox

section LogBoxFiniteness

variable {F : Type} [Field F] [NumberField F]

private theorem finite_setOf_forall_abs_log_apply_le (L : ℝ) :
    {u : (NumberField.RingOfIntegers F)ˣ |
      ∀ w : NumberField.InfinitePlace F,
        |Real.log (w (algebraMap (NumberField.RingOfIntegers F) F u))| ≤ L}.Finite := by
  have hbig : {u : (NumberField.RingOfIntegers F)ˣ |
      ∀ w : NumberField.InfinitePlace F, w (algebraMap (NumberField.RingOfIntegers F) F u) ≤ Real.exp L}.Finite := by
    refine Set.Finite.of_finite_image ?_ (NumberField.Units.coe_injective F).injOn
    refine (NumberField.Embeddings.finite_of_norm_le F ℂ (Real.exp L)).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨NumberField.RingOfIntegers.isIntegral_coe _, fun φ => hu (NumberField.InfinitePlace.mk φ)⟩
  refine hbig.subset fun u hu w => ?_
  have hpos : 0 < w (algebraMap (NumberField.RingOfIntegers F) F u) := NumberField.Units.pos_at_place u w
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr ((abs_le.mp (hu w)).2)

end LogBoxFiniteness

private theorem exists_forall_boxGenCount_le_mul_log_pow :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ),
      boxGenCount K 𝔟 H ≤
        C * (1 + ENNReal.ofReal (Real.log
          ((∏ w : InfinitePlace K, H w ^ w.mult) / ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ)))) ^ Units.rank K := by
  obtain ⟨C₃, hC₃, hL3⟩ := exists_forall_ncard_units_forall_abs_log_le_le K
  refine ⟨ENNReal.ofReal C₃, ENNReal.ofReal_ne_top, fun 𝔟 H => ?_⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Set Kˣ, S = {γ : Kˣ | FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
        ∀ w : InfinitePlace K, w (γ : K) ≤ H w} := ⟨_, rfl⟩
  have hind : ∀ γ : Kˣ, γ ∉ S → S.indicator (1 : Kˣ → ℝ≥0∞) γ = 0 :=
    fun γ hγ => Set.indicator_apply_eq_zero.mpr fun hmem => (hγ hmem).elim
  rw [boxGenCount, ← hSdef]
  by_cases hex : ∃ γ₁ : Kˣ, γ₁ ∈ S
  swap
  · rw [tsum_congr fun γ => hind γ fun hmem => hex ⟨γ, hmem⟩, tsum_zero]
    exact zero_le
  obtain ⟨γ₁, hγ₁S⟩ := hex
  have hγ₁ := hγ₁S
  rw [hSdef] at hγ₁
  obtain ⟨hγ₁𝔟, hγ₁H⟩ := hγ₁
  have hwγ₁ : ∀ w : InfinitePlace K, 0 < w (γ₁ : K) := fun w => InfinitePlace.pos_iff.mpr γ₁.ne_zero

  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ,
      Λ = Real.log ((∏ w : InfinitePlace K, H w ^ w.mult) / ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ)) := ⟨_, rfl⟩
  rw [← hΛdef]
  have hD1 : ∀ w : InfinitePlace K, 1 ≤ H w / w (γ₁ : K) := fun w => (one_le_div₀ (hwγ₁ w)).mpr (hγ₁H w)
  have hlogD : ∀ w : InfinitePlace K, 0 ≤ Real.log (H w / w (γ₁ : K)) := fun w => Real.log_nonneg (hD1 w)
  have hΛ : Λ = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (H w / w (γ₁ : K)) := by
    rw [hΛdef, ← hγ₁𝔟, absNorm_spanSingleton_eq_prod_apply_pow_mult (F := K), ← Finset.prod_div_distrib]
    simp_rw [← div_pow]
    rw [Real.log_prod fun w _ => pow_ne_zero _ (zero_lt_one.trans_le (hD1 w)).ne']
    simp_rw [Real.log_pow]
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (Nat.cast_nonneg _) (hlogD w)
  have hDΛ : ∀ w : InfinitePlace K, Real.log (H w / w (γ₁ : K)) ≤ Λ := fun w => by
    rw [hΛ]
    calc Real.log (H w / w (γ₁ : K)) ≤ (w.mult : ℝ) * Real.log (H w / w (γ₁ : K)) :=
          le_mul_of_one_le_left (hlogD w) InfinitePlace.one_le_mult
      _ ≤ ∑ w' : InfinitePlace K, (w'.mult : ℝ) * Real.log (H w' / w' (γ₁ : K)) :=
          Finset.single_le_sum (f := fun w' : InfinitePlace K => (w'.mult : ℝ) * Real.log (H w' / w' (γ₁ : K)))
            (fun w' _ => mul_nonneg (Nat.cast_nonneg _) (hlogD w')) (Finset.mem_univ w)

  have hsub : S ⊆ (fun ε : (𝓞 K)ˣ => Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) ε * γ₁) ''
      {u : (𝓞 K)ˣ | ∀ w : InfinitePlace K, |Real.log (w (algebraMap (𝓞 K) K u))| ≤ Λ} := by
    intro γ hγS
    rw [hSdef] at hγS
    obtain ⟨hγ𝔟, hγH⟩ := hγS
    obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp (hγ₁𝔟.trans hγ𝔟.symm)
    have hεγ : algebraMap (𝓞 K) K ε * (γ₁ : K) = (γ : K) := by
      rw [← hε, Units.smul_def, Algebra.smul_def]
    have hεpos : ∀ w : InfinitePlace K, 0 < w (algebraMap (𝓞 K) K ε) := fun w => Units.pos_at_place ε w
    have hεle : ∀ w : InfinitePlace K,
        Real.log (w (algebraMap (𝓞 K) K ε)) ≤ Real.log (H w / w (γ₁ : K)) := fun w => by
      refine Real.log_le_log (hεpos w) ((le_div_iff₀ (hwγ₁ w)).mpr ?_)
      rw [← map_mul, hεγ]
      exact hγH w
    have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 K) K ε)) = 0 :=
      Units.sum_mult_mul_log ε
    have hgap : ∑ w : InfinitePlace K,
        (w.mult : ℝ) * (Real.log (H w / w (γ₁ : K)) - Real.log (w (algebraMap (𝓞 K) K ε))) = Λ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hsum, sub_zero, hΛ]
    refine ⟨ε, fun w => abs_le.mpr ⟨?_, (hεle w).trans (hDΛ w)⟩, ?_⟩
    · have hterm :
          (w.mult : ℝ) * (Real.log (H w / w (γ₁ : K)) - Real.log (w (algebraMap (𝓞 K) K ε))) ≤ Λ := by
        rw [← hgap]
        exact Finset.single_le_sum
          (f := fun w' : InfinitePlace K =>
            (w'.mult : ℝ) * (Real.log (H w' / w' (γ₁ : K)) - Real.log (w' (algebraMap (𝓞 K) K ε))))
          (fun w' _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hεle w'))) (Finset.mem_univ w)
      have hdiff : Real.log (H w / w (γ₁ : K)) - Real.log (w (algebraMap (𝓞 K) K ε)) ≤ Λ :=
        (le_mul_of_one_le_left (sub_nonneg.mpr (hεle w)) InfinitePlace.one_le_mult).trans hterm
      linarith [hlogD w]
    · exact Units.ext (by rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, hεγ])
  have hT : {u : (𝓞 K)ˣ | ∀ w : InfinitePlace K, |Real.log (w (algebraMap (𝓞 K) K u))| ≤ Λ}.Finite :=
    finite_setOf_forall_abs_log_apply_le (F := K) Λ
  have hSfin : S.Finite := (hT.image _).subset hsub
  have hcount : (S.ncard : ℝ) ≤ C₃ * (1 + Λ) ^ Units.rank K := by
    calc (S.ncard : ℝ)
        ≤ ({u : (𝓞 K)ˣ | ∀ w : InfinitePlace K, |Real.log (w (algebraMap (𝓞 K) K u))| ≤ Λ}.ncard : ℝ) := by
          exact_mod_cast (Set.ncard_le_ncard hsub (hT.image _)).trans (Set.ncard_image_le hT)
      _ ≤ C₃ * (1 + Λ) ^ Units.rank K := hL3 Λ hΛ0

  have hS1 : ∀ γ ∈ hSfin.toFinset, S.indicator (1 : Kˣ → ℝ≥0∞) γ = 1 := fun γ hγ =>
    Set.indicator_of_mem (hSfin.mem_toFinset.mp hγ) (1 : Kˣ → ℝ≥0∞)
  rw [tsum_eq_sum (s := hSfin.toFinset) fun γ hγ => hind γ fun hmem => hγ (hSfin.mem_toFinset.mpr hmem),
    Finset.sum_congr rfl hS1, Finset.sum_const, nsmul_eq_mul, mul_one, ← Set.ncard_eq_toFinset_card S hSfin,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hΛ0,
    ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul hC₃]
  exact ENNReal.ofReal_le_ofReal hcount

private theorem exists_forall_one_le_boxGenCount_and_absNorm_le :
    ∃ K₁ : ℝ, 1 ≤ K₁ ∧ ∀ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ),
      (∀ w : InfinitePlace K, 0 < H w) →
        ((∃ γ : Kˣ, FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟) →
            ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) * K₁ ≤ ∏ w : InfinitePlace K, H w ^ w.mult →
              1 ≤ boxGenCount K 𝔟 H) ∧
          (1 ≤ boxGenCount K 𝔟 H → ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) ≤ ∏ w : InfinitePlace K, H w ^ w.mult) := by
  obtain ⟨R, hR0, hdev⟩ := exists_forall_mem_fundamentalCone_abs_deviation_le (F := K)
  have hnpos : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  refine ⟨Real.exp (Module.finrank ℚ K * R), Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hR0),
    fun 𝔟 H hH => ⟨fun hprin hle => ?_, fun h1 => ?_⟩⟩
  · obtain ⟨γ₀, hγ₀⟩ := hprin
    have hP : 0 < ∏ w : InfinitePlace K, H w ^ w.mult := Finset.prod_pos fun w _ => pow_pos (hH w) _
    have hN : ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) = ∏ w : InfinitePlace K, w (γ₀ : K) ^ w.mult := by
      rw [← hγ₀]
      exact absNorm_spanSingleton_eq_prod_apply_pow_mult (F := K) _
    have hNpos : 0 < ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) := by
      rw [hN]
      exact Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.mpr γ₀.ne_zero) _

    obtain ⟨z, hz⟩ : ∃ z : NumberField.mixedEmbedding.mixedSpace K,
        ∀ w : InfinitePlace K, NumberField.mixedEmbedding.normAtPlace w z = (H w)⁻¹ :=
      ⟨_, normAtPlace_pair_inv_eq (F := K) H hH⟩
    obtain ⟨y, hy⟩ : ∃ y : NumberField.mixedEmbedding.mixedSpace K,
        ∀ w : InfinitePlace K, NumberField.mixedEmbedding.normAtPlace w y = w (γ₀ : K) * (H w)⁻¹ :=
      ⟨NumberField.mixedEmbedding K (γ₀ : K) * z, fun w => by
        rw [map_mul, NumberField.mixedEmbedding.normAtPlace_apply, hz w]⟩
    have hnormy : NumberField.mixedEmbedding.norm y =
        ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) * (∏ w : InfinitePlace K, H w ^ w.mult)⁻¹ := by
      rw [NumberField.mixedEmbedding.norm_apply, hN, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [hy w, mul_pow, inv_pow]
    have hy0 : NumberField.mixedEmbedding.norm y ≠ 0 := by
      rw [hnormy]
      exact (mul_pos hNpos (inv_pos.mpr hP)).ne'

    obtain ⟨u, hu⟩ := NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem hy0
    have hexp : 0 < Real.exp (Module.finrank ℚ K * R) := Real.exp_pos _
    have hnormu : NumberField.mixedEmbedding.norm (u • y) ≤ (Real.exp (Module.finrank ℚ K * R))⁻¹ := by
      rw [NumberField.mixedEmbedding.norm_unit_smul, hnormy, ← div_eq_mul_inv, div_le_iff₀ hP]
      have h' : ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) ≤
          (∏ w : InfinitePlace K, H w ^ w.mult) / Real.exp (Module.finrank ℚ K * R) :=
        (le_div_iff₀ hexp).mpr hle
      rwa [div_eq_inv_mul] at h'
    have hlognorm : Real.log (NumberField.mixedEmbedding.norm (u • y)) ≤ -(Module.finrank ℚ K * R) := by
      have hpos : 0 < NumberField.mixedEmbedding.norm (u • y) := by
        rw [NumberField.mixedEmbedding.norm_unit_smul, hnormy]
        exact mul_pos hNpos (inv_pos.mpr hP)
      calc Real.log (NumberField.mixedEmbedding.norm (u • y))
          ≤ Real.log (Real.exp (Module.finrank ℚ K * R))⁻¹ := Real.log_le_log hpos hnormu
        _ = -(Module.finrank ℚ K * R) := by rw [Real.log_inv, Real.log_exp]
    have hmean : Real.log (NumberField.mixedEmbedding.norm (u • y)) * (Module.finrank ℚ K : ℝ)⁻¹ ≤ -R := by
      have h3 := mul_le_mul_of_nonneg_right hlognorm (inv_nonneg.mpr hnpos.le)
      rwa [neg_mul, mul_comm (Module.finrank ℚ K : ℝ) R, mul_assoc, mul_inv_cancel₀ hnpos.ne', mul_one] at h3
    have hwu : ∀ w : InfinitePlace K, NumberField.mixedEmbedding.normAtPlace w (u • y) =
        w (algebraMap (𝓞 K) K u) * (w (γ₀ : K) * (H w)⁻¹) := fun w => by
      rw [NumberField.mixedEmbedding.unitSMul_smul, map_mul, NumberField.mixedEmbedding.normAtPlace_apply, hy w]
    have hbox : ∀ w : InfinitePlace K, w (algebraMap (𝓞 K) K u) * w (γ₀ : K) ≤ H w := by
      intro w
      have hwu0 : 0 < w (algebraMap (𝓞 K) K u) :=
        InfinitePlace.pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero)
      have ht : 0 < w (algebraMap (𝓞 K) K u) * (w (γ₀ : K) * (H w)⁻¹) :=
        mul_pos hwu0 (mul_pos (InfinitePlace.pos_iff.mpr γ₀.ne_zero) (inv_pos.mpr (hH w)))
      have h1 := (abs_le.mp (hdev (u • y) hu w)).2
      rw [hwu w] at h1
      have hlog : Real.log (w (algebraMap (𝓞 K) K u) * (w (γ₀ : K) * (H w)⁻¹)) ≤ 0 := by linarith
      have ht1 := (Real.log_nonpos_iff ht.le).mp hlog
      rwa [← mul_assoc, ← div_eq_mul_inv, div_le_one₀ (hH w)] at ht1

    obtain ⟨v, hv⟩ : ∃ v : Kˣ, (v : K) = algebraMap (𝓞 K) K u :=
      ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, rfl⟩
    have hmem : v * γ₀ ∈ {γ : Kˣ | FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
        ∀ w : InfinitePlace K, w (γ : K) ≤ H w} := by
      refine ⟨?_, fun w => ?_⟩
      · rw [← hγ₀]
        refine (FractionalIdeal.spanSingleton_eq_spanSingleton.mpr ⟨u, ?_⟩).symm
        rw [Units.smul_def, Algebra.smul_def, Units.val_mul, hv]
      · rw [Units.val_mul, map_mul, hv]
        exact hbox w
    calc (1 : ℝ≥0∞)
        = ({γ : Kˣ | FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
            ∀ w : InfinitePlace K, w (γ : K) ≤ H w}).indicator (1 : Kˣ → ℝ≥0∞) (v * γ₀) :=
          (Set.indicator_of_mem hmem (1 : Kˣ → ℝ≥0∞)).symm
      _ ≤ boxGenCount K 𝔟 H := by
        rw [boxGenCount]
        exact ENNReal.le_tsum _
  ·
    obtain ⟨γ, hγ𝔟, hγH⟩ : ∃ γ : Kˣ, FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
        ∀ w : InfinitePlace K, w (γ : K) ≤ H w := by
      by_contra hcon
      have hzero : ∀ γ : Kˣ, ({γ : Kˣ | FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
          ∀ w : InfinitePlace K, w (γ : K) ≤ H w}).indicator (1 : Kˣ → ℝ≥0∞) γ = 0 :=
        fun γ => Set.indicator_apply_eq_zero.mpr fun hmem => (hcon ⟨γ, hmem.1, hmem.2⟩).elim
      rw [boxGenCount, tsum_congr hzero, tsum_zero] at h1
      exact absurd h1 (by simp)
    rw [← hγ𝔟, absNorm_spanSingleton_eq_prod_apply_pow_mult (F := K)]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (apply_nonneg w _) _)
      (fun w _ => pow_le_pow_left₀ (apply_nonneg w _) (hγH w) _)

private theorem exists_forall_one_le_boxGenCountBal_of_one_le_boxGenCount :
    ∃ κ₀ : ℝ, 1 ≤ κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ → ∀ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ),
      1 ≤ boxGenCount K 𝔟 H → 1 ≤ boxGenCountBal K κ 𝔟 H := by
  obtain ⟨κ₀, hκ₀, hbal⟩ :=
    exists_one_le_forall_le_forall_exists_unit_forall_le_mul_and_forall_mul_le_mul (F := K)
  refine ⟨κ₀, hκ₀, fun κ hκ 𝔟 H h1 => ?_⟩

  obtain ⟨γ, hγ𝔟, hγH⟩ : ∃ γ : Kˣ, FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
      ∀ w : InfinitePlace K, w (γ : K) ≤ H w := by
    by_contra hcon
    have hzero : ∀ γ : Kˣ, ({γ : Kˣ | FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
        ∀ w : InfinitePlace K, w (γ : K) ≤ H w}).indicator (1 : Kˣ → ℝ≥0∞) γ = 0 :=
      fun γ => Set.indicator_apply_eq_zero.mpr fun hmem => (hcon ⟨γ, hmem.1, hmem.2⟩).elim
    rw [boxGenCount, tsum_congr hzero, tsum_zero] at h1
    exact absurd h1 (by simp)
  have hwγ : ∀ w : InfinitePlace K, 0 < w (γ : K) :=
    fun w => NumberField.InfinitePlace.pos_iff.mpr γ.ne_zero

  obtain ⟨u, hu1, hu2⟩ := hbal κ hκ 1 (fun w => H w / w (γ : K))
    (fun w => div_pos ((hwγ w).trans_le (hγH w)) (hwγ w)) (fun w => (one_le_div₀ (hwγ w)).mpr (hγH w))
  have hau : ∀ w : InfinitePlace K, 0 < w (algebraMap (𝓞 K) K u) :=
    fun w => NumberField.InfinitePlace.pos_iff.mpr (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero)
  have hu1' : ∀ w : InfinitePlace K, w (γ : K) ≤ (w (algebraMap (𝓞 K) K u)) ^ 2 * H w := by
    intro w
    have h : 1 ≤ (w (algebraMap (𝓞 K) K u)) ^ 2 * (H w / w (γ : K)) := hu1 w
    rwa [← mul_div_assoc, one_le_div₀ (hwγ w)] at h
  have hu2' : ∀ w w' : InfinitePlace K, (w (algebraMap (𝓞 K) K u)) ^ 2 * (H w / w (γ : K)) ≤
      κ * ((w' (algebraMap (𝓞 K) K u)) ^ 2 * (H w' / w' (γ : K))) := fun w w' => hu2 w w'

  obtain ⟨v, hv⟩ : ∃ v : Kˣ, (v : K) = algebraMap (𝓞 K) K u :=
    ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, rfl⟩
  have hval : ((γ * v⁻¹ ^ 2 : Kˣ) : K) = (γ : K) * (algebraMap (𝓞 K) K u)⁻¹ ^ 2 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hv]
  have hwγ' : ∀ w : InfinitePlace K,
      w ((γ * v⁻¹ ^ 2 : Kˣ) : K) = w (γ : K) / (w (algebraMap (𝓞 K) K u)) ^ 2 := by
    intro w
    rw [hval, map_mul, map_pow, map_inv₀, div_eq_mul_inv, inv_pow]
  have hmem : γ * v⁻¹ ^ 2 ∈ {γ : Kˣ | (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
      ∀ w : InfinitePlace K, w (γ : K) ≤ H w) ∧
      ∀ w w' : InfinitePlace K, H w * w' (γ : K) ≤ κ * (H w' * w (γ : K))} := by
    refine ⟨⟨?_, fun w => ?_⟩, fun w w' => ?_⟩
    · rw [← hγ𝔟]
      refine (FractionalIdeal.spanSingleton_eq_spanSingleton.mpr ⟨u⁻¹ ^ 2, ?_⟩).symm
      rw [Units.smul_def, Algebra.smul_def, Units.val_pow_eq_pow_val, map_pow, map_units_inv, hval, mul_comm]
    · rw [hwγ' w, div_le_iff₀ (pow_pos (hau w) 2)]
      linarith [hu1' w]
    · rw [hwγ' w, hwγ' w']
      have h := hu2' w w'
      simp only [← mul_div_assoc] at h ⊢
      rw [div_le_div_iff₀ (hwγ w) (hwγ w')] at h
      rw [div_le_div_iff₀ (pow_pos (hau w') 2) (pow_pos (hau w) 2)]
      linarith [h]
  calc (1 : ℝ≥0∞) = ({γ : Kˣ | (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
          ∀ w : InfinitePlace K, w (γ : K) ≤ H w) ∧
          ∀ w w' : InfinitePlace K, H w * w' (γ : K) ≤ κ * (H w' * w (γ : K))}).indicator
            (1 : Kˣ → ℝ≥0∞) (γ * v⁻¹ ^ 2) :=
              (Set.indicator_of_mem hmem (1 : Kˣ → ℝ≥0∞)).symm
    _ ≤ boxGenCountBal K κ 𝔟 H := by
      rw [boxGenCountBal]
      exact ENNReal.le_tsum _

private theorem exists_forall_norm_apply_eq_ideleNorm_rpow_of_mem_isotypicCuspSubmodule
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (g : AdelicGL2 (𝓞 K) K → ℂ)
    (hg : g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ)
    (hg0 : g ≠ 0) :
    ∃ σ : ℝ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ σ := by
  have hP := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K Φ₀
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ξ N S Ψ g hg hg0
  have hlsxi : IsLsXiFunction (𝓞 K) K ⊤ ξ g := ((lsXiMemberAt_iff _ _ _ _ _ _ _).mp hP.smoothCusp.1.1).1
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hg0
  obtain ⟨hprincipal, hcts⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K ξ g hlsxi hP.continuous
      ⟨x, hx⟩
  let ι : (AdeleRing (𝓞 K) K)ˣ →* (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) :=
    { toFun := fun z => ⟨z, Subgroup.mem_top z⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K (ξ.comp ι) hprincipal hcts
  exact ⟨σ, fun z => hσ z⟩

private theorem isotypicCuspSubmodule_mono (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    {S S' : Finset (HeightOneSpectrum (𝓞 K))} (hSS' : S ⊆ S') (Ψ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K pins ξ N S Ψ ≤ isotypicCuspSubmodule K pins ξ N S' Ψ := by
  refine Submodule.span_mono fun φ (hφ : IsIsotypicCuspFormAt K pins ξ N S Ψ φ) => ?_
  show IsIsotypicCuspFormAt K pins ξ N S' Ψ φ
  exact ⟨hφ.smoothCusp, hφ.continuous, hφ.level_invariant, fun v hv => hφ.hecke_eigen v fun h => hv (hSS' h),
    fun v hv g => hφ.central_eigen v (fun h => hv (hSS' h)) g⟩

private theorem classSum_eq_zero_of_not_classCarriesMass (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ψ : HeckeEigensystem K ℂ) (e : ℝ) (𝒞 : ClassGroup (𝓞 K))
    (h𝒞 : ¬ ClassCarriesMass K S Ψ 𝒞) (Y : ℝ) :
    classSum K S Ψ e 𝒞 Y = 0 ∧ classBlock K S Ψ e 𝒞 Y = 0 := by
  have h0 : ∀ 𝔫 : GoodIdeal K S, GoodIdeal.cls K 𝔫 = 𝒞 → massSeq K Ψ e 𝔫.1 = 0 := by
    intro 𝔫 h
    have hr : recValue K Ψ 𝔫.1 = 0 := by
      by_contra hne
      exact h𝒞 ⟨𝔫, h, hne⟩
    simp [massSeq, hr]
  exact ⟨ENNReal.tsum_eq_zero.mpr fun 𝔫 => h0 𝔫.1 𝔫.2.1,
    ENNReal.tsum_eq_zero.mpr fun 𝔫 => h0 𝔫.1 𝔫.2.1⟩

section IsotypicCoefficients

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology

open AdelicDock
open scoped ProbabilityTheory

noncomputable section

section LevelKernels

private def IsLevelKernel (N : Ideal (𝓞 K)) (f : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  IsFactorizableTestFn K f ∧
    ∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
      ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧
        k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k

end LevelKernels

section WindowPinMeasures

private abbrev pinsOf (D : Set (AdelicGL2 (𝓞 K) K)) :=
  productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

private theorem secondCountable_adelicGL2 : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact (Units.isInducing_embedProduct (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).secondCountableTopology

private theorem sigmaFinite_adelicGLHaar : SigmaFinite (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := secondCountable_adelicGL2 K
  infer_instance

private theorem isProbabilityMeasure_pins_ν (D : Set (AdelicGL2 (𝓞 K) K)) : IsProbabilityMeasure (pinsOf K D).ν :=
  isProbabilityMeasure_productionPinsOf_ν K D _ _ (adelicBox K)
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos K).ne'
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top K).ne

private theorem isKfSmooth_of_finEmbed_invariant (U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (hUo : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, f (g * finEmbed (𝓞 K) K u) = f g) : IsKfSmooth K f := by
  rw [isKfSmooth_iff]
  refine FLT.SmoothVectors.IsSmoothVector.of_isOpen_subgroup
    (U.comap ((glFin (𝓞 K) K).comp (finiteAdelicGL2Subgroup K).subtype)) ?_ ?_
  · exact hUo.preimage ((continuous_glFin (𝓞 K) K).comp continuous_subtype_val)
  · rw [FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
    convert isOpen_univ
    ext h
    simp only [SetLike.mem_coe, Set.mem_univ, iff_true, MulAction.mem_stabilizer_iff]
    obtain ⟨⟨g, hgfin⟩, hgU⟩ := h
    have hgU' : glFin (𝓞 K) K g ∈ U := Subgroup.mem_comap.mp hgU
    have hg : g = finEmbed (𝓞 K) K (glFin (𝓞 K) K g) := by
      apply eq_of_glArch_eq_of_glFin_eq
      · rw [glArch_finEmbed]
        exact (mem_finiteAdelicGL2Subgroup_iff K g).mp hgfin
      · rw [glFin_finEmbed]
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    change f (x * g) = f x
    rw [hg]
    exact hf x _ hgU'

section

variable {K}

private theorem integrable_joint (D : Set (AdelicGL2 (𝓞 K) K)) {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ}
    (hψ : IsGlobalAddChar K ψ) {φ F : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hFc : Continuous F)
    (hFs : HasCompactSupport F) (α : K) (h : AdelicGL2 (𝓞 K) K) :
    Integrable (fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        F p.2 * (φ (unipotentGL2 p.1 * (h * p.2)) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * p.1))))
      ((pinsOf K D).ν.prod (adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  haveI := sigmaFinite_adelicGLHaar K
  haveI := isProbabilityMeasure_pins_ν K D
  haveI : IsProbabilityMeasure (pinsOf K D).ν := isProbabilityMeasure_cond_adelicBox K
  have hνbox : ∀ᵐ x ∂(pinsOf K D).ν, x ∈ adelicBox K := ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox K)
  have hu : Continuous (fun x : AdeleRing (𝓞 K) K => unipotentGL2 x) := continuous_unipotentGL2
  obtain ⟨C₀, hC₀, hbox⟩ := exists_isCompact_adelicBox_subset K
  have hKc : IsCompact ((fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => unipotentGL2 p.1 * (h * p.2)) ''
      (C₀ ×ˢ tsupport F)) :=
    (hC₀.prod hFs).image ((hu.comp continuous_fst).mul (continuous_const.mul continuous_snd))
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hφ.continuousOn
  have hFint : Integrable F (adelicGLHaar (Fin 2) (𝓞 K) K) := hFc.integrable_of_hasCompactSupport hFs
  have hmeas : AEStronglyMeasurable (fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
      F p.2 * (φ (unipotentGL2 p.1 * (h * p.2)) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * p.1))))
      ((pinsOf K D).ν.prod (adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    refine Continuous.aestronglyMeasurable ?_
    exact (hFc.comp continuous_snd).mul
      ((hφ.comp ((hu.comp continuous_fst).mul (continuous_const.mul continuous_snd))).mul
        (hψ.continuous.comp (continuous_const.mul continuous_fst).neg))
  have hae : ∀ᵐ p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K ∂((pinsOf K D).ν.prod (adelicGLHaar (Fin 2) (𝓞 K) K)),
      p.1 ∈ adelicBox K :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hνbox
  refine ((hFint.norm.comp_snd (pinsOf K D).ν).mul_const M).mono' hmeas (hae.mono fun p hp => ?_)
  rw [norm_mul, norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K hψ, mul_one]
  by_cases hy : p.2 ∈ tsupport F
  · exact mul_le_mul_of_nonneg_left (hM _ ⟨p, ⟨hbox hp, hy⟩, rfl⟩) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hy]

private theorem whittakerCoefficient_rightConv (D : Set (AdelicGL2 (𝓞 K) K)) {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ}
    (hψ : IsGlobalAddChar K ψ) {φ F : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hFc : Continuous F)
    (hFs : HasCompactSupport F) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (pinsOf K D) ψ (rightConv K φ F) α g
      = ∫ y, F y * whittakerCoefficient K (pinsOf K D) ψ φ α (g * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := sigmaFinite_adelicGLHaar K
  haveI := isProbabilityMeasure_pins_ν K D
  have hW : whittakerCoefficient K (pinsOf K D) ψ (rightConv K φ F) α g
      = ∫ x, (∫ y, F y * (φ (unipotentGL2 x * (g * y)) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂(pinsOf K D).ν := by
    unfold whittakerCoefficient
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [rightConv_apply, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    simp only [mul_assoc]
    ring
  rw [hW, integral_integral_swap (integrable_joint D hψ hφ hFc hFs α g)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [integral_const_mul]
  rfl

end

end WindowPinMeasures

section ArchimedeanFiniteCommutation

variable {K}

private theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {a b : AdelicGL2 (𝓞 K) K}
    (ha : glFin (𝓞 K) K a = 1) (hb : glArch (𝓞 K) K b = 1) : a * b = b * a := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul, hb, mul_one, one_mul]
  · rw [map_mul, map_mul, ha, mul_one, one_mul]

private theorem glArch_eq_one_of_mem_level {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : glArch (𝓞 K) K k = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff K k).mp hk.2

private theorem glArch_eq_one_of_mem_doubleCoset {U : Subgroup (AdelicGL2 (𝓞 K) K)}
    (hU : U ≤ finiteAdelicGL2Subgroup K) {gv : AdelicGL2 (𝓞 K) K} (hgv : gv ∈ finiteAdelicGL2Subgroup K)
    {x : AdelicGL2 (𝓞 K) K} (hx : x ∈ HeckePair.doubleCoset U gv) : glArch (𝓞 K) K x = 1 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact (mem_finiteAdelicGL2Subgroup_iff K _).mp
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu₁) hgv) (hU hu₂))

end ArchimedeanFiniteCommutation

section SupportFactorization

variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

private theorem apply_mul_mul_mul_eq_of_levelKernel (hf : IsLevelKernel K N f)
    (hg : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u) = g y)
    (h b x : AdelicGL2 (𝓞 K) K) (hb : glArch (𝓞 K) K b = 1) (hx : f x ≠ 0) :
    ∃ a : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ g (h * b * x) = g (h * a * b) ∧ g (h * x) = g (h * a) := by
  obtain ⟨a, k, ha, hk, rfl⟩ := hf.2 x hx
  refine ⟨a, ha, ?_, ?_⟩
  · rw [← mul_assoc, hg _ k hk, mul_assoc, ← mul_comm_of_glFin_eq_one_of_glArch_eq_one ha hb, ← mul_assoc]
  · rw [← mul_assoc, hg _ k hk]

private theorem integrand_mul_level (hf : IsLevelKernel K N f)
    (hg : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u) = g y)
    (h : AdelicGL2 (𝓞 K) K) {u : AdelicGL2 (𝓞 K) K} (hu : u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (x : AdelicGL2 (𝓞 K) K) : g (h * u * x) * f x = g (h * x) * f x := by
  by_cases hx : f x = 0
  · simp [hx]
  obtain ⟨a, ha, h₁, h₂⟩ := apply_mul_mul_mul_eq_of_levelKernel hf hg h u x (glArch_eq_one_of_mem_level hu) hx
  rw [h₁, h₂, hg _ u hu]

private theorem sum_integrand_reps (hf : IsLevelKernel K N f)
    (hg : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u) = g y)
    {n : ℕ} {reps : Fin n → AdelicGL2 (𝓞 K) K} (hreps : ∀ i, glArch (𝓞 K) K (reps i) = 1) {c : ℂ}
    (heig : ∀ y : AdelicGL2 (𝓞 K) K, ∑ i, g (y * reps i) = c * g y) (h x : AdelicGL2 (𝓞 K) K) :
    ∑ i, g (h * reps i * x) * f x = c * g (h * x) * f x := by
  by_cases hx : f x = 0
  · simp [hx]
  obtain ⟨a₀, k₀, ha₀, hk₀, rfl⟩ := hf.2 x hx
  have hterm : ∀ i, g (h * reps i * (a₀ * k₀)) = g (h * a₀ * reps i) := by
    intro i
    rw [← mul_assoc, hg _ k₀ hk₀, mul_assoc, ← mul_comm_of_glFin_eq_one_of_glArch_eq_one ha₀ (hreps i),
      ← mul_assoc]
  rw [← Finset.sum_mul, Finset.sum_congr rfl fun i _ => hterm i, heig, ← mul_assoc h a₀ k₀, hg _ k₀ hk₀]

end SupportFactorization

section ClauseTransfer

variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

private theorem integrable_smoothing_integrand (hg : Continuous g) (hf : IsFactorizableTestFn K f)
    (y : AdelicGL2 (𝓞 K) K) : Integrable (fun x => g (y * x) * f x) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  exact ((hg.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport
    (hfs.mul_left)

private theorem heckeGen_mem_finite (v : HeightOneSpectrum (𝓞 K)) :
    heckeGen (𝓞 K) K v ∈ finiteAdelicGL2Subgroup K := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := heckeGenAt_fst (R := 𝓞 K) (K := K) (v := v) (uniformizerUnit K v) i j
  exact h

private theorem rightConv_mul_level (hf : IsLevelKernel K N f)
    (hg : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u) = g y)
    (h : AdelicGL2 (𝓞 K) K) {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    rightConv K g f (h * u) = rightConv K g f h := by
  simp only [rightConv_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integrand_mul_level hf hg h hu x)

private theorem isHeckeCosetEigenfunctionAt_rightConv (hf : IsLevelKernel K N f) (hgc : Continuous g)
    (hg : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u) = g y)
    (v : HeightOneSpectrum (𝓞 K)) {c : ℂ}
    (heig : SmoothCusp.IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v) v g c) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v) v (rightConv K g f) c := by
  obtain ⟨reps, hsys, hsum⟩ := heig
  refine ⟨reps, hsys, fun h => ?_⟩
  have hreps : ∀ i, glArch (𝓞 K) K (reps i) = 1 := fun i =>
    glArch_eq_one_of_mem_doubleCoset inf_le_right (heckeGen_mem_finite v) (hsys.mem_doubleCoset i)
  have hsum' : ∀ y : AdelicGL2 (𝓞 K) K, ∑ i, g (y * reps i) = c * g y := fun y => hsum y
  simp only [SmoothCusp.heckeCosetSum, rightConv_apply]
  rw [← integral_finsetSum _ fun i _ => integrable_smoothing_integrand hgc hf.1 (h * reps i)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [sum_integrand_reps hf hg hreps hsum' h x, mul_assoc]

private theorem rightConv_mul_left_eq (hgc : Continuous g) (hf : IsFactorizableTestFn K f)
    {z : AdelicGL2 (𝓞 K) K} {l : ℂ} (hz : ∀ y : AdelicGL2 (𝓞 K) K, g (z * y) = l * g y) (h : AdelicGL2 (𝓞 K) K) :
    rightConv K g f (z * h) = l * rightConv K g f h := by
  have _ := hgc; have _ := hf
  simp only [rightConv_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [mul_assoc z h x, hz, mul_assoc]

end ClauseTransfer

section WindowClauses

variable {K}

private abbrev windowSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂

private theorem measure_windowSet_lt_top (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (hd₁ : 0 < d₁) : adelicGLHaar (Fin 2) (𝓞 K) K (windowSet c u d₁ d₂ T) < ⊤ := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  refine (measure_biUnion_finset_le (μ := adelicGLHaar (Fin 2) (𝓞 K) K) T _).trans_lt
    (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  rw [Set.image_mul_right, measure_preimage_mul_right]
  exact SiegelVolume.measure_centreCutSiegelSet_lt_top (adelicGLHaar (Fin 2) (𝓞 K) K) hc u hd₁ d₂

private theorem constantTerm_eq_whittakerCoefficient_zero (D : Set (AdelicGL2 (𝓞 K) K))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    @constantTerm _ (pinsOf K D).nS _ _ (pinsOf K D).ν unipotentGL2 φ h
      = whittakerCoefficient K (pinsOf K D) ψ φ 0 h := by
  letI := (pinsOf K D).nS
  simp only [constantTerm, constantTermIntegrand, whittakerCoefficient, map_zero, zero_mul, neg_zero,
    AddChar.map_zero_eq_one, mul_one]

private theorem isCuspidalFn_rightConv_pinsOf (D : Set (AdelicGL2 (𝓞 K) K)) {φ f : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hf : IsFactorizableTestFn K f)
    (hcusp : @IsCuspidalFn _ (pinsOf K D).nS _ _ (pinsOf K D).ν unipotentGL2 φ) :
    @IsCuspidalFn _ (pinsOf K D).nS _ _ (pinsOf K D).ν unipotentGL2 (rightConv K φ f) :=
  AutomorphicForm.isCuspidalFn_rightConv K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) φ hφ hcusp f hf

private theorem measurableSet_windowSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    MeasurableSet (windowSet c u d₁ d₂ T) :=
  T.measurableSet_biUnion fun x _ => by
    rw [Set.image_mul_right]
    exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const x⁻¹)

end WindowClauses

section PlaceExtensionality

variable {K}

open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

private theorem adelicGL2_ext {x y : AdelicGL2 (𝓞 K) K} (harch : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K),
      finComponent (𝓞 K) K w (glFin (𝓞 K) K x) = finComponent (𝓞 K) K w (glFin (𝓞 K) K y)) : x = y := by
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K
  · ext i j
    have h0 := Units.val_inj.mpr harch
    have h := congrFun (congrFun h0 i) j
    first | exact h | simpa only [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply] using h
  · apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K
    intro w
    ext i j
    have h0 := Units.val_inj.mpr (hfin w)
    have h := congrFun (congrFun h0 i) j
    first | exact h | simpa only [finComponent_apply, glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply] using h

private theorem commute_placeEmbed {v : HeightOneSpectrum (𝓞 K)} {x : AdelicGL2 (𝓞 K) K}
    (hx : finComponent (𝓞 K) K v (glFin (𝓞 K) K x) = 1) (k : GL (Fin 2) (v.adicCompletion K)) :
    x * placeEmbed K v k = placeEmbed K v k * x := by
  apply adelicGL2_ext
  · simp only [map_mul, placeEmbed, MonoidHom.coe_comp, Function.comp_apply, glArch_finEmbed, mul_one, one_mul]
  · intro w
    simp only [map_mul, placeEmbed, MonoidHom.coe_comp, Function.comp_apply, glFin_finEmbed]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_localEmbed_self, hx, one_mul, mul_one]
    · rw [finComponent_localEmbed_of_ne (𝓞 K) K v k hw, mul_one, one_mul]

private theorem whittakerCoefficientIntegrable_of_continuous (D : Set (AdelicGL2 (𝓞 K) K))
    {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (α : K) (g : AdelicGL2 (𝓞 K) K) : WhittakerCoefficientIntegrable K (pinsOf K D) ψ f α g := by
  unfold WhittakerCoefficientIntegrable
  haveI : IsProbabilityMeasure (pinsOf K D).ν := isProbabilityMeasure_cond_adelicBox K
  have hu : Continuous (fun x : AdeleRing (𝓞 K) K => unipotentGL2 x) := continuous_unipotentGL2
  obtain ⟨C₀, hC₀, hbox⟩ := exists_isCompact_adelicBox_subset K
  have hc : Continuous (fun x : AdeleRing (𝓞 K) K =>
      f (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))) :=
    (hf.comp (hu.mul continuous_const)).mul (hψ.continuous.comp (continuous_const.mul continuous_id).neg)
  obtain ⟨M, hM⟩ := hC₀.exists_bound_of_continuousOn hc.continuousOn
  refine (integrable_const M).mono' hc.aestronglyMeasurable ?_
  have hae : ∀ᵐ x ∂(pinsOf K D).ν, x ∈ adelicBox K := ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox K)
  exact hae.mono fun x hx => hM x (hbox hx)

end PlaceExtensionality

section UnipotentGlobalPoints

private theorem globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, Matrix.GeneralLinearGroup.map]

end UnipotentGlobalPoints

section RecursionIdentities

variable {K}

private theorem ne_zero_of_rightConv_apply_ne_zero {g f : AdelicGL2 (𝓞 K) K → ℂ} {x : AdelicGL2 (𝓞 K) K}
    (hx : rightConv K g f x ≠ 0) : g ≠ 0 := by
  rintro rfl
  apply hx
  rw [show rightConv K (0 : AdelicGL2 (𝓞 K) K → ℂ) f = fun _ => 0 from AutomorphicForm.rightConv_zero_left K f]

private theorem finComponent_glFin_mem_localIntegralSet {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (v : HeightOneSpectrum (𝓞 K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K k) ∈ localIntegralSet K v := by
  have h : glFin (𝓞 K) K k ∈ finiteLevelZero (𝓞 K) K N :=
    finiteLevelOne_le_finiteLevelZero (𝓞 K) K N (mem_levelOne_iff.mp (Subgroup.mem_inf.mp hk).1)
  refine ⟨fun i j => h.1.integral i j v, fun i j => ?_⟩
  rw [← map_inv]
  exact h.2.integral i j v

private theorem conj_heckeRecursionSeq (n : ℕ) (a b : ℂ) :
    ∀ m : ℕ, (starRingEnd ℂ) (UnramifiedWhittaker.heckeRecursionSeq (n : ℂ) a b m)
      = UnramifiedWhittaker.heckeRecursionSeq (n : ℂ) ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) m
  | 0 => by simp [UnramifiedWhittaker.heckeRecursionSeq]
  | 1 => by simp [UnramifiedWhittaker.heckeRecursionSeq, map_div₀]
  | m + 2 => by
    simp only [UnramifiedWhittaker.heckeRecursionSeq, map_div₀, map_sub, map_mul, map_natCast,
      conj_heckeRecursionSeq n a b (m + 1), conj_heckeRecursionSeq n a b m]

private def eigensystemAtLevel (Ψ : HeckeEigensystem K ℂ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) : HeckeEigensystem K ℂ where
  level := N
  level_ne_bot := hN
  a := Ψ.a
  b := Ψ.b

private def realizationOfIsIsotypicCuspFormAt {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)}
    (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 K))} {Ψ : HeckeEigensystem K ℂ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsIsotypicCuspFormAt K pins ξ N S Ψ φ) (hne : ∃ x, φ x ≠ 0) :
    SmoothCuspRealizationAt K pins (eigensystemAtLevel Ψ N hN).toRawCentral where
  toFun := φ
  exists_ne_zero := hne
  centralChar := ξ
  smoothCusp := hφ.smoothCusp
  level_invariant := hφ.level_invariant
  exceptionalSet := S
  hecke_eigen := hφ.hecke_eigen
  central_eigen := hφ.central_eigen

private theorem realizationOfIsIsotypicCuspFormAt_toFun {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)}
    (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 K))} {Ψ : HeckeEigensystem K ℂ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsIsotypicCuspFormAt K pins ξ N S Ψ φ) (hne : ∃ x, φ x ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hN hφ hne).toFun = φ := rfl

end RecursionIdentities

section NonVanishing

variable {K}

private theorem ne_zero_of_rightConv_rightConv_apply_ne_zero {g f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ}
    {x : AdelicGL2 (𝓞 K) K} (hx : rightConv K (rightConv K g f₁) f₂ x ≠ 0) : g ≠ 0 := by
  rintro rfl
  apply hx
  rw [show rightConv K (0 : AdelicGL2 (𝓞 K) K → ℂ) f₁ = fun _ => 0 from AutomorphicForm.rightConv_zero_left K f₁,
    AutomorphicForm.rightConv_zero_left K f₂]

private theorem exists_rightConv_ne_zero_of_rightConv_rightConv_apply_ne_zero {g f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ}
    {x : AdelicGL2 (𝓞 K) K} (hx : rightConv K (rightConv K g f₁) f₂ x ≠ 0) : ∃ y, rightConv K g f₁ y ≠ 0 := by
  by_contra hcon
  apply hx
  have h0 : rightConv K g f₁ = fun _ => 0 := funext fun y => by
    by_contra hy
    exact hcon ⟨y, hy⟩
  rw [h0, AutomorphicForm.rightConv_zero_left K f₂]

end NonVanishing

section CentralCharacterModulus

variable {K}

private theorem exists_norm_apply_eq_ideleNorm_rpow_of_isLsXiFunction
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hcont : Continuous φ) (hne : ∃ x, φ x ≠ 0) :
    ∃ w₀ : ℝ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w₀ := by
  obtain ⟨hprincipal, hcts⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K ξ φ hφ hcont hne
  let ι : (AdeleRing (𝓞 K) K)ˣ →* (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) :=
    { toFun := fun z => ⟨z, Subgroup.mem_top z⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  obtain ⟨w₀, hw₀⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K (ξ.comp ι) hprincipal hcts
  exact ⟨w₀, fun z => hw₀ z⟩

end CentralCharacterModulus

open scoped Topology

section ApproximateIdentity

private theorem isLocallyConstant_indicator_finiteLevelOne (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) {α : Type} [Zero α]
    (c : α) :
    IsLocallyConstant ((finiteLevelOne (𝓞 K) K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator
      fun _ => c) := by
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun b => ?_
  by_cases hc : c = 0
  · subst hc
    by_cases hb : b = 0
    · subst hb
      convert isOpen_univ using 1
      ext x
      simp
    · convert isOpen_empty using 1
      ext x
      simp [Ne.symm hb]
  by_cases hbc : b = c
  · subst hbc
    convert isOpen_finiteLevelOne (𝓞 K) K hN using 1
    ext x
    simp [hc]
  by_cases hb : b = 0
  · subst hb
    convert (isClosed_finiteLevelOne (𝓞 K) K N).isOpen_compl using 1
    ext x
    simp [hc]
  convert isOpen_empty using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  by_cases hx : x ∈ (finiteLevelOne (𝓞 K) K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
  · rw [Set.indicator_of_mem hx]
    exact Ne.symm hbc
  · rw [Set.indicator_of_notMem hx]
    exact Ne.symm hb

private theorem isFinTestFactor_indicator_finiteLevelOne (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (z : ℂ) :
    IsFinTestFactor K ((finiteLevelOne (𝓞 K) K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator
      fun _ => z) :=
  ⟨isLocallyConstant_indicator_finiteLevelOne K N hN z,
    HasCompactSupport.intro (isCompact_finiteLevelOne (𝓞 K) K N) fun _ hx => Set.indicator_of_notMem hx _⟩

private theorem exists_mem_inf_and_eq_adelicArchGLIncl_mul (N : Ideal (𝓞 K)) (y : AdelicGL2 (𝓞 K) K)
    (hy : glFin (𝓞 K) K y ∈ finiteLevelOne (𝓞 K) K N) :
    ∃ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      y = adelicArchGLIncl K (glArch (𝓞 K) K y) * k := by
  refine ⟨(adelicArchGLIncl K (glArch (𝓞 K) K y))⁻¹ * y, Subgroup.mem_inf.mpr ⟨?_, ?_⟩,
    (mul_inv_cancel_left _ _).symm⟩
  · rw [mem_levelOne_iff, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
    exact hy
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

private theorem continuous_adelicArchGLIncl_of_entries : Continuous (adelicArchGLIncl K) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := Units.continuous_val
  have hinv : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_val.comp continuous_inv
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact (((continuous_apply j).comp ((continuous_apply i).comp hval)).prodMk continuous_const)
  · refine continuous_matrix fun i j => ?_
    exact (((continuous_apply j).comp ((continuous_apply i).comp hinv)).prodMk continuous_const)

private theorem eventually_forall_norm_sub_le (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g)
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (1 : AdelicGL2 (𝓞 K) K), ∀ x ∈ C, ‖g (x * y) - g x‖ ≤ ε := by
  refine hC.eventually_forall_of_forall_eventually (x₀ := (1 : AdelicGL2 (𝓞 K) K))
    (P := fun y x => ‖g (x * y) - g x‖ ≤ ε) fun x _ => ?_
  have hk : Continuous fun z : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => g (z.2 * z.1) - g z.2 :=
    (hg.comp (continuous_snd.mul continuous_fst)).sub (hg.comp continuous_snd)
  have hlim : Filter.Tendsto (fun z : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => g (z.2 * z.1) - g z.2)
      (𝓝 ((1 : AdelicGL2 (𝓞 K) K), x)) (𝓝 0) := by
    simpa using hk.tendsto ((1 : AdelicGL2 (𝓞 K) K), x)
  refine (hlim.eventually (Metric.closedBall_mem_nhds (0 : ℂ) hε)).mono fun z hz => ?_
  simpa using hz

private theorem exists_isLevelKernel_forall_norm_rightConv_sub_le
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g)
    (hinv : ∀ x : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (x * u) = g x)
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsLevelKernel K N f ∧ ∀ x ∈ C, ‖rightConv K g f x - g x‖ ≤ ε := by
  classical

  have hW := eventually_forall_norm_sub_le K g hg C hC ε hε
  have hV : (adelicArchGLIncl K) ⁻¹' {y | ∀ x ∈ C, ‖g (x * y) - g x‖ ≤ ε} ∈
      𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing K)) := by
    refine (continuous_adelicArchGLIncl_of_entries K).continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact hW
  obtain ⟨h, hA, hreal, h1pos, hsupp, -, -⟩ :=
    exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat K 0 _ hV

  set S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
    (finiteLevelOne (𝓞 K) K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) with hS
  set f₀ : AdelicGL2 (𝓞 K) K → ℂ :=
    fun y => h (glArch (𝓞 K) K y) * S.indicator (fun _ => (1 : ℂ)) (glFin (𝓞 K) K y) with hf₀
  have hf₀fact : IsFactorizableTestFn K f₀ :=
    ⟨h, S.indicator fun _ => (1 : ℂ), hA, isFinTestFactor_indicator_finiteLevelOne K N hN 1, fun _ => rfl⟩
  obtain ⟨hf₀c, hf₀supp⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f₀ hf₀fact
  set ρ : AdelicGL2 (𝓞 K) K → ℝ := fun y => (f₀ y).re with hρ
  have hρ_eq : ∀ y, ((ρ y : ℝ) : ℂ) = f₀ y := by
    intro y
    by_cases hy : glFin (𝓞 K) K y ∈ S
    · simp only [hρ, hf₀, Set.indicator_of_mem hy, mul_one]
      exact (hreal _).1
    · simp [hρ, hf₀, Set.indicator_of_notMem hy]
  have hρ_nonneg : ∀ y, 0 ≤ ρ y := by
    intro y
    by_cases hy : glFin (𝓞 K) K y ∈ S
    · simp only [hρ, hf₀, Set.indicator_of_mem hy, mul_one]
      exact (hreal _).2
    · simp [hρ, hf₀, Set.indicator_of_notMem hy]
  have hρc : Continuous ρ := Complex.continuous_re.comp hf₀c
  have hρsupp : HasCompactSupport ρ := hf₀supp.comp_left Complex.zero_re

  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  have hρi : Integrable ρ μ := hρc.integrable_of_hasCompactSupport hρsupp
  have hρ1 : 0 < ρ 1 := by
    have h1S : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ S := (finiteLevelOne (𝓞 K) K N).one_mem
    simp only [hρ, hf₀, map_one, Set.indicator_of_mem h1S, mul_one]
    exact h1pos
  have hmpos : 0 < ∫ y, ρ y ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hρ_nonneg hρi]
    refine lt_of_lt_of_le ((isOpen_lt continuous_const hρc).measure_pos μ ⟨1, hρ1⟩) (measure_mono ?_)
    intro y hy
    exact (show (0 : ℝ) < ρ y from hy).ne'
  set m : ℝ := ∫ y, ρ y ∂μ with hm

  set f : AdelicGL2 (𝓞 K) K → ℂ := fun y => ((m⁻¹ * ρ y : ℝ) : ℂ) with hf
  have hfc : Continuous f := Complex.continuous_ofReal.comp (continuous_const.mul hρc)
  have hfsupp : HasCompactSupport f := (hρsupp.mul_left).comp_left Complex.ofReal_zero
  have hf_norm : ∀ y, ‖f y‖ = m⁻¹ * ρ y := fun y =>
    Complex.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hmpos.le) (hρ_nonneg y))
  have hmass : ∫ y, f y ∂μ = 1 := by
    have hcast : ∫ y, ((m⁻¹ * ρ y : ℝ) : ℂ) ∂μ = ((∫ y, m⁻¹ * ρ y ∂μ : ℝ) : ℂ) := integral_ofReal
    simp only [hf]
    rw [hcast, integral_const_mul, ← hm, inv_mul_cancel₀ hmpos.ne', Complex.ofReal_one]

  have hmove : ∀ y, ρ y ≠ 0 → ∀ x ∈ C, ‖g (x * y) - g x‖ ≤ ε := by
    intro y hy x hx
    have hf₀y : f₀ y ≠ 0 := by
      intro h0
      apply hy
      have := hρ_eq y
      rw [h0] at this
      exact_mod_cast this
    have hyS : glFin (𝓞 K) K y ∈ S :=
      Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul hf₀y)
    have hyV : adelicArchGLIncl K (glArch (𝓞 K) K y) ∈ {y | ∀ x ∈ C, ‖g (x * y) - g x‖ ≤ ε} :=
      hsupp (subset_tsupport h (left_ne_zero_of_mul hf₀y))
    obtain ⟨k, hk, hyk⟩ := exists_mem_inf_and_eq_adelicArchGLIncl_mul K N y hyS
    rw [hyk, ← mul_assoc, hinv _ k hk]
    exact hyV x hx
  refine ⟨f, ⟨⟨h, S.indicator fun _ => ((m⁻¹ : ℝ) : ℂ), hA, isFinTestFactor_indicator_finiteLevelOne K N hN _,
    fun y => ?_⟩, fun y hy => ?_⟩, fun x hx => ?_⟩
  · by_cases hy : glFin (𝓞 K) K y ∈ S
    · simp only [hf, Complex.ofReal_mul, Set.indicator_of_mem hy, hρ_eq y, hf₀, mul_one]
      ring
    · have hρy : ρ y = 0 := by simp [hρ, hf₀, Set.indicator_of_notMem hy]
      simp [hf, hρy, Set.indicator_of_notMem hy]
  · have hρy : ρ y ≠ 0 := by
      intro h0
      apply hy
      simp [hf, h0]
    have hyS : glFin (𝓞 K) K y ∈ S := by
      have hf₀y : f₀ y ≠ 0 := fun h0 => hρy (by have := hρ_eq y; rw [h0] at this; exact_mod_cast this)
      exact Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul hf₀y)
    obtain ⟨k, hk, hyk⟩ := exists_mem_inf_and_eq_adelicArchGLIncl_mul K N y hyS
    exact ⟨adelicArchGLIncl K (glArch (𝓞 K) K y), k, glFin_adelicArchGLIncl K _, hk, hyk⟩
  ·
    have hint₁ : Integrable (fun y => g (x * y) * f y) μ :=
      ((hg.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport hfsupp.mul_left
    have hint₂ : Integrable (fun y => g x * f y) μ := hfc.integrable_of_hasCompactSupport hfsupp |>.const_mul _
    have hgx : g x = ∫ y, g x * f y ∂μ := by rw [integral_const_mul, hmass, mul_one]
    have hdiff : rightConv K g f x - g x = ∫ y, (g (x * y) - g x) * f y ∂μ := by
      rw [rightConv_apply]
      conv_lhs => rw [hgx]
      rw [← integral_sub hint₁ hint₂]
      congr 1
      funext y
      ring
    have hbound : Integrable (fun y => ε * (m⁻¹ * ρ y)) μ := (hρi.const_mul m⁻¹).const_mul ε
    rw [hdiff]
    calc ‖∫ y, (g (x * y) - g x) * f y ∂μ‖ ≤ ∫ y, ε * (m⁻¹ * ρ y) ∂μ := by
          refine norm_integral_le_of_norm_le hbound (Filter.Eventually.of_forall fun y => ?_)
          rw [norm_mul, hf_norm y]
          by_cases hρy : ρ y = 0
          · simp [hρy]
          · exact mul_le_mul_of_nonneg_right (hmove y hρy x hx)
              (mul_nonneg (inv_nonneg.mpr hmpos.le) (hρ_nonneg y))
      _ = ε := by
          rw [integral_const_mul, integral_const_mul, ← hm, inv_mul_cancel₀ hmpos.ne', mul_one]

end ApproximateIdentity

section LimitIdentities

variable {K}

private theorem norm_whittakerCoefficient_sub_le (D : Set (AdelicGL2 (𝓞 K) K)) {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ}
    (hψ : IsGlobalAddChar K ψ) {x g : AdelicGL2 (𝓞 K) K → ℂ} (hx : Continuous x) (hg : Continuous g) (α : K)
    (h : AdelicGL2 (𝓞 K) K) {ε : ℝ}
    (hε : ∀ t ∈ adelicBox K, ‖x (unipotentGL2 t * h) - g (unipotentGL2 t * h)‖ ≤ ε) :
    ‖whittakerCoefficient K (pinsOf K D) ψ x α h - whittakerCoefficient K (pinsOf K D) ψ g α h‖ ≤ ε := by
  haveI : IsProbabilityMeasure (pinsOf K D).ν := isProbabilityMeasure_cond_adelicBox K
  have hxi := whittakerCoefficientIntegrable_of_continuous D hψ hx α h
  have hgi := whittakerCoefficientIntegrable_of_continuous D hψ hg α h
  unfold WhittakerCoefficientIntegrable at hxi hgi
  have hae : ∀ᵐ t ∂(pinsOf K D).ν, t ∈ adelicBox K := ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox K)
  unfold whittakerCoefficient
  rw [← integral_sub hxi hgi]
  refine (norm_integral_le_of_norm_le_const (C := ε) (hae.mono fun t ht => ?_)).trans ?_
  · rw [← sub_mul, norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K hψ, mul_one]
    exact hε t ht
  · simp only [probReal_univ, mul_one, le_refl]

private theorem exists_isCompact_unipotentGL2_mul_mem (h : AdelicGL2 (𝓞 K) K) :
    ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ t ∈ adelicBox K, unipotentGL2 t * h ∈ C := by
  obtain ⟨C₀, hC₀, hbox⟩ := exists_isCompact_adelicBox_subset K
  have hu : Continuous (fun t : AdeleRing (𝓞 K) K => unipotentGL2 t) := continuous_unipotentGL2
  exact ⟨(fun t : AdeleRing (𝓞 K) K => unipotentGL2 t * h) '' C₀, hC₀.image (hu.mul continuous_const),
    fun t ht => ⟨t, hbox ht, rfl⟩⟩

private theorem level_invariant_of_mem_isotypicCuspSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {Ψ : HeckeEigensystem K ℂ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : φ ∈ isotypicCuspSubmodule K pins ξ N S Ψ) (x : AdelicGL2 (𝓞 K) K) :
    ∀ u ∈ pins.U N, φ (x * u) = φ x := by
  refine Submodule.span_induction (p := fun φ _ => ∀ u ∈ pins.U N, φ (x * u) = φ x) ?_ ?_ ?_ ?_ h
  · exact fun φ hφ u hu => hφ.level_invariant x u hu
  · exact fun _ _ => rfl
  · exact fun _ _ _ _ hφ hφ' u hu => by simp only [Pi.add_apply, hφ u hu, hφ' u hu]
  · exact fun a _ _ hφ u hu => by simp only [Pi.smul_apply, hφ u hu]

end LimitIdentities

section Smoothing

variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
variable (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
variable (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)

private theorem isIsotypicCuspFormAt_window_rightConv
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (hβ : 0 < β) (hαβ : α < β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {x | ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}))
    (hN : N ≠ ⊥)
    (g : AdelicGL2 (𝓞 K) K → ℂ)
    (hg : IsIsotypicCuspFormAt K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsLevelKernel K N f) :
    IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ (rightConv K g f) := by
  have _ := hd
  have _ := hcov
  have hgc : Continuous g := hg.continuous
  have hlev : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u' ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u') = g y :=
    fun y u' hu' => hg.level_invariant y u' hu'
  obtain ⟨⟨hauto, hcusp⟩, -⟩ := hg.smoothCusp
  have hauto' := (lsXiMemberAt_iff _ _ _ _ _ _ _).mp hauto
  have hcusp' : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 g := hcusp
  have hmem : MemLp g 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) := hauto'.2
  have hcuspW : @IsCuspidalFn _ (pinsOf K (windowSet c u d₁ d₂ T)).nS _ _ (pinsOf K (windowSet c u d₁ d₂ T)).ν
      unipotentGL2 g := hcusp
  obtain ⟨C, hC⟩ :=
    exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
      K ξ f hf.1 c u d₁ d₂ T hc hd₁ α β hβ hαβ Φ₀ hΦ₀
  have hbound := hC g hauto'.1 hcusp' hgc hmem
  have hlsxi : IsLsXiFunction (𝓞 K) K ⊤ ξ (rightConv K g f) :=
    ⟨fun γ y => by
        rw [rightConv_mul_left_eq hgc hf.1 (z := globalPoints (𝓞 K) K γ) (l := 1)
          (fun y' => by rw [hauto'.1.left_invariant γ y', one_mul]) y, one_mul],
      fun z y => rightConv_mul_left_eq hgc hf.1 (hauto'.1.central_transform z) y⟩
  refine
    { smoothCusp := ⟨⟨?_, isCuspidalFn_rightConv_pinsOf _ hgc hf.1 hcuspW⟩, ?_⟩
      continuous := (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K g hgc f hf.1).1
      level_invariant := fun y u' hu' => rightConv_mul_level hf hlev y hu'
      hecke_eigen := fun v hv => isHeckeCosetEigenfunctionAt_rightConv hf hgc hlev v (hg.hecke_eigen v hv)
      central_eigen := fun v hv y => rightConv_mul_left_eq hgc hf.1 (hg.central_eigen v hv) y }
  · rw [IsAutomorphicFnAt, lsXiMemberAt_iff]
    refine ⟨hlsxi, ?_⟩
    show MemLp (rightConv K g f) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (windowSet c u d₁ d₂ T))
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (windowSet c u d₁ d₂ T)) :=
      isFiniteMeasure_restrict.mpr (measure_windowSet_lt_top c u d₁ d₂ T hc hd₁).ne
    refine MemLp.of_bound
      (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K g hgc f hf.1).1.aestronglyMeasurable
      (C * (eLpNorm g 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal) ?_
    rw [ae_restrict_iff' (measurableSet_windowSet c u d₁ d₂ T)]
    exact Filter.Eventually.of_forall fun y hy => hbound y hy
  · exact isKfSmooth_of_finEmbed_invariant K (finiteLevelOne (𝓞 K) K N) (isOpen_finiteLevelOne (𝓞 K) K hN)
      fun y u' hu' => rightConv_mul_level hf hlev y ⟨(finEmbed_mem_levelOne_iff (𝓞 K) K u').mpr hu',
        (mem_finiteAdelicGL2Subgroup_iff K _).mpr (glArch_finEmbed (𝓞 K) K u')⟩

private theorem exists_norm_whittakerCoefficient_le_of_rightConv_rightConv
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (hβ : 0 < β) (hαβ : α < β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {x | ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}))
    (hN : N ≠ ⊥)
    (g : AdelicGL2 (𝓞 K) K → ℂ)
    (hg : g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ)
    (f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ) (hf₁ : IsLevelKernel K N f₁) (hf₂ : IsLevelKernel K N f₂)
    (tys : ArchTypeFamily K) (hxt : rightConv K (rightConv K g f₁) f₂ ∈ archCutSubmodule K tys)
    (m : ℕ) :
    ∃ C : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → 1 ≤ ideleNorm K a →
        ‖whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1
            (diagOne a * k)‖ ≤ C * ideleNorm K a ^ (-(m : ℝ)) := by
  by_cases hx : ∃ x, rightConv K (rightConv K g f₁) f₂ x ≠ 0
  · obtain ⟨x, hx0⟩ := hx
    have hgP : IsIsotypicCuspFormAt K
        (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ g :=
      AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ξ N S Ψ g hg
        (ne_zero_of_rightConv_rightConv_apply_ne_zero hx0)
    have hP := isIsotypicCuspFormAt_window_rightConv K c u d₁ d₂ T α β Φ₀ ξ N S Ψ hc hd₁ hd hcov hβ hαβ hΦ₀ hN g
      hgP f₁ hf₁
    have hlsxi : IsLsXiFunction (𝓞 K) K ⊤ ξ (rightConv K g f₁) :=
      ((lsXiMemberAt_iff _ _ _ _ _ _ _).mp hP.smoothCusp.1.1).1
    obtain ⟨w₀, hw₀⟩ := exists_norm_apply_eq_ideleNorm_rpow_of_isLsXiFunction ξ hlsxi hP.continuous
      (exists_rightConv_ne_zero_of_rightConv_rightConv_apply_ne_zero hx0)
    exact AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
      K c u d₁ d₂ T hd hcov ξ (rightConv K g f₁) hP.smoothCusp.1 hP.continuous f₂ hf₂.1 tys hxt w₀ hw₀ m
  · refine ⟨0, fun _ _ _ _ _ _ => ?_⟩
    have h0 : rightConv K (rightConv K g f₁) f₂ = fun _ => 0 := funext fun y => by
      by_contra hy
      exact hx ⟨y, hy⟩
    rw [h0, whittakerCoefficient_zero, norm_zero, zero_mul]

open AutomorphicForm.SmoothCuspRealizationAt in

private theorem whittakerCoefficient_recursion_of_rightConv_rightConv
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (hβ : 0 < β) (hαβ : α < β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {x | ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}))
    (hN : N ≠ ⊥)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (g : AdelicGL2 (𝓞 K) K → ℂ)
    (hg : g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ)
    (f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ) (hf₁ : IsLevelKernel K N f₁) (hf₂ : IsLevelKernel K N f₂)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (k : AdelicGL2 (𝓞 K) K) (hk : glFin (𝓞 K) K k = 1)
    (y : AdelicGL2 (𝓞 K) K)
    (hy : Valued.v ((((Matrix.GeneralLinearGroup.det y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2)
    (m : ℕ) :
    ‖whittakerCoefficient K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1
        ((heckeGen (𝓞 K) K v) ^ m * y * k)‖ ^ 2 =
      ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
          (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2 *
        ‖whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (y * k)‖ ^ 2 := by
  by_cases hx : ∃ x, rightConv K g f₁ x ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hx
    have hgP : IsIsotypicCuspFormAt K
        (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ g :=
      AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ξ N S Ψ g hg
        (ne_zero_of_rightConv_apply_ne_zero hx₀)
    have hP := isIsotypicCuspFormAt_window_rightConv K c u d₁ d₂ T α β Φ₀ ξ N S Ψ hc hd₁ hd hcov hβ hαβ hΦ₀ hN g
      hgP f₁ hf₁
    have hlsxi : IsLsXiFunction (𝓞 K) K ⊤ ξ (rightConv K g f₁) :=
      ((lsXiMemberAt_iff _ _ _ _ _ _ _).mp hP.smoothCusp.1.1).1
    have hxc : Continuous (rightConv K (rightConv K g f₁) f₂) :=
      (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K (rightConv K g f₁) hP.continuous f₂ hf₂.1).1
    have hxsum : ∀ h : AdelicGL2 (𝓞 K) K, rightConv K (rightConv K g f₁) f₂ h =
        ∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℂ)) i *
          rightConv K (realizationOfIsIsotypicCuspFormAt hN hP ⟨x₀, hx₀⟩).toFun f₂ (h * (fun _ : Fin 1 => 1) i) :=
      fun h => by simp [realizationOfIsIsotypicCuspFormAt_toFun]
    have hxint : ∀ (α' : K) (h : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) α' h :=
      fun α' h => whittakerCoefficientIntegrable_of_continuous (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) hxc α' h
    have hxper : ∀ (β' : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
        rightConv K (rightConv K g f₁) f₂ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β' + uu) * hh) =
          rightConv K (rightConv K g f₁) f₂ (unipotentGL2 uu * hh) := by
      intro β' uu hh
      rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2 K β']
      have hli : ∀ y : AdelicGL2 (𝓞 K) K,
          rightConv K g f₁ (globalPoints (𝓞 K) K (unipotentGL2 β') * y) = (1 : ℂ) * rightConv K g f₁ y :=
        fun y => by rw [hlsxi.left_invariant, one_mul]
      rw [rightConv_mul_left_eq hP.continuous hf₂.1 hli, one_mul]
    have hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (h : AdelicGL2 (𝓞 K) K),
        rightConv K (rightConv K g f₁) f₂ (centralScalar (𝓞 K) K z * h) =
          (((realizationOfIsIsotypicCuspFormAt hN hP ⟨x₀, hx₀⟩).centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            rightConv K (rightConv K g f₁) f₂ h :=
      fun z h => rightConv_mul_left_eq hP.continuous hf₂.1 (hlsxi.central_transform ⟨z, Subgroup.mem_top z⟩) h
    have hsupp : ∀ z : AdelicGL2 (𝓞 K) K, f₂ z ≠ 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
          finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
        ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
          z₂ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
          ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
            z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁ := by
      intro z hz
      obtain ⟨a, k, ha, hk, rfl⟩ := hf₂.2 z hz
      refine ⟨fun v _ => ?_, a, k, rfl, hk, fun v _ xv => commute_placeEmbed (by rw [ha, map_one]) xv⟩
      rw [map_mul, ha, one_mul]
      exact finComponent_glFin_mem_localIntegralSet hk v
    have hSd : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ N ∧ v ∉ S :=
      fun v hv => ⟨fun hdvd => hv (hS v hdvd), hv⟩
    have hψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0 :=
      fun v hv => addCharLevel_psiLocal_eq_zero_of_not_dvd fun hdvd => hv (hSψ v hdvd)
    have hdock := whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
      K c u d₁ d₂ T S S (Finset.Subset.refl S) hψ0
      (eigensystemAtLevel Ψ N hN) (realizationOfIsIsotypicCuspFormAt hN hP ⟨x₀, hx₀⟩) hP.continuous
      hP.level_invariant f₂ hf₂.1 S (Finset.Subset.refl S) hsupp hSd 1 (fun _ => 1) (fun _ => 1)
      (fun _ => map_one (glArch (𝓞 K) K)) (fun _ _ _ _ => by simp)
      (rightConv K (rightConv K g f₁) f₂) hxsum hxint hxper hxZ
      (eigensystemAtLevel Ψ N hN) (realizationOfIsIsotypicCuspFormAt hN hP ⟨x₀, hx₀⟩) hP.continuous
      hP.level_invariant f₂ hf₂.1 S (Finset.Subset.refl S) hsupp hSd 1 (fun _ => 1) (fun _ => 1)
      (fun _ => map_one (glArch (𝓞 K) K)) (fun _ _ _ _ => by simp)
      (rightConv K (rightConv K g f₁) f₂) hxsum hxint hxper hxZ
      v hv k k hk hk y hy m
    rw [← conj_heckeRecursionSeq, Complex.mul_conj, Complex.mul_conj, Complex.mul_conj] at hdock
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact_mod_cast hdock
  · have h0 : rightConv K g f₁ = fun _ => 0 := funext fun z => by
      by_contra hz
      exact hx ⟨z, hz⟩
    rw [h0, AutomorphicForm.rightConv_zero_left K f₂, whittakerCoefficient_zero, whittakerCoefficient_zero, norm_zero]
    ring

private theorem whittakerCoefficient_recursion_of_mem
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (hβ : 0 < β) (hαβ : α < β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {x | ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}))
    (hN : N ≠ ⊥)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (g : AdelicGL2 (𝓞 K) K → ℂ)
    (hg : g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (k : AdelicGL2 (𝓞 K) K) (hk : glFin (𝓞 K) K k = 1)
    (y : AdelicGL2 (𝓞 K) K)
    (hy : Valued.v ((((Matrix.GeneralLinearGroup.det y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2)
    (m : ℕ) :
    ‖whittakerCoefficient K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) g 1 ((heckeGen (𝓞 K) K v) ^ m * y * k)‖ ^ 2 =
      ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
          (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2 *
        ‖whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) g 1 (y * k)‖ ^ 2 := by
  have hgc : Continuous g := continuous_of_mem_isotypicCuspSubmodule hg
  have hginv : ∀ x : AdelicGL2 (𝓞 K) K, ∀ u' ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (x * u') = g x :=
    fun x u' hu' => level_invariant_of_mem_isotypicCuspSubmodule hg x u' hu'
  obtain ⟨C₁, hC₁, hmem₁⟩ := exists_isCompact_unipotentGL2_mul_mem ((heckeGen (𝓞 K) K v) ^ m * y * k)
  obtain ⟨C₀, hC₀, hmem₀⟩ := exists_isCompact_unipotentGL2_mul_mem (y * k)
  have key : ∀ n : ℕ, ∃ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x ∧
      (∀ p ∈ C₁ ∪ C₀, ‖x p - g p‖ ≤ 1 / ((n : ℝ) + 1)) ∧
      ‖whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * y * k)‖ ^ 2 =
        ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
            (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2 *
          ‖whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) x 1 (y * k)‖ ^ 2 := by
    intro n
    have hhalf : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 2 := by positivity
    obtain ⟨f₁, hf₁, h₁⟩ :=
      exists_isLevelKernel_forall_norm_rightConv_sub_le K N hN g hgc hginv (C₁ ∪ C₀) (hC₁.union hC₀) _ hhalf
    have h₁c : Continuous (rightConv K g f₁) :=
      (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K g hgc f₁ hf₁.1).1
    have h₁inv : ∀ x : AdelicGL2 (𝓞 K) K, ∀ u' ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        rightConv K g f₁ (x * u') = rightConv K g f₁ x :=
      fun x _ hu' => rightConv_mul_level hf₁ hginv x hu'
    obtain ⟨f₂, hf₂, h₂⟩ :=
      exists_isLevelKernel_forall_norm_rightConv_sub_le K N hN (rightConv K g f₁) h₁c h₁inv
        (C₁ ∪ C₀) (hC₁.union hC₀) _ hhalf
    refine ⟨rightConv K (rightConv K g f₁) f₂,
      (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K (rightConv K g f₁) h₁c f₂ hf₂.1).1,
      fun p hp => ?_,
      whittakerCoefficient_recursion_of_rightConv_rightConv K c u d₁ d₂ T α β Φ₀ ξ N S Ψ hc hd₁ hd hcov hβ hαβ hΦ₀
        hN hS hSψ g hg f₁ f₂ hf₁ hf₂ v hv k hk y hy m⟩
    calc ‖rightConv K (rightConv K g f₁) f₂ p - g p‖
        = ‖(rightConv K (rightConv K g f₁) f₂ p - rightConv K g f₁ p) + (rightConv K g f₁ p - g p)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖rightConv K (rightConv K g f₁) f₂ p - rightConv K g f₁ p‖ + ‖rightConv K g f₁ p - g p‖ := norm_add_le _ _
      _ ≤ 1 / ((n : ℝ) + 1) / 2 + 1 / ((n : ℝ) + 1) / 2 := add_le_add (h₂ p hp) (h₁ p hp)
      _ = 1 / ((n : ℝ) + 1) := add_halves _
  choose x hxc hxg hxid using key
  have hconv : ∀ p : AdelicGL2 (𝓞 K) K, (∀ t ∈ adelicBox K, unipotentGL2 t * p ∈ C₁ ∪ C₀) →
      Filter.Tendsto (fun n => whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (x n) 1 p)
        Filter.atTop (nhds (whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) g 1 p)) := by
    intro p hp
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact norm_whittakerCoefficient_sub_le (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) (hxc n) hgc 1 p fun t ht => hxg n _ (hp t ht)
  have h₁ := (hconv _ fun t ht => Set.mem_union_left _ (hmem₁ t ht)).norm.pow 2
  have h₀ := ((hconv _ fun t ht => Set.mem_union_right _ (hmem₀ t ht)).norm.pow 2).const_mul
    (‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
        (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2)
  simp only [hxid] at h₁
  exact tendsto_nhds_unique h₁ h₀

end Smoothing

end

end IsotypicCoefficients

section RecursionValueExponent

open scoped Classical in

private theorem count_factors_eq_toNat_emultiplicity (v : HeightOneSpectrum (𝓞 K)) (𝔫 : Ideal (𝓞 K)) :
    (Associates.mk v.asIdeal).count (Associates.mk 𝔫).factors = (emultiplicity v.asIdeal 𝔫).toNat := by
  by_cases h : 𝔫 = 0
  · subst h
    rw [Associates.mk_zero, Associates.factors_zero, emultiplicity_zero, ENat.toNat_top]
    simp only [Associates.count, dif_pos v.associates_irreducible, Associates.bcount]
  · rw [Ideal.count_associates_factors_eq h v.isPrime v.ne_bot,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible h,
      normalize_eq, ENat.toNat_coe]

private theorem recValue_eq_finprod_toNat_emultiplicity (Ψ : HeckeEigensystem K ℂ) (𝔫 : Ideal (𝓞 K)) :
    recValue K Ψ 𝔫 = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
        (Ψ.toRawCentral.b v) (emultiplicity v.asIdeal 𝔫).toNat := by
  unfold recValue
  exact finprod_congr fun v => by rw [count_factors_eq_toNat_emultiplicity (K := K) v 𝔫]

end RecursionValueExponent

private theorem _root_.WindowMultiplicity.exists_forall_classBlock_le_and_classSum_le (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (σ : ℝ) (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ σ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (Ψ : HeckeEigensystem K ℂ)
    (hV : ∃ g ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ, g ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (𝒞 : ClassGroup (𝓞 K)) (Y : ℝ), 0 < Y →
      classBlock K S Ψ (1 + σ) 𝒞 Y ≤ C * ENNReal.ofReal Y ∧
        classSum K S Ψ (1 + σ) 𝒞 Y ≤ 2 * C * ENNReal.ofReal Y := by
  have h :=
    AutomorphicForm.ClassSumGrowth.exists_forall_classBlock_le_and_classSum_le K α β hβ hαβ Φ₀ hΦ₀ ξ σ
      hξ N hN S hS hSψ Ψ hV
  simp only [← recValue_eq_finprod_toNat_emultiplicity] at h
  exact h

p2m_export "WindowMultiplicity" "exists_forall_classBlock_le_and_classSum_le"

private theorem _root_.WindowMultiplicity.exists_forall_le_classSum_of_classCarriesMass (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (σ : ℝ) (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ σ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (Ψ : HeckeEigensystem K ℂ)
    (hV : ∃ g ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ, g ≠ 0) :
    ∃ cL : ℝ, 0 < cL ∧ ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ 𝒞 : ClassGroup (𝓞 K), ClassCarriesMass K S Ψ 𝒞 →
      ∀ Y : ℝ, Y₀ ≤ Y → ENNReal.ofReal (cL * Y) ≤ classSum K S Ψ (1 + σ) 𝒞 Y := by
  have h :=
    AutomorphicForm.ClassSumGrowth.exists_forall_le_classSum_of_classCarriesMass K α β hβ hαβ Φ₀ hΦ₀ ξ σ
      hξ N hN S hS hSψ Ψ hV
  simp only [← recValue_eq_finprod_toNat_emultiplicity] at h
  exact h

p2m_export "WindowMultiplicity" "exists_forall_le_classSum_of_classCarriesMass"

open scoped NNReal

namespace DyadicBlockComparison

private noncomputable def ratio (e : ℝ) : ℝ≥0 := Real.toNNReal ((2 : ℝ) ^ (-e))

private theorem coe_ratio (e : ℝ) : ((ratio e : ℝ≥0) : ℝ) = (2 : ℝ) ^ (-e) :=
  Real.coe_toNNReal _ (Real.rpow_nonneg (by norm_num) _)

private theorem ratio_pos (e : ℝ) : 0 < ratio e := by
  rw [← NNReal.coe_pos, coe_ratio]
  exact Real.rpow_pos_of_pos (by norm_num) _

private theorem ratio_lt_one {e : ℝ} (he : 0 < e) : ratio e < 1 := by
  rw [← NNReal.coe_lt_coe, coe_ratio, NNReal.coe_one]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

private noncomputable def weightSeries (e : ℝ) (r : ℕ) (j : ℕ) : ℝ≥0 := ((j : ℝ≥0) + 1) ^ r * ratio e ^ j

private theorem summable_weightSeries {e : ℝ} (he : 0 < e) (r : ℕ) : Summable (weightSeries e r) := by
  rw [← NNReal.summable_coe]
  have hq : ‖((ratio e : ℝ≥0) : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (ratio e).coe_nonneg]
    exact_mod_cast ratio_lt_one he
  have h : Summable fun n : ℕ => (n : ℝ) ^ r * ((ratio e : ℝ≥0) : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one r hq
  have h1 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ r * ((ratio e : ℝ≥0) : ℝ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr h
  have hq0 : ((ratio e : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast (ratio_pos e).ne'
  refine (h1.mul_left (((ratio e : ℝ≥0) : ℝ)⁻¹)).congr fun n => ?_
  simp only [weightSeries, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  push_cast
  field_simp
  ring

private theorem coe_weightSeries (e : ℝ) (r j : ℕ) :
    ((weightSeries e r j : ℝ≥0) : ℝ≥0∞) = ((j : ℝ≥0∞) + 1) ^ r * ((ratio e : ℝ≥0) : ℝ≥0∞) ^ j := by
  simp only [weightSeries]
  push_cast
  rfl

private theorem tsum_weightSeries_ne_top {e : ℝ} (he : 0 < e) (r : ℕ) :
    (∑' j : ℕ, ((weightSeries e r j : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ :=
  ENNReal.tsum_coe_ne_top_iff_summable.mpr (summable_weightSeries he r)

private noncomputable def comparisonConstant (A a B : ℝ≥0) (e : ℝ) (r : ℕ) : ℝ≥0∞ :=
  ((B * A / a : ℝ≥0) : ℝ≥0∞) * ∑' j : ℕ, ((weightSeries e r j : ℝ≥0) : ℝ≥0∞)

private theorem comparisonConstant_ne_top (A a B : ℝ≥0) {e : ℝ} (he : 0 < e) (r : ℕ) :
    comparisonConstant A a B e r ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.coe_ne_top (tsum_weightSeries_ne_top he r)

private theorem ofReal_div_two_pow_rpow {Y : ℝ} (hY : 0 < Y) (e : ℝ) (j : ℕ) :
    ENNReal.ofReal ((Y / 2 ^ j) ^ e) = ENNReal.ofReal (Y ^ e) * ((ratio e : ℝ≥0) : ℝ≥0∞) ^ j := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hpow : ((2 : ℝ) ^ j) ^ e = ((2 : ℝ) ^ e) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2, mul_comm, Real.rpow_mul_natCast h2]
  have hq : ((ratio e : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ (-e)) := by
    rw [ENNReal.ofReal, ratio]
  rw [Real.div_rpow hY.le (by positivity), hpow, div_eq_mul_inv, ← inv_pow, ← Real.rpow_neg h2,
    ENNReal.ofReal_mul (Real.rpow_nonneg hY.le _), ENNReal.ofReal_pow (Real.rpow_nonneg h2 _), hq]

private theorem tsum_weight_mul_block_le (A a B : ℝ≥0) (ha : 0 < a) (e : ℝ) (r : ℕ)
    (w : ℕ → ℝ≥0∞) (μ S : ℝ → ℝ≥0∞) (Y : ℝ) (hY : 0 < Y)
    (hw : ∀ j : ℕ, w j ≤ (B : ℝ≥0∞) * ((j : ℝ≥0∞) + 1) ^ r)
    (hμ : ∀ X : ℝ, 0 < X → μ X ≤ (A : ℝ≥0∞) * ENNReal.ofReal (X ^ e))
    (hS : (a : ℝ≥0∞) * ENNReal.ofReal (Y ^ e) ≤ S Y) :
    ∑' j : ℕ, w j * μ (Y / 2 ^ j) ≤ comparisonConstant A a B e r * S Y := by
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha.ne'
  have hYa : ENNReal.ofReal (Y ^ e) ≤ S Y / a := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl ENNReal.coe_ne_top), mul_comm]
    exact hS
  have hterm : ∀ j : ℕ, w j * μ (Y / 2 ^ j) ≤
      ((B : ℝ≥0∞) * A * ENNReal.ofReal (Y ^ e)) * ((weightSeries e r j : ℝ≥0) : ℝ≥0∞) := by
    intro j
    calc w j * μ (Y / 2 ^ j)
        ≤ ((B : ℝ≥0∞) * ((j : ℝ≥0∞) + 1) ^ r) * ((A : ℝ≥0∞) * ENNReal.ofReal ((Y / 2 ^ j) ^ e)) :=
          mul_le_mul' (hw j) (hμ _ (by positivity))
      _ = ((B : ℝ≥0∞) * A * ENNReal.ofReal (Y ^ e)) * ((weightSeries e r j : ℝ≥0) : ℝ≥0∞) := by
          rw [coe_weightSeries, ofReal_div_two_pow_rpow hY]
          ring
  calc ∑' j : ℕ, w j * μ (Y / 2 ^ j)
      ≤ ∑' j : ℕ, ((B : ℝ≥0∞) * A * ENNReal.ofReal (Y ^ e)) * ((weightSeries e r j : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum hterm
    _ = ((B : ℝ≥0∞) * A * ENNReal.ofReal (Y ^ e)) * ∑' j : ℕ, ((weightSeries e r j : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.tsum_mul_left
    _ ≤ ((B : ℝ≥0∞) * A * (S Y / a)) * ∑' j : ℕ, ((weightSeries e r j : ℝ≥0) : ℝ≥0∞) := by
        gcongr
    _ = comparisonConstant A a B e r * S Y := by
        simp only [comparisonConstant]
        rw [ENNReal.coe_div ha.ne', ENNReal.coe_mul, div_eq_mul_inv, div_eq_mul_inv]
        ring

private theorem exists_const_tsum_weight_mul_block_le
    (A a B : ℝ≥0) (ha : 0 < a) (e : ℝ) (he : 0 < e) (r : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (w : ℕ → ℝ≥0∞) (μ S : ℝ → ℝ≥0∞) (Y : ℝ), 0 < Y →
        (∀ j : ℕ, w j ≤ B * ((j : ℝ≥0∞) + 1) ^ r) →
        (∀ X : ℝ, 0 < X → μ X ≤ A * ENNReal.ofReal (X ^ e)) →
        (a : ℝ≥0∞) * ENNReal.ofReal (Y ^ e) ≤ S Y →
        ∑' j : ℕ, w j * μ (Y / 2 ^ j) ≤ C * S Y :=
  ⟨comparisonConstant A a B e r, comparisonConstant_ne_top A a B he r,
    fun w μ S Y hY hw hμ hS => tsum_weight_mul_block_le A a B ha e r w μ S Y hY hw hμ hS⟩

private theorem tsum_pow_mul_block_le (A a : ℝ≥0) (ha : 0 < a) (e : ℝ) (r : ℕ)
    (μ S : ℝ → ℝ≥0∞) (Y : ℝ) (hY : 0 < Y)
    (hμ : ∀ X : ℝ, 0 < X → μ X ≤ (A : ℝ≥0∞) * ENNReal.ofReal (X ^ e))
    (hS : (a : ℝ≥0∞) * ENNReal.ofReal (Y ^ e) ≤ S Y) :
    ∑' j : ℕ, ((j : ℝ≥0∞) + 1) ^ r * μ (Y / 2 ^ j) ≤ comparisonConstant A a 1 e r * S Y :=
  tsum_weight_mul_block_le A a 1 ha e r (fun j => ((j : ℝ≥0∞) + 1) ^ r) μ S Y hY
    (fun j => by simp) hμ hS

private theorem tsum_pow_mul_block_le_of_eventually_zero (r J : ℕ) (μ S : ℝ → ℝ≥0∞) (Y : ℝ)
    (hvan : ∀ j : ℕ, J ≤ j → μ (Y / 2 ^ j) = 0)
    (hpart : ∑' j : ℕ, μ (Y / 2 ^ j) ≤ S Y) :
    ∑' j : ℕ, ((j : ℝ≥0∞) + 1) ^ r * μ (Y / 2 ^ j) ≤ (J : ℝ≥0∞) ^ r * S Y := by
  have hterm : ∀ j : ℕ, ((j : ℝ≥0∞) + 1) ^ r * μ (Y / 2 ^ j) ≤ (J : ℝ≥0∞) ^ r * μ (Y / 2 ^ j) := by
    intro j
    rcases lt_or_ge j J with hj | hj
    · have hle : (j : ℝ≥0∞) + 1 ≤ (J : ℝ≥0∞) := by exact_mod_cast hj
      gcongr
    · rw [hvan j hj, mul_zero, mul_zero]
  calc ∑' j : ℕ, ((j : ℝ≥0∞) + 1) ^ r * μ (Y / 2 ^ j)
      ≤ ∑' j : ℕ, (J : ℝ≥0∞) ^ r * μ (Y / 2 ^ j) := ENNReal.tsum_le_tsum hterm
    _ = (J : ℝ≥0∞) ^ r * ∑' j : ℕ, μ (Y / 2 ^ j) := ENNReal.tsum_mul_left
    _ ≤ (J : ℝ≥0∞) ^ r * S Y := by gcongr

private noncomputable def level (t : ℝ) : ℕ := Nat.log 2 ⌊t⌋₊

private theorem two_pow_level_le {t : ℝ} (ht : 1 ≤ t) : (2 : ℝ) ^ level t ≤ t := by
  have hm : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  have h1 : 2 ^ level t ≤ ⌊t⌋₊ := Nat.pow_log_le_self 2 (by omega)
  calc (2 : ℝ) ^ level t = ((2 ^ level t : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ t := Nat.floor_le (by linarith)

private theorem lt_two_pow_level_succ (t : ℝ) : t < (2 : ℝ) ^ (level t + 1) := by
  have h1 : ⌊t⌋₊ < 2 ^ (level t + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  calc t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    _ ≤ ((2 ^ (level t + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (2 : ℝ) ^ (level t + 1) := by push_cast; rfl

private theorem weight_le_of_level {t : ℝ} (ht : 1 ≤ t) (r : ℕ) :
    (1 + ENNReal.ofReal (Real.log t)) ^ r ≤ (2 : ℝ≥0∞) ^ r * ((level t : ℝ≥0∞) + 1) ^ r := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : Real.log t ≤ (level t : ℝ) + 1 := by
    have h1 : Real.log t ≤ Real.log ((2 : ℝ) ^ (level t + 1)) :=
      Real.log_le_log (by linarith) (lt_two_pow_level_succ t).le
    rw [Real.log_pow] at h1
    push_cast at h1
    nlinarith [hlog2, (Nat.cast_nonneg (level t) : (0 : ℝ) ≤ level t)]
  have h2 : 1 + ENNReal.ofReal (Real.log t) ≤ 2 * ((level t : ℝ≥0∞) + 1) := by
    calc 1 + ENNReal.ofReal (Real.log t) ≤ 1 + ENNReal.ofReal ((level t : ℝ) + 1) := by gcongr
      _ = 1 + ((level t : ℝ≥0∞) + 1) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      _ ≤ 2 * ((level t : ℝ≥0∞) + 1) := by
          rw [two_mul]
          gcongr
          exact le_add_self
  calc (1 + ENNReal.ofReal (Real.log t)) ^ r ≤ (2 * ((level t : ℝ≥0∞) + 1)) ^ r := by gcongr
    _ = (2 : ℝ≥0∞) ^ r * ((level t : ℝ≥0∞) + 1) ^ r := mul_pow _ _ _

private noncomputable def subLevelSum {I : Type} (N : I → ℝ) (x : I → ℝ≥0∞) (Y : ℝ) : ℝ≥0∞ :=
  ∑' i : I, {i | N i ≤ Y}.indicator x i

private theorem subLevelSum_eq {I : Type} (N : I → ℝ) (x : I → ℝ≥0∞) (Y : ℝ) :
    ∑' i : {i // N i ≤ Y}, x i = subLevelSum N x Y :=
  tsum_subtype {i | N i ≤ Y} x

private theorem subLevelSum_mono {I : Type} (N : I → ℝ) (x : I → ℝ≥0∞) {Y Z : ℝ} (h : Y ≤ Z) :
    subLevelSum N x Y ≤ subLevelSum N x Z :=
  ENNReal.tsum_le_tsum fun i =>
    Set.indicator_le_indicator_of_subset (fun i hi => show N i ≤ Z from le_trans (show N i ≤ Y from hi) h)
      (fun _ => zero_le) i

private theorem subLevelSum_eq_zero {I : Type} (N : I → ℝ) (hN : ∀ i, 1 ≤ N i) (x : I → ℝ≥0∞) {Z : ℝ}
    (hZ : Z < 1) : subLevelSum N x Z = 0 := by
  simp only [subLevelSum, ENNReal.tsum_eq_zero]
  intro i
  have : ¬ N i ≤ Z := by linarith [hN i]
  simp [this]

private theorem tsum_indicator_mul_weight_le {I : Type} (N : I → ℝ) (hN : ∀ i, 1 ≤ N i) (x : I → ℝ≥0∞)
    (r : ℕ) (X : ℝ) (𝒜 : Set I) (h𝒜 : 𝒜 ⊆ {i | N i ≤ X}) :
    ∑' i : I, 𝒜.indicator (fun i => x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r) i ≤
      ∑' j : ℕ, ((2 : ℝ≥0∞) ^ r * ((j : ℝ≥0∞) + 1) ^ r) * subLevelSum N x (X / 2 ^ j) := by
  classical
  set w : ℕ → ℝ≥0∞ := fun j => (2 : ℝ≥0∞) ^ r * ((j : ℝ≥0∞) + 1) ^ r with hw
  have hratio : ∀ i ∈ 𝒜, 1 ≤ X / N i := fun i hi => by
    have h0 : 0 < N i := by linarith [hN i]
    rw [le_div_iff₀ h0, one_mul]
    exact h𝒜 hi

  have hstep1 : ∀ i : I, 𝒜.indicator (fun i => x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r) i ≤
      ∑' j : ℕ, (if i ∈ 𝒜 ∧ level (X / N i) = j then w j * x i else 0) := by
    intro i
    by_cases hi : i ∈ 𝒜
    · have hsum : ∑' j : ℕ, (if i ∈ 𝒜 ∧ level (X / N i) = j then w j * x i else 0) =
          w (level (X / N i)) * x i := by
        have : ∀ j : ℕ, (if i ∈ 𝒜 ∧ level (X / N i) = j then w j * x i else 0) =
            (if j = level (X / N i) then w j * x i else 0) := by
          intro j
          by_cases hj : j = level (X / N i)
          · simp [hj, hi]
          · simp [hj, hi, Ne.symm hj]
        simp_rw [this]
        exact tsum_ite_eq (level (X / N i)) (fun j => w j * x i)
      rw [hsum, Set.indicator_of_mem hi, mul_comm (w _)]
      have hwt := weight_le_of_level (hratio i hi) r
      gcongr
    · rw [Set.indicator_of_notMem hi]
      exact zero_le

  have hstep2 : ∀ j : ℕ, ∑' i : I, (if i ∈ 𝒜 ∧ level (X / N i) = j then w j * x i else 0) ≤
      w j * subLevelSum N x (X / 2 ^ j) := by
    intro j
    rw [subLevelSum, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun i => ?_
    by_cases hij : i ∈ 𝒜 ∧ level (X / N i) = j
    · obtain ⟨hi, hj⟩ := hij
      have h0 : 0 < N i := by linarith [hN i]
      have hmem : i ∈ {i | N i ≤ X / 2 ^ j} := by
        show N i ≤ X / 2 ^ j
        rw [le_div_iff₀ (by positivity), ← hj]
        have h1 := two_pow_level_le (hratio i hi)
        rw [le_div_iff₀ h0] at h1
        linarith
      rw [if_pos ⟨hi, hj⟩, Set.indicator_of_mem hmem]
    · rw [if_neg hij]
      exact zero_le
  calc ∑' i : I, 𝒜.indicator (fun i => x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r) i
      ≤ ∑' i : I, ∑' j : ℕ, (if i ∈ 𝒜 ∧ level (X / N i) = j then w j * x i else 0) :=
        ENNReal.tsum_le_tsum hstep1
    _ = ∑' j : ℕ, ∑' i : I, (if i ∈ 𝒜 ∧ level (X / N i) = j then w j * x i else 0) := ENNReal.tsum_comm
    _ ≤ ∑' j : ℕ, w j * subLevelSum N x (X / 2 ^ j) := ENNReal.tsum_le_tsum hstep2

private theorem exists_const_tsum_mul_log_weight_le
    (I : Type) (N : I → ℝ) (hN : ∀ i, 1 ≤ N i) (x : I → ℝ≥0∞)
    (a c₁ C₁ Y₀ : ℝ) (ha : 0 < a) (hc₁ : 0 < c₁) (hY₀ : 1 ≤ Y₀)
    (hlow : ∀ Y, Y₀ ≤ Y → ENNReal.ofReal (c₁ * Y ^ a) ≤ ∑' i : {i // N i ≤ Y}, x i)
    (hup  : ∀ Y, Y₀ ≤ Y → ∑' i : {i // N i ≤ Y}, x i ≤ ENNReal.ofReal (C₁ * Y ^ a)) :
    ∀ (r : ℕ) (K₁ : ℝ), 1 ≤ K₁ → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (𝒜 : Set I),
      {i | N i ≤ X / K₁} ⊆ 𝒜 → 𝒜 ⊆ {i | N i ≤ X} →
      ∑' i : 𝒜, x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r ≤ C * ∑' i : 𝒜, x i := by
  intro r K₁ hK₁
  simp only [subLevelSum_eq] at hlow hup

  set Cfree : ℝ≥0∞ := (1 + ENNReal.ofReal (Real.log (K₁ * Y₀))) ^ r with hCfree

  set Ccore : ℝ≥0∞ :=
    comparisonConstant (Real.toNNReal (C₁ * Y₀ ^ a)) (Real.toNNReal c₁) (2 ^ r) a r with hCcore

  set D : ℝ≥0∞ := ENNReal.ofReal (C₁ * K₁ ^ a / c₁) with hD
  refine ⟨Cfree + Ccore * D, ?_, ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.ofReal_ne_top⟩), ENNReal.mul_ne_top (comparisonConstant_ne_top _ _ _ ha r) ENNReal.ofReal_ne_top⟩
  intro X hX 𝒜 h𝒜₁ h𝒜₂
  have hXpos : 0 < X := by linarith
  rw [tsum_subtype 𝒜 (fun i => x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r), tsum_subtype 𝒜 x]
  set M : ℝ≥0∞ := ∑' i : I, 𝒜.indicator x i with hM
  have hratio : ∀ i ∈ 𝒜, 1 ≤ X / N i := fun i hi => by
    have h0 : 0 < N i := by linarith [hN i]
    rw [le_div_iff₀ h0, one_mul]
    exact h𝒜₂ hi
  by_cases hcase : X < K₁ * Y₀
  ·
    have hterm : ∀ i : I, 𝒜.indicator (fun i => x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r) i ≤
        Cfree * 𝒜.indicator x i := by
      intro i
      by_cases hi : i ∈ 𝒜
      · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
        have h1 : Real.log (X / N i) ≤ Real.log (K₁ * Y₀) := by
          have h0 : 0 < N i := by linarith [hN i]
          refine Real.log_le_log (by positivity) ?_
          calc X / N i ≤ X := div_le_self hXpos.le (hN i)
            _ ≤ K₁ * Y₀ := hcase.le
        have hWi : (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r ≤ Cfree := by
          rw [hCfree]
          gcongr
        calc x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r ≤ x i * Cfree := by gcongr
          _ = Cfree * x i := mul_comm _ _
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero]
    calc ∑' i : I, 𝒜.indicator (fun i => x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r) i
        ≤ ∑' i : I, Cfree * 𝒜.indicator x i := ENNReal.tsum_le_tsum hterm
      _ = Cfree * M := ENNReal.tsum_mul_left
      _ ≤ (Cfree + Ccore * D) * M := by
          gcongr
          exact le_self_add
  ·
    have hcase' : K₁ * Y₀ ≤ X := not_lt.mp hcase
    have hXY₀ : Y₀ ≤ X := le_trans (le_mul_of_one_le_left (by linarith) hK₁) hcase'
    have hXK : Y₀ ≤ X / K₁ := by
      rw [le_div_iff₀ (by linarith)]
      linarith [mul_comm K₁ Y₀]

    have hC₁ : 0 < C₁ := by
      by_contra hneg
      have hneg' : C₁ ≤ 0 := not_lt.mp hneg
      have h1 := le_trans (hlow X hXY₀) (hup X hXY₀)
      have h2 : ENNReal.ofReal (C₁ * X ^ a) = 0 :=
        ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg hneg' (Real.rpow_nonneg hXpos.le a))
      rw [h2, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      have h3 : 0 < c₁ * X ^ a := mul_pos hc₁ (Real.rpow_pos_of_pos hXpos a)
      linarith

    have hμ : ∀ Z : ℝ, 0 < Z →
        subLevelSum N x Z ≤ ((Real.toNNReal (C₁ * Y₀ ^ a) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (Z ^ a) := by
      intro Z hZ
      by_cases hZ1 : Z < 1
      · rw [subLevelSum_eq_zero N hN x hZ1]
        exact zero_le
      have hZ1' : 1 ≤ Z := not_lt.mp hZ1
      have hmaxle : max Z Y₀ ≤ Y₀ * Z := by
        refine max_le ?_ ?_
        · exact le_mul_of_one_le_left hZ.le hY₀
        · exact le_mul_of_one_le_right (by linarith) hZ1'
      calc subLevelSum N x Z ≤ subLevelSum N x (max Z Y₀) := subLevelSum_mono N x (le_max_left _ _)
        _ ≤ ENNReal.ofReal (C₁ * (max Z Y₀) ^ a) := hup _ (le_max_right _ _)
        _ ≤ ENNReal.ofReal (C₁ * (Y₀ * Z) ^ a) := by
            refine ENNReal.ofReal_le_ofReal ?_
            refine mul_le_mul_of_nonneg_left ?_ hC₁.le
            exact Real.rpow_le_rpow (le_trans hZ.le (le_max_left _ _)) hmaxle ha.le
        _ = ((Real.toNNReal (C₁ * Y₀ ^ a) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (Z ^ a) := by
            rw [Real.mul_rpow (by linarith) hZ.le, ← mul_assoc, ENNReal.ofReal_mul (by positivity)]
            rfl
    have hS : ((Real.toNNReal c₁ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (X ^ a) ≤ subLevelSum N x X := by
      have h1 := hlow X hXY₀
      rwa [ENNReal.ofReal_mul hc₁.le] at h1
    have hw : ∀ j : ℕ, (2 : ℝ≥0∞) ^ r * ((j : ℝ≥0∞) + 1) ^ r ≤
        (((2 : ℝ≥0) ^ r : ℝ≥0) : ℝ≥0∞) * ((j : ℝ≥0∞) + 1) ^ r := by
      intro j
      rw [ENNReal.coe_pow, ENNReal.coe_ofNat]
    have hcore := tsum_weight_mul_block_le (Real.toNNReal (C₁ * Y₀ ^ a)) (Real.toNNReal c₁) (2 ^ r)
      (Real.toNNReal_pos.mpr hc₁) a r (fun j => (2 : ℝ≥0∞) ^ r * ((j : ℝ≥0∞) + 1) ^ r)
      (subLevelSum N x) (subLevelSum N x) X hXpos hw hμ hS

    have hreturn : subLevelSum N x X ≤ D * M := by
      have h1 : subLevelSum N x (X / K₁) ≤ M :=
        ENNReal.tsum_le_tsum fun i =>
          Set.indicator_le_indicator_of_subset h𝒜₁ (fun _ => zero_le) i
      have h2 : ENNReal.ofReal (C₁ * X ^ a) = D * ENNReal.ofReal (c₁ * (X / K₁) ^ a) := by
        rw [hD, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.div_rpow hXpos.le (by linarith)]
        field_simp
      calc subLevelSum N x X ≤ ENNReal.ofReal (C₁ * X ^ a) := hup X hXY₀
        _ = D * ENNReal.ofReal (c₁ * (X / K₁) ^ a) := h2
        _ ≤ D * subLevelSum N x (X / K₁) := by
            have h3 := hlow _ hXK
            gcongr
        _ ≤ D * M := by gcongr
    calc ∑' i : I, 𝒜.indicator (fun i => x i * (1 + ENNReal.ofReal (Real.log (X / N i))) ^ r) i
        ≤ ∑' j : ℕ, ((2 : ℝ≥0∞) ^ r * ((j : ℝ≥0∞) + 1) ^ r) * subLevelSum N x (X / 2 ^ j) :=
          tsum_indicator_mul_weight_le N hN x r X 𝒜 h𝒜₂
      _ ≤ Ccore * subLevelSum N x X := hcore
      _ ≤ Ccore * (D * M) := by gcongr
      _ = Ccore * D * M := (mul_assoc _ _ _).symm
      _ ≤ (Cfree + Ccore * D) * M := by
          gcongr
          exact le_add_self

end DyadicBlockComparison

private theorem boxGenCount_eq_zero_or (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ) :
    boxGenCount K 𝔟 H = 0 ∨
      (1 ≤ boxGenCount K 𝔟 H ∧ ∃ γ : Kˣ, FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧
        ∀ w : InfinitePlace K, w (γ : K) ≤ H w) := by
  by_cases h : ∃ γ : Kˣ, FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧ ∀ w : InfinitePlace K, w (γ : K) ≤ H w
  · obtain ⟨γ, hγ⟩ := h
    refine Or.inr ⟨?_, γ, hγ⟩
    unfold boxGenCount
    exact le_trans (le_of_eq (Set.indicator_of_mem (s := {γ : Kˣ |
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧ ∀ w : InfinitePlace K, w (γ : K) ≤ H w}) hγ
      (1 : Kˣ → ℝ≥0∞)).symm) (ENNReal.le_tsum γ)
  · refine Or.inl (ENNReal.tsum_eq_zero.mpr fun γ => Set.indicator_of_notMem (s := {γ : Kˣ |
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = 𝔟 ∧ ∀ w : InfinitePlace K, w (γ : K) ≤ H w}) ?_ (1 : Kˣ → ℝ≥0∞))
    exact fun hγ => h ⟨γ, hγ⟩

private theorem GoodIdeal.exists_spanSingleton_eq_mul_iff {S : Finset (HeightOneSpectrum (𝓞 K))}
    (𝔫 : GoodIdeal K S) {𝔟 : FractionalIdeal (𝓞 K)⁰ K} (h𝔟 : 𝔟 ≠ 0) :
    (∃ γ : Kˣ, FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) = (𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) ↔
      GoodIdeal.cls K 𝔫 = (ClassGroup.mk K (Units.mk0 𝔟 h𝔟))⁻¹ := by
  have hn : (𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr 𝔫.2.1
  rw [GoodIdeal.cls, ← ClassGroup.mk_mk0 K ⟨𝔫.1, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔫.2.1⟩,
    eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
  simp only [Units.val_mul, Units.val_mk0, FractionalIdeal.coe_mk0]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, hγ.symm⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [FractionalIdeal.spanSingleton_zero] at hx
      exact mul_ne_zero hn h𝔟 hx
    exact ⟨Units.mk0 x hx0, hx.symm⟩

private theorem classSum_eq_tsum_subtype (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (e : ℝ) (𝒞 : ClassGroup (𝓞 K)) (Y : ℝ) :
    classSum K S Ψ e 𝒞 Y =
      ∑' i : {i : {𝔫 : GoodIdeal K S | GoodIdeal.cls K 𝔫 = 𝒞} // (Ideal.absNorm i.1.1 : ℝ) ≤ Y},
        massSeq K Ψ e i.1.1.1 :=
  (Equiv.tsum_eq (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ {𝔫 : GoodIdeal K S | GoodIdeal.cls K 𝔫 = 𝒞})
      fun 𝔫 : GoodIdeal K S => (Ideal.absNorm 𝔫.1 : ℝ) ≤ Y)
    fun 𝔫 : {𝔫 : GoodIdeal K S // GoodIdeal.cls K 𝔫 = 𝒞 ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ Y} =>
      massSeq K Ψ e 𝔫.1.1).symm

private theorem exists_forall_tsum_massSeq_mul_boxGenCount_le (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {x | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (σ : ℝ) (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ σ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (Ψ : HeckeEigensystem K ℂ)
    (hV : ∃ g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ, g ≠ 0) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ), (∀ w : InfinitePlace K, 0 < H w) →
        ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 *
            boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H ≤
          C * ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 *
            boxGenCountBal K κ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H := by
  classical
  obtain ⟨K₃, hK₃, hL3⟩ := exists_forall_boxGenCount_le_mul_log_pow K
  obtain ⟨K₁, hK₁, hcov⟩ := exists_forall_one_le_boxGenCount_and_absNorm_le K
  obtain ⟨κ₀, hκ₀, hbal⟩ := exists_forall_one_le_boxGenCountBal_of_one_le_boxGenCount K
  obtain ⟨Cu, hCu, hup⟩ :=
    exists_forall_classBlock_le_and_classSum_le K α β hβ hαβ Φ₀ hΦ₀ ξ σ hξ N hN S hS hSψ Ψ hV
  obtain ⟨cL, hcL, Y₀, hY₀, hlow⟩ :=
    exists_forall_le_classSum_of_classCarriesMass K α β hβ hαβ Φ₀ hΦ₀ ξ σ hξ N hN S hS hSψ Ψ hV

  have hN1 : ∀ (𝒞 : ClassGroup (𝓞 K)) (i : {𝔫 : GoodIdeal K S | GoodIdeal.cls K 𝔫 = 𝒞}),
      (1 : ℝ) ≤ (Ideal.absNorm i.1.1 : ℝ) := fun 𝒞 i =>
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr fun h0 =>
      i.1.2.1 ((Ideal.absNorm_eq_zero_iff.mp h0).trans Submodule.zero_eq_bot.symm))

  have hbrick : ∀ 𝒞 : ClassGroup (𝓞 K), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (ClassCarriesMass K S Ψ 𝒞 →
      ∀ X : ℝ, 1 ≤ X → ∀ 𝒜 : Set {𝔫 : GoodIdeal K S | GoodIdeal.cls K 𝔫 = 𝒞},
        {i | (Ideal.absNorm i.1.1 : ℝ) ≤ X / K₁} ⊆ 𝒜 → 𝒜 ⊆ {i | (Ideal.absNorm i.1.1 : ℝ) ≤ X} →
          ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1 *
              (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1.1 : ℝ)))) ^ Units.rank K ≤
            C * ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1) := by
    intro 𝒞
    by_cases h𝒞 : ClassCarriesMass K S Ψ 𝒞
    · obtain ⟨C, hC, h⟩ := DyadicBlockComparison.exists_const_tsum_mul_log_weight_le
        {𝔫 : GoodIdeal K S | GoodIdeal.cls K 𝔫 = 𝒞} (fun i => (Ideal.absNorm i.1.1 : ℝ)) (hN1 𝒞)
        (fun i => massSeq K Ψ (1 + σ) i.1.1) 1 cL (2 * Cu.toReal) Y₀ one_pos hcL hY₀
        (fun Y hY => by
          rw [Real.rpow_one, ← classSum_eq_tsum_subtype]
          exact hlow 𝒞 h𝒞 Y hY)
        (fun Y hY => by
          have hY0 : 0 < Y := by linarith
          rw [Real.rpow_one, ← classSum_eq_tsum_subtype]
          refine ((hup 𝒞 Y hY0).2).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
            ENNReal.ofReal_toReal hCu])
        (Units.rank K) K₁ hK₁
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, ENNReal.zero_ne_top, fun h => absurd h h𝒞⟩
  choose Cc hCc hCcP using hbrick
  refine ⟨κ₀, hκ₀, K₃ * ∑ 𝒞, Cc 𝒞, ENNReal.mul_ne_top hK₃ (ENNReal.sum_ne_top.mpr fun 𝒞 _ => hCc 𝒞),
    fun 𝔟 H hH => ?_⟩

  by_cases h𝔟 : 𝔟 = 0
  · have h0 : ∀ 𝔫 : GoodIdeal K S, boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H = 0 := fun 𝔫 => by
      rcases boxGenCount_eq_zero_or K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H with h | ⟨-, γ, hγ, -⟩
      · exact h
      · exact absurd (FractionalIdeal.spanSingleton_eq_zero_iff.mp (hγ.trans (by rw [h𝔟, mul_zero])))
          γ.ne_zero
    simp only [h0, mul_zero, tsum_zero, zero_le]

  set 𝒞₀ : ClassGroup (𝓞 K) := (ClassGroup.mk K (Units.mk0 𝔟 h𝔟))⁻¹
  set I : Set (GoodIdeal K S) := {𝔫 | GoodIdeal.cls K 𝔫 = 𝒞₀}
  have hb0 : 0 < ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) := by
    have h1 : FractionalIdeal.absNorm 𝔟 ≠ 0 := fun h => h𝔟 (FractionalIdeal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg 𝔟) (Ne.symm h1)
  set X : ℝ := (∏ w : InfinitePlace K, H w ^ w.mult) / ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) with hX
  have hNb : ∀ 𝔫 : GoodIdeal K S,
      ((FractionalIdeal.absNorm ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) : ℚ) : ℝ) =
        (Ideal.absNorm 𝔫.1 : ℝ) * ((FractionalIdeal.absNorm 𝔟 : ℚ) : ℝ) := by
    intro 𝔫
    rw [map_mul, FractionalIdeal.coeIdeal_absNorm, Rat.cast_mul, Rat.cast_natCast]

  have hvan : ∀ 𝔫 : GoodIdeal K S, 𝔫 ∉ I → boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H = 0 := by
    intro 𝔫 h𝔫
    rcases boxGenCount_eq_zero_or K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H with h | ⟨-, γ, hγ, -⟩
    · exact h
    · exact absurd ((GoodIdeal.exists_spanSingleton_eq_mul_iff K 𝔫 h𝔟).mp ⟨γ, hγ⟩) h𝔫

  have hupper : ∀ i : I, 1 ≤ boxGenCount K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H →
      (Ideal.absNorm i.1.1 : ℝ) ≤ X := by
    intro i hi
    have h1 := ((hcov _ H hH).2 hi)
    rw [hNb] at h1
    rwa [hX, le_div_iff₀ hb0]
  have hlower : ∀ i : I, (Ideal.absNorm i.1.1 : ℝ) ≤ X / K₁ →
      1 ≤ boxGenCount K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H := by
    intro i hi
    refine (hcov _ H hH).1 ((GoodIdeal.exists_spanSingleton_eq_mul_iff K i.1 h𝔟).mpr i.2) ?_
    have hK0 : 0 < K₁ := by linarith
    rw [le_div_iff₀ hK0, hX, le_div_iff₀ hb0] at hi
    rw [hNb, mul_right_comm]
    exact hi
  have hcount : ∀ i : I, boxGenCount K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H ≤
      K₃ * (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1 : ℝ)))) ^ Units.rank K := by
    intro i
    have h1 := hL3 ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H
    rwa [hNb, div_mul_eq_div_div_swap, ← hX] at h1
  have hbal1 : ∀ i : I, 1 ≤ boxGenCount K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H →
      1 ≤ boxGenCountBal K κ₀ ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H :=
    fun i hi => hbal κ₀ le_rfl _ H hi

  set 𝒜 : Set I := {i | 1 ≤ boxGenCount K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H}
  have h𝒜X : 𝒜 ⊆ {i | (Ideal.absNorm i.1.1 : ℝ) ≤ X} := fun i hi => hupper i hi
  have hX𝒜 : {i : I | (Ideal.absNorm i.1.1 : ℝ) ≤ X / K₁} ⊆ 𝒜 := fun i hi => hlower i hi

  have h1 : ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 * boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H
      = ∑' i : I, massSeq K Ψ (1 + σ) i.1.1 * boxGenCount K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H := by
    rw [tsum_subtype I fun 𝔫 : GoodIdeal K S =>
      massSeq K Ψ (1 + σ) 𝔫.1 * boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H]
    refine tsum_congr fun 𝔫 => ?_
    by_cases h𝔫 : 𝔫 ∈ I
    · rw [Set.indicator_of_mem h𝔫]
    · rw [Set.indicator_of_notMem h𝔫, hvan 𝔫 h𝔫, mul_zero]

  have h2 : ∑' i : I, massSeq K Ψ (1 + σ) i.1.1 * boxGenCount K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H ≤
      ∑' i : I, 𝒜.indicator (fun i => K₃ * (massSeq K Ψ (1 + σ) i.1.1 *
        (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1 : ℝ)))) ^ Units.rank K)) i := by
    refine ENNReal.tsum_le_tsum fun i => ?_
    by_cases hi : i ∈ 𝒜
    · simp only [Set.indicator_of_mem hi]
      rw [mul_left_comm]
      exact mul_le_mul_right (hcount i) _
    · rw [Set.indicator_of_notMem hi]
      rcases boxGenCount_eq_zero_or K ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H with h | ⟨h', -⟩
      · simp [h]
      · exact absurd h' hi
  have h3 : ∑' i : I, 𝒜.indicator (fun i => K₃ * (massSeq K Ψ (1 + σ) i.1.1 *
        (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1 : ℝ)))) ^ Units.rank K)) i =
      K₃ * ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1 *
        (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1.1 : ℝ)))) ^ Units.rank K := by
    rw [← ENNReal.tsum_mul_left]
    exact (tsum_subtype 𝒜 fun i : I => K₃ * (massSeq K Ψ (1 + σ) i.1.1 *
      (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1 : ℝ)))) ^ Units.rank K)).symm

  have h4 : ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1 *
        (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1.1 : ℝ)))) ^ Units.rank K ≤
      Cc 𝒞₀ * ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1 := by
    by_cases hm : ClassCarriesMass K S Ψ 𝒞₀
    · by_cases hX1 : 1 ≤ X
      · exact hCcP 𝒞₀ hm X hX1 𝒜 hX𝒜 h𝒜X
      · refine (ENNReal.tsum_eq_zero.mpr fun i => ?_).trans_le (zero_le)
        exact absurd ((hN1 𝒞₀ i.1).trans (hupper i.1 i.2)) hX1
    · refine (ENNReal.tsum_eq_zero.mpr fun i => ?_).trans_le (zero_le)
      have hr : recValue K Ψ i.1.1.1 = 0 := by
        by_contra hr
        exact hm ⟨i.1.1, i.1.2, hr⟩
      simp [massSeq, hr]

  have h5 : ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1 ≤
      ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 *
        boxGenCountBal K κ₀ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H := by
    calc ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1
        = ∑' i : I, 𝒜.indicator (fun i => massSeq K Ψ (1 + σ) i.1.1) i :=
          tsum_subtype 𝒜 fun i : I => massSeq K Ψ (1 + σ) i.1.1
      _ ≤ ∑' i : I, massSeq K Ψ (1 + σ) i.1.1 * boxGenCountBal K κ₀ ((i.1.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          by_cases hi : i ∈ 𝒜
          · rw [Set.indicator_of_mem hi]
            exact le_mul_of_one_le_right (zero_le) (hbal1 i hi)
          · rw [Set.indicator_of_notMem hi]
            exact zero_le
      _ = ∑' 𝔫 : GoodIdeal K S, I.indicator (fun 𝔫 => massSeq K Ψ (1 + σ) 𝔫.1 *
            boxGenCountBal K κ₀ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H) 𝔫 :=
          tsum_subtype I fun 𝔫 : GoodIdeal K S => massSeq K Ψ (1 + σ) 𝔫.1 *
            boxGenCountBal K κ₀ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H
      _ ≤ ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 *
            boxGenCountBal K κ₀ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H :=
          ENNReal.tsum_le_tsum fun 𝔫 => Set.indicator_le_self _ _ 𝔫

  have h6 : Cc 𝒞₀ ≤ ∑ 𝒞, Cc 𝒞 := Finset.single_le_sum (f := Cc) (fun 𝒞 _ => zero_le) (Finset.mem_univ 𝒞₀)
  calc ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 * boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H
      ≤ K₃ * ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1 *
          (1 + ENNReal.ofReal (Real.log (X / (Ideal.absNorm i.1.1.1 : ℝ)))) ^ Units.rank K := by
        rw [h1, ← h3]; exact h2
    _ ≤ K₃ * (Cc 𝒞₀ * ∑' i : 𝒜, massSeq K Ψ (1 + σ) i.1.1.1) := mul_le_mul_right h4 _
    _ ≤ K₃ * ((∑ 𝒞, Cc 𝒞) * ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 *
          boxGenCountBal K κ₀ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H) :=
        mul_le_mul_right (mul_le_mul' h6 h5) _
    _ = K₃ * (∑ 𝒞, Cc 𝒞) * ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ (1 + σ) 𝔫.1 *
          boxGenCountBal K κ₀ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H := (mul_assoc _ _ _).symm

section WindowWeights

private def normBox (d₁ d₂ : ℝ) : Set (AdeleRing (𝓞 K) K)ˣ :=
  {b | (∀ w : InfinitePlace K, ‖((b : AdeleRing (𝓞 K) K).1 w)‖ ^ 2 ∈ Set.Icc d₁ d₂) ∧
    b ∈ AdeleRing.unitIdelesOutside (𝓞 K) K ∅}

private def normPowWeight (e : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ :=
  ENNReal.ofReal (TateGlobal.ideleNorm K z ^ e)

private def boxWeight (d₁ d₂ e : ℝ) : ℝ≥0∞ :=
  ∫⁻ b in normBox K d₁ d₂, normPowWeight K e b ∂(NumberField.Idele.idelicHaar K)

private def pointFactor (e : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  ENNReal.ofReal ((TateGlobal.ideleNorm K t * TateGlobal.ideleNorm K (GeneralLinearGroup.det k)) ^ (-(e / 2)))

private def IsFiniteAdmissibleAt (s : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : Prop :=
  ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (x : AdeleRing (𝓞 K) K),
    glFin (𝓞 K) K (unipotentGL2 x * centralScalar (𝓞 K) K z * diagOne s * k) ∈ finiteIntegralGL2 (𝓞 K) K

private def IsAdmissibleAt (c : ℝ) (s : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : Prop :=
  (∀ w : InfinitePlace K, c ≤ localHeight (archComponent K w (glArch (𝓞 K) K (diagOne s * k)))) ∧
    IsFiniteAdmissibleAt K s k

private def IsAmpleAdmissibleAt (c κ : ℝ) (s : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) : Prop :=
  IsAdmissibleAt K c s k ∧
    ∀ w w' : InfinitePlace K,
      localHeight (archComponent K w (glArch (𝓞 K) K (diagOne s * k))) ≤
        κ * localHeight (archComponent K w' (glArch (𝓞 K) K (diagOne s * k)))

end WindowWeights

section Ideles

open NumberField.AdelicVolume

variable {K}

private def archComp (w : InfinitePlace K) : (AdeleRing (𝓞 K) K)ˣ →* w.Completion :=
  (archEval K w).toMonoidHom.comp ((adeleArch (𝓞 K) K).toMonoidHom.comp (Units.coeHom (AdeleRing (𝓞 K) K)))

private theorem archComp_apply (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    archComp w z = (z : AdeleRing (𝓞 K) K).1 w := rfl

private def finComp : (AdeleRing (𝓞 K) K)ˣ →* FiniteAdeleRing (𝓞 K) K :=
  (adeleFin (𝓞 K) K).toMonoidHom.comp (Units.coeHom (AdeleRing (𝓞 K) K))

private theorem finComp_apply (z : (AdeleRing (𝓞 K) K)ˣ) : finComp z = (z : AdeleRing (𝓞 K) K).2 := rfl

private noncomputable def archIdele (a : (w : InfinitePlace K) → (w.Completion)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  ∏ w : InfinitePlace K, archCentralUnit K w (a w)

private theorem archIdele_fst (a : (w : InfinitePlace K) → (w.Completion)ˣ) (w : InfinitePlace K) :
    ((archIdele a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = a w := by
  rw [← archComp_apply, archIdele, map_prod]
  rw [Finset.prod_eq_single w]
  · rw [archComp_apply, archCentralUnit_fst_self]
  · intro w' _ hw'
    rw [archComp_apply, archCentralUnit_fst_of_ne w' (a w') (Ne.symm hw')]
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem archIdele_snd (a : (w : InfinitePlace K) → (w.Completion)ˣ) :
    ((archIdele a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := by
  rw [← finComp_apply, archIdele, map_prod]
  exact Finset.prod_eq_one fun w _ => by rw [finComp_apply, archCentralUnit_snd]

private theorem finitePartUnits_archIdele (a : (w : InfinitePlace K) → (w.Completion)ˣ) :
    NumberField.AdeleRing.finitePartUnits (𝓞 K) K (archIdele a) = 1 :=
  Units.ext (by rw [NumberField.AdeleRing.val_finitePartUnits, archIdele_snd, Units.val_one])

private theorem fst_inv_apply (z : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = ((z : AdeleRing (𝓞 K) K).1 w)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← archComp_apply, ← archComp_apply, ← map_mul, mul_inv_cancel, map_one]

private theorem fst_mul_apply (z z' : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ((z * z' : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
      = (z : AdeleRing (𝓞 K) K).1 w * (z' : AdeleRing (𝓞 K) K).1 w := by
  rw [← archComp_apply, map_mul, archComp_apply, archComp_apply]

private theorem archDetNorm_eq_norm_det (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm w g = ‖((GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ := by
  unfold archDetNorm
  congr 1

private theorem det_centralScalar' (z : (AdeleRing (𝓞 K) K)ˣ) :
    GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  rw [centralScalar, GeneralLinearGroup.det_scalar, Fintype.card_fin, sq]

private theorem det_diagOne' (s : (AdeleRing (𝓞 K) K)ˣ) : GeneralLinearGroup.det (diagOne s) = s := by
  apply Units.ext
  show Matrix.det (diagOne s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = (s : AdeleRing (𝓞 K) K)
  rw [Matrix.det_fin_two, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply]
  simp

private theorem det_unipotentGL2' (x : AdeleRing (𝓞 K) K) : GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  apply Units.ext
  show Matrix.det (unipotentGL2 x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

private theorem det_fibre (x : AdeleRing (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) (h : AdelicGL2 (𝓞 K) K) :
    GeneralLinearGroup.det (unipotentGL2 x * (centralScalar (𝓞 K) K z * h))
      = z * z * GeneralLinearGroup.det h := by
  rw [map_mul, map_mul, det_unipotentGL2', det_centralScalar', one_mul]

private theorem det_diagOne_mul_eq_mul_det (s : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    GeneralLinearGroup.det (diagOne s * k) = s * GeneralLinearGroup.det k := by
  rw [map_mul, det_diagOne']

private theorem det_glFin_mem_unitIdeles {g : AdelicGL2 (𝓞 K) K} (hg : glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K) :
    NumberField.AdeleRing.finitePartUnits (𝓞 K) K (GeneralLinearGroup.det g) ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  obtain ⟨hent, hinv⟩ := mem_finiteIntegralGL2_iff.1 hg
  have hdet : ((NumberField.AdeleRing.finitePartUnits (𝓞 K) K (GeneralLinearGroup.det g) : (FiniteAdeleRing (𝓞 K) K)ˣ)
      :
      FiniteAdeleRing (𝓞 K) K) = Matrix.det ((glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
    rw [NumberField.AdeleRing.val_finitePartUnits]
    show (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).2 = _
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [glFin_apply]
    rfl
  have hdetinv : (((NumberField.AdeleRing.finitePartUnits (𝓞 K) K (GeneralLinearGroup.det g))⁻¹ : (FiniteAdeleRing (𝓞
      K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) = Matrix.det (((glFin (𝓞 K) K g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
    rw [← map_inv, NumberField.AdeleRing.val_finitePartUnits, ← map_inv]
    show (Matrix.det ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).2 = _
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    rfl
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [hdet, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hent 0 0 v) (hent 1 1 v)) (mul_mem (hent 0 1 v) (hent 1 0 v))
  · rw [hdetinv, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hinv 0 0 v) (hinv 1 1 v)) (mul_mem (hinv 0 1 v) (hinv 1 0 v))

end Ideles

section Box

variable {K}

private theorem measurableSet_normBox (d₁ d₂ : ℝ) : MeasurableSet (normBox K d₁ d₂) := by
  have h1 : MeasurableSet {b : (AdeleRing (𝓞 K) K)ˣ |
      ∀ w : InfinitePlace K, ‖((b : AdeleRing (𝓞 K) K).1 w)‖ ^ 2 ∈ Set.Icc d₁ d₂} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun w => ?_
    refine (isClosed_Icc.preimage ?_).measurableSet
    exact ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val)).norm.pow 2
  have h2 : MeasurableSet (AdeleRing.unitIdelesOutside (𝓞 K) K ∅ : Set (AdeleRing (𝓞 K) K)ˣ) :=
    (NumberField.Idele.isOpen_unitIdelesOutside K ∅).measurableSet
  exact h1.inter h2

private theorem mem_unitIdelesOutside_empty_iff (b : (AdeleRing (𝓞 K) K)ˣ) :
    b ∈ AdeleRing.unitIdelesOutside (𝓞 K) K ∅ ↔
      NumberField.AdeleRing.finitePartUnits (𝓞 K) K b ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  rw [AdeleRing.mem_unitIdelesOutside_iff]
  constructor
  · intro h
    exact ⟨fun v => (h v (Set.notMem_empty v)).1, fun v => (h v (Set.notMem_empty v)).2⟩
  · intro h v _
    exact ⟨h.1 v, h.2 v⟩

end Box

section Weight

open NumberField.AdelicVolume NumberField.TateGlobal

variable {K}

attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

omit [NumberField K] in

private theorem exists_norm_eq (w : InfinitePlace K) {r : ℝ} (hr : 0 ≤ r) : ∃ a : w.Completion, ‖a‖ = r := by
  by_cases hw : w.IsReal
  · obtain ⟨a, ha⟩ := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).surjective r
    refine ⟨a, ?_⟩
    rw [← norm_placeEmb w a]
    simp only [placeEmb, dif_pos hw, RingHom.comp_apply, Complex.ofRealHom_eq_coe]
    rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, ha, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) (r : ℂ)
    refine ⟨a, ?_⟩
    rw [← norm_placeEmb w a]
    simp only [placeEmb, dif_neg hw]
    rw [ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem normPowWeight_mul (e : ℝ) (l b : (AdeleRing (𝓞 K) K)ˣ) :
    normPowWeight K e (l * b) = ENNReal.ofReal (ideleNorm K l ^ e) * normPowWeight K e b := by
  unfold normPowWeight
  rw [ideleNorm_mul, Real.mul_rpow (ideleNorm_pos l).le (ideleNorm_pos b).le,
    ENNReal.ofReal_mul (Real.rpow_nonneg (ideleNorm_pos l).le e)]

private theorem lintegral_indicator_translate_box (d₁ d₂ e : ℝ) (l : (AdeleRing (𝓞 K) K)ˣ) :
    ∫⁻ z, {z : (AdeleRing (𝓞 K) K)ˣ | l⁻¹ * z ∈ normBox K d₁ d₂}.indicator (normPowWeight K e) z
        ∂(NumberField.Idele.idelicHaar K)
      = ENNReal.ofReal (ideleNorm K l ^ e) * boxWeight K d₁ d₂ e := by
  rw [show (∫⁻ z, {z : (AdeleRing (𝓞 K) K)ˣ | l⁻¹ * z ∈ normBox K d₁ d₂}.indicator (normPowWeight K e) z
        ∂(NumberField.Idele.idelicHaar K))
      = ∫⁻ b, {z : (AdeleRing (𝓞 K) K)ˣ | l⁻¹ * z ∈ normBox K d₁ d₂}.indicator (normPowWeight K e) (l * b)
        ∂(NumberField.Idele.idelicHaar K) from
      (lintegral_mul_left_eq_self (μ := NumberField.Idele.idelicHaar K)
        (fun z => {z : (AdeleRing (𝓞 K) K)ˣ | l⁻¹ * z ∈ normBox K d₁ d₂}.indicator (normPowWeight K e) z)
        l).symm]
  have hfun : ∀ b : (AdeleRing (𝓞 K) K)ˣ,
      {z : (AdeleRing (𝓞 K) K)ˣ | l⁻¹ * z ∈ normBox K d₁ d₂}.indicator (normPowWeight K e) (l * b)
        = (normBox K d₁ d₂).indicator (fun b => ENNReal.ofReal (ideleNorm K l ^ e) * normPowWeight K e b) b := by
    intro b
    by_cases hb : b ∈ normBox K d₁ d₂
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (by simpa [Set.mem_setOf_eq] using hb), normPowWeight_mul]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (by simpa [Set.mem_setOf_eq] using hb)]
  simp only [hfun]
  rw [lintegral_indicator (measurableSet_normBox d₁ d₂), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

private theorem ideleNorm_eq_one_of_forall_norm_eq_one {μ : (AdeleRing (𝓞 K) K)ˣ}
    (harch : ∀ w : InfinitePlace K, ‖(μ : AdeleRing (𝓞 K) K).1 w‖ = 1)
    (hfin : NumberField.AdeleRing.finitePartUnits (𝓞 K) K μ ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K) : ideleNorm K μ = 1
        := by
  set β : (AdeleRing (𝓞 K) K)ˣ :=
    archIdele fun w => Units.mk0 ((μ : AdeleRing (𝓞 K) K).1 w) (fst_apply_ne_zero μ w) with hβ
  have hβnorm : ideleNorm K β = 1 := by
    rw [hβ, ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (archIdele_snd _)]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [archIdele_fst, Units.val_mk0, harch w, one_pow]
  have hrest : ideleNorm K (μ * β⁻¹) = 1 := by
    refine ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K (μ * β⁻¹) ?_ ?_
    · funext w
      rw [fst_mul_apply, fst_inv_apply, hβ, archIdele_fst, Units.val_mk0,
        mul_inv_cancel₀ (fst_apply_ne_zero μ w)]
      rfl
    · rw [map_mul, map_inv, hβ, finitePartUnits_archIdele, inv_one, mul_one]
      exact hfin
  have hμ := ideleNorm_mul (μ * β⁻¹) β
  rw [inv_mul_cancel_right, hrest, hβnorm, one_mul] at hμ
  exact hμ

private theorem ideleNorm_one' : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  simp [ideleNorm]

private theorem ideleNorm_principalIdele (γ : Kˣ) : ideleNorm K (principalIdele K γ) = 1 := by
  unfold ideleNorm principalIdele
  rw [NumberField.AdeleRing.distribHaarChar_algebraMap]
  simp

private theorem ideleNorm_principalIdele_inv_mul (γ : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K ((principalIdele K γ)⁻¹ * t) = ideleNorm K t := by
  have h := ideleNorm_mul (principalIdele K γ)⁻¹ (principalIdele K γ)
  rw [inv_mul_cancel, ideleNorm_one', ideleNorm_principalIdele, mul_one] at h
  rw [ideleNorm_mul, ← h, one_mul]

private theorem rpow_eq_rpow_neg_half_mul {N M : ℝ} (hN : 0 < N) (hM : 0 < M) (h : N ^ 2 * M = 1) (e : ℝ) :
    N ^ e = M ^ (-(e / 2)) := by
  have hN2 : N ^ (2 : ℝ) = M⁻¹ := by
    rw [Real.rpow_two]
    exact eq_inv_of_mul_eq_one_left h
  calc N ^ e = (N ^ (2 : ℝ)) ^ (e / 2) := by
        rw [← Real.rpow_mul hN.le]
        congr 1
        ring
    _ = M ^ (-(e / 2)) := by rw [hN2, Real.inv_rpow hM.le, ← Real.rpow_neg hM.le]

open scoped Classical in

private theorem lintegral_shadow_eq (E : Set (AdelicGL2 (𝓞 K) K)) (A : Prop) (d₁ d₂ e : ℝ)
    (s : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K)
    (hread : ∀ z : (AdeleRing (𝓞 K) K)ˣ, centralScalar (𝓞 K) K z * (diagOne s * k) ∈ unipotentShadow K E ↔
      A ∧ (∃ x : AdeleRing (𝓞 K) K,
          glFin (𝓞 K) K (unipotentGL2 x * (centralScalar (𝓞 K) K z * (diagOne s * k))) ∈ finiteIntegralGL2 (𝓞 K) K) ∧
        ∀ w : InfinitePlace K,
          ‖(z : AdeleRing (𝓞 K) K).1 w‖ ^ 2 * archDetNorm w (diagOne s * k) ∈ Set.Icc d₁ d₂) :
    ∫⁻ z, (unipotentShadow K E).indicator 1 (centralScalar (𝓞 K) K z * (diagOne s * k)) * normPowWeight K e z
        ∂(NumberField.Idele.idelicHaar K)
      = (if A ∧ IsFiniteAdmissibleAt K s k then
          boxWeight K d₁ d₂ e *
            ENNReal.ofReal ((ideleNorm K s * ideleNorm K (GeneralLinearGroup.det k)) ^ (-(e / 2)))
        else 0) := by
  have hint : (fun z : (AdeleRing (𝓞 K) K)ˣ =>
      (unipotentShadow K E).indicator 1 (centralScalar (𝓞 K) K z * (diagOne s * k)) * normPowWeight K e z)
        = fun z => {z : (AdeleRing (𝓞 K) K)ˣ |
            centralScalar (𝓞 K) K z * (diagOne s * k) ∈ unipotentShadow K E}.indicator (normPowWeight K e) z := by
    funext z
    by_cases hz : centralScalar (𝓞 K) K z * (diagOne s * k) ∈ unipotentShadow K E
    · simp [Set.indicator, hz]
    · simp [Set.indicator, hz]
  simp only [hint]
  by_cases hadm : A ∧ IsFiniteAdmissibleAt K s k
  · rw [if_pos hadm]
    obtain ⟨hA, z₀, x₀, hP₀⟩ := hadm
    have hP₀' : glFin (𝓞 K) K (unipotentGL2 x₀ * (centralScalar (𝓞 K) K z₀ * (diagOne s * k)))
        ∈ finiteIntegralGL2 (𝓞 K) K := by
      simpa only [mul_assoc] using hP₀
    have hr : ∀ w : InfinitePlace K, 0 ≤ archDetNorm w (diagOne s * k) ^ (-(1 / 2 : ℝ)) :=
      fun w => Real.rpow_nonneg (archDetNorm_pos w _).le _
    choose a ha using fun w : InfinitePlace K => exists_norm_eq w (hr w)
    have hane : ∀ w, a w ≠ 0 := fun w h0 => by
      have h := ha w
      rw [h0, norm_zero] at h
      exact (Real.rpow_pos_of_pos (archDetNorm_pos w _) _).ne h
    set l : (AdeleRing (𝓞 K) K)ˣ :=
      archIdele (fun w => Units.mk0 (a w) (hane w) * (Units.mk0 _ (fst_apply_ne_zero z₀ w))⁻¹) * z₀ with hl
    have hl_fst : ∀ w, (l : AdeleRing (𝓞 K) K).1 w = a w := fun w => by
      rw [hl, fst_mul_apply, archIdele_fst, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0,
        inv_mul_cancel_right₀ (fst_apply_ne_zero z₀ w)]
    have hl_fin : NumberField.AdeleRing.finitePartUnits (𝓞 K) K l = NumberField.AdeleRing.finitePartUnits (𝓞 K) K z₀
        := by
      rw [hl, map_mul, finitePartUnits_archIdele, one_mul]
    have hl_sq : ∀ w, ‖(l : AdeleRing (𝓞 K) K).1 w‖ ^ 2 * archDetNorm w (diagOne s * k) = 1 := fun w => by
      rw [hl_fst, ha, ← Real.rpow_natCast, ← Real.rpow_mul (archDetNorm_pos w _).le]
      norm_num
      rw [Real.rpow_neg_one]
      exact inv_mul_cancel₀ (archDetNorm_pos w _).ne'
    clear_value l
    have hset : {z : (AdeleRing (𝓞 K) K)ˣ | centralScalar (𝓞 K) K z * (diagOne s * k) ∈ unipotentShadow K E}
        = {z | l⁻¹ * z ∈ normBox K d₁ d₂} := by
      ext z
      simp only [Set.mem_setOf_eq]
      rw [hread z, exists_glFin_mem_iff_of_mem hP₀' z, normBox, Set.mem_setOf_eq, mem_unitIdelesOutside_empty_iff]
      have hband : ∀ w : InfinitePlace K,
          ‖((l⁻¹ * z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ^ 2
            = ‖(z : AdeleRing (𝓞 K) K).1 w‖ ^ 2 * archDetNorm w (diagOne s * k) := fun w => by
        rw [fst_mul_apply, fst_inv_apply, norm_mul, norm_inv, mul_pow, inv_pow,
          eq_inv_of_mul_eq_one_left (hl_sq w), inv_inv, mul_comm]
      simp only [hband, map_mul, map_inv, hl_fin]
      constructor
      · rintro ⟨-, hcos, hb⟩
        exact ⟨hb, by rwa [mul_comm] at hcos⟩
      · rintro ⟨hb, hcos⟩
        exact ⟨hA, by rwa [mul_comm] at hcos, hb⟩
    rw [hset, lintegral_indicator_translate_box]
    have hμ : ideleNorm K (l * l * (s * GeneralLinearGroup.det k)) = 1 := by
      apply ideleNorm_eq_one_of_forall_norm_eq_one
      · intro w
        rw [fst_mul_apply, fst_mul_apply, norm_mul, norm_mul, ← sq, ← det_diagOne_mul_eq_mul_det, ←
            archDetNorm_eq_norm_det]
        exact hl_sq w
      · rw [map_mul, map_mul, hl_fin, ← map_mul, ← det_diagOne_mul_eq_mul_det, ← map_mul, ← det_fibre x₀ z₀]
        exact det_glFin_mem_unitIdeles hP₀'
    rw [ideleNorm_mul, ideleNorm_mul, ideleNorm_mul, ← sq] at hμ
    rw [rpow_eq_rpow_neg_half_mul (ideleNorm_pos l) (mul_pos (ideleNorm_pos s) (ideleNorm_pos _)) hμ e, mul_comm]
  · rw [if_neg hadm]
    have hempty : {z : (AdeleRing (𝓞 K) K)ˣ |
        centralScalar (𝓞 K) K z * (diagOne s * k) ∈ unipotentShadow K E} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hz
      obtain ⟨hA', ⟨x, hx⟩, -⟩ := (hread z).1 hz
      exact hadm ⟨hA', z, x, by simpa only [mul_assoc] using hx⟩
    simp only [hempty, Set.indicator_empty, lintegral_zero]

open scoped Classical in

private theorem summand_eq (P : Kˣ → Prop) (A : Prop) (d₁ d₂ e : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ)
    (k : AdelicGL2 (𝓞 K) K) (γ : Kˣ) (hP : P γ ↔ A ∧ IsFiniteAdmissibleAt K ((principalIdele K γ)⁻¹ * t) k) :
    (if A ∧ IsFiniteAdmissibleAt K ((principalIdele K γ)⁻¹ * t) k then
        boxWeight K d₁ d₂ e * ENNReal.ofReal ((ideleNorm K ((principalIdele K γ)⁻¹ * t) *
          ideleNorm K (GeneralLinearGroup.det k)) ^ (-(e / 2)))
      else 0)
      = boxWeight K d₁ d₂ e * (pointFactor K e t k * {γ : Kˣ | P γ}.indicator 1 γ) := by
  by_cases hγ : A ∧ IsFiniteAdmissibleAt K ((principalIdele K γ)⁻¹ * t) k
  · rw [if_pos hγ, Set.indicator_of_mem (show γ ∈ {γ : Kˣ | P γ} from hP.2 hγ), Pi.one_apply, mul_one,
      pointFactor, ideleNorm_principalIdele_inv_mul]
  · rw [if_neg hγ, Set.indicator_of_notMem (show γ ∉ {γ : Kˣ | P γ} from fun h => hγ (hP.1 h)), mul_zero,
      mul_zero]

end Weight

section WeightIdentities

private theorem windowWeight_centreCutSiegelSet (c u d₁ d₂ e : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ)
    (k : AdelicGL2 (𝓞 K) K) :
    windowWeight K (centreCutSiegelSet K c u d₁ d₂) (normPowWeight K e) t k
      = boxWeight K d₁ d₂ e * pointFactor K e t k
          * ∑' γ : Kˣ, {γ : Kˣ | IsAdmissibleAt K c ((principalIdele K γ)⁻¹ * t) k}.indicator 1 γ := by
  unfold windowWeight
  simp only [mul_assoc]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [lintegral_shadow_eq (centreCutSiegelSet K c u d₁ d₂) (∀ w : InfinitePlace K,
      c ≤ localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * t) * k))))
    d₁ d₂ e _ k (fun z => ?_)]
  · exact summand_eq (fun γ => IsAdmissibleAt K c ((principalIdele K γ)⁻¹ * t) k) _ d₁ d₂ e t k γ Iff.rfl
  · rw [centralScalar_mul_mem_unipotentShadow_iff]
    tauto

private theorem windowWeight_centreCutSiegelSetAmple (c u d₁ d₂ κ e : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ)
    (k : AdelicGL2 (𝓞 K) K) :
    windowWeight K (centreCutSiegelSetAmple K c u d₁ d₂ κ) (normPowWeight K e) t k
      = boxWeight K d₁ d₂ e * pointFactor K e t k
          * ∑' γ : Kˣ, {γ : Kˣ | IsAmpleAdmissibleAt K c κ ((principalIdele K γ)⁻¹ * t) k}.indicator 1 γ := by
  unfold windowWeight
  simp only [mul_assoc]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [lintegral_shadow_eq (centreCutSiegelSetAmple K c u d₁ d₂ κ) ((∀ w : InfinitePlace K,
      c ≤ localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * t) * k)))) ∧
      ∀ w w' : InfinitePlace K,
        localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * t) * k))) ≤
          κ * localHeight (archComponent K w' (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * t) * k))))
    d₁ d₂ e _ k (fun z => ?_)]
  · refine summand_eq (fun γ => IsAmpleAdmissibleAt K c κ ((principalIdele K γ)⁻¹ * t) k)
      ((∀ w : InfinitePlace K,
          c ≤ localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * t) * k)))) ∧
        ∀ w w' : InfinitePlace K,
          localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * t) * k))) ≤
            κ * localHeight (archComponent K w' (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * t) * k))))
      d₁ d₂ e t k γ ?_
    simp only [IsAmpleAdmissibleAt, IsAdmissibleAt]
    tauto
  · rw [centralScalar_mul_mem_unipotentShadow_ample_iff, centralScalar_mul_mem_unipotentShadow_iff]
    tauto

end WeightIdentities

section CountsArch

open NumberField.AdelicVolume AutomorphicForm.SiegelCoordinates

variable {K}

private theorem archComponent_glArch_diagOne_apply (s : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K)
    (i j : Fin 2) :
    ((archComponent K w (glArch (𝓞 K) K (diagOne s)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j
      = Matrix.diagonal ![(s : AdeleRing (𝓞 K) K).1 w, 1] i j := by
  rw [archComponent_apply, glArch_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem localHeight_diagOne_mul (s : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K)
    (g : AdelicGL2 (𝓞 K) K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (diagOne s * g)))
      = ‖(s : AdeleRing (𝓞 K) K).1 w‖ * localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [map_mul, map_mul,
    localHeight_upper_entries_mul (a := (s : AdeleRing (𝓞 K) K).1 w) (t := (1 : w.Completion)) one_ne_zero
      (by rw [archComponent_glArch_diagOne_apply]; rfl) (by rw [archComponent_glArch_diagOne_apply]; rfl)
      (by rw [archComponent_glArch_diagOne_apply]; rfl),
    norm_one, div_one]

private theorem norm_principalIdele_fst_apply (γ : Kˣ) (w : InfinitePlace K) :
    ‖((principalIdele K γ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ = w (γ : K) := by
  have h : ((principalIdele K γ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = ((γ : K) : w.Completion) := rfl
  rw [h]
  exact NumberField.InfinitePlace.Completion.norm_coe w _

private theorem infinitePlace_pos (γ : Kˣ) (w : InfinitePlace K) : 0 < w (γ : K) := by
  rw [← norm_principalIdele_fst_apply]
  exact norm_pos_iff.2 (fst_apply_ne_zero _ w)

private theorem localHeight_twist (γ : Kˣ) (r : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K)
    (w : InfinitePlace K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * r) * k)))
      = (w (γ : K))⁻¹ *
          (‖(r : AdeleRing (𝓞 K) K).1 w‖ * localHeight (archComponent K w (glArch (𝓞 K) K k))) := by
  rw [localHeight_diagOne_mul, fst_mul_apply, fst_inv_apply, norm_mul, norm_inv, norm_principalIdele_fst_apply,
    mul_assoc]

private theorem le_localHeight_twist_iff {c : ℝ} (hc : 0 < c) (γ : Kˣ) (r : (AdeleRing (𝓞 K) K)ˣ)
    (k : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) :
    c ≤ localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * r) * k)))
      ↔ w (γ : K) ≤ ‖(r : AdeleRing (𝓞 K) K).1 w‖ * localHeight (archComponent K w (glArch (𝓞 K) K k)) / c := by
  have hγ := infinitePlace_pos γ w
  rw [localHeight_twist, le_div_iff₀ hc, ← div_eq_inv_mul, le_div_iff₀ hγ]
  constructor <;> intro h <;> linarith

private theorem balance_twist_iff {c : ℝ} (hc : 0 < c) (κ : ℝ) (γ : Kˣ) (r : (AdeleRing (𝓞 K) K)ˣ)
    (k : AdelicGL2 (𝓞 K) K) (w w' : InfinitePlace K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * r) * k)))
        ≤ κ * localHeight (archComponent K w' (glArch (𝓞 K) K (diagOne ((principalIdele K γ)⁻¹ * r) * k)))
      ↔ ‖((r : AdeleRing (𝓞 K) K).1 w)‖ * localHeight (archComponent K w (glArch (𝓞 K) K k)) / c * w' (γ : K)
          ≤ κ * (‖((r : AdeleRing (𝓞 K) K).1 w')‖ * localHeight (archComponent K w' (glArch (𝓞 K) K k)) / c
              * w (γ : K)) := by
  have hγ := infinitePlace_pos γ w
  have hγ' := infinitePlace_pos γ w'
  rw [localHeight_twist, localHeight_twist]
  set A := ‖(r : AdeleRing (𝓞 K) K).1 w‖ * localHeight (archComponent K w (glArch (𝓞 K) K k)) with hA
  set B := ‖(r : AdeleRing (𝓞 K) K).1 w'‖ * localHeight (archComponent K w' (glArch (𝓞 K) K k)) with hB

  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hc]
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_right h (mul_pos hγ hγ').le
    calc A * w' (γ : K) = (w (γ : K))⁻¹ * A * (w (γ : K) * w' (γ : K)) := by field_simp
      _ ≤ κ * ((w' (γ : K))⁻¹ * B) * (w (γ : K) * w' (γ : K)) := h'
      _ = κ * (B * w (γ : K)) := by field_simp
  · intro h
    have h' := mul_le_mul_of_nonneg_right h (mul_pos (inv_pos.2 hγ) (inv_pos.2 hγ')).le
    calc (w (γ : K))⁻¹ * A = A * w' (γ : K) * ((w (γ : K))⁻¹ * (w' (γ : K))⁻¹) := by field_simp
      _ ≤ κ * (B * w (γ : K)) * ((w (γ : K))⁻¹ * (w' (γ : K))⁻¹) := h'
      _ = κ * ((w' (γ : K))⁻¹ * B) := by field_simp

end CountsArch

section CountsCoset

variable {K}

private theorem glFin_diagOne_apply (u : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((glFin (𝓞 K) K (diagOne u) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
      = Matrix.diagonal ![(u : AdeleRing (𝓞 K) K).2, 1] i j := by
  rw [glFin_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem diagOne_mem_finiteIntegralGL2 {u : (AdeleRing (𝓞 K) K)ˣ}
    (hu : NumberField.AdeleRing.finitePartUnits (𝓞 K) K u ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K) :
    glFin (𝓞 K) K (diagOne u) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [FiniteAdeleRing.mem_unitIdeles_iff] at hu
  have h1 : (1 : FiniteAdeleRing (𝓞 K) K) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := fun v => one_mem _
  have h0 : (0 : FiniteAdeleRing (𝓞 K) K) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := fun v => zero_mem _
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_diagOne_apply]
    fin_cases i <;> fin_cases j
    · exact hu.1
    · exact h0
    · exact h0
    · exact h1
  · rw [← map_inv, ← map_inv, glFin_diagOne_apply]
    fin_cases i <;> fin_cases j
    · exact hu.2
    · exact h0
    · exact h0
    · exact h1

private theorem glFin_unipotent_central_diagOne_unipotent_diag (x y : AdeleRing (𝓞 K) K)
    (z u : (AdeleRing (𝓞 K) K)ˣ) :
    ((glFin (𝓞 K) K (unipotentGL2 x * centralScalar (𝓞 K) K z * diagOne u * unipotentGL2 y) :
          GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 0 0
        = ((z * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 ∧
      ((glFin (𝓞 K) K (unipotentGL2 x * centralScalar (𝓞 K) K z * diagOne u * unipotentGL2 y) :
          GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1
        = (z : AdeleRing (𝓞 K) K).2 := by

  have hmid : ∀ i j : Fin 2,
      ((glFin (𝓞 K) K (centralScalar (𝓞 K) K z * diagOne u) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
        = Matrix.diagonal ![((z * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2,
            (z : AdeleRing (𝓞 K) K).2] i j := by
    intro i j
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, glFin_centralScalar_apply,
      glFin_centralScalar_apply, glFin_diagOne_apply, glFin_diagOne_apply]
    have hzu : ((z * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
        = (z : AdeleRing (𝓞 K) K).2 * (u : AdeleRing (𝓞 K) K).2 := rfl
    fin_cases i <;> fin_cases j <;> simp [hzu, Prod.snd_mul] <;> rfl
  have hprod : unipotentGL2 x * centralScalar (𝓞 K) K z * diagOne u * unipotentGL2 y
      = unipotentGL2 x * (centralScalar (𝓞 K) K z * diagOne u) * unipotentGL2 y := by
    simp only [mul_assoc]
  rw [hprod, map_mul, map_mul, glFin_unipotentGL2_adeleFin, glFin_unipotentGL2_adeleFin, Units.val_mul, Units.val_mul]

  simp only [Matrix.mul_apply, Fin.sum_univ_two, hmid, unipotentGL2, Units.val_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, ne_eq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, not_false_eq_true, Matrix.head_fin_const]
  constructor <;> ring

private theorem finitePartUnits_mem_unitIdeles_of_entries {g g' : AdelicGL2 (𝓞 K) K}
    (hg : glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K) (hg' : glFin (𝓞 K) K g' ∈ finiteIntegralGL2 (𝓞 K) K)
    (a : (AdeleRing (𝓞 K) K)ˣ) (i : Fin 2)
    (h : ((glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i i = (a : AdeleRing (𝓞 K) K).2)
    (h' : ((glFin (𝓞 K) K g' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i i = ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2) :
    NumberField.AdeleRing.finitePartUnits (𝓞 K) K a ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  rw [FiniteAdeleRing.mem_unitIdeles_iff]
  rw [mem_finiteIntegralGL2_iff] at hg hg'
  have e1 := hg.1 i i
  have e2 := hg'.1 i i
  rw [h] at e1
  rw [h'] at e2
  exact ⟨e1, e2⟩

private theorem admissible_shape_mul_inv (k : AdelicGL2 (𝓞 K) K) (z₁ z₂ s₁ s₂ : (AdeleRing (𝓞 K) K)ˣ)
    (x₁ x₂ : AdeleRing (𝓞 K) K) :
    unipotentGL2 x₁ * centralScalar (𝓞 K) K z₁ * diagOne s₁ * k *
        (unipotentGL2 x₂ * centralScalar (𝓞 K) K z₂ * diagOne s₂ * k)⁻¹
      = unipotentGL2 x₁ * centralScalar (𝓞 K) K (z₁ * z₂⁻¹) * diagOne (s₁ * s₂⁻¹) * unipotentGL2 (-x₂) := by
  rw [map_mul, map_inv, map_mul, map_inv, ← unipotentGL2_inv]
  have hcomm : (centralScalar (𝓞 K) K z₂)⁻¹ * (diagOne s₁ * (diagOne s₂)⁻¹)
      = diagOne s₁ * (diagOne s₂)⁻¹ * (centralScalar (𝓞 K) K z₂)⁻¹ := by
    rw [← map_inv]
    exact centralScalar_mul_comm _ _
  calc unipotentGL2 x₁ * centralScalar (𝓞 K) K z₁ * diagOne s₁ * k *
          (unipotentGL2 x₂ * centralScalar (𝓞 K) K z₂ * diagOne s₂ * k)⁻¹
      = unipotentGL2 x₁ * centralScalar (𝓞 K) K z₁ *
          (diagOne s₁ * (diagOne s₂)⁻¹ * (centralScalar (𝓞 K) K z₂)⁻¹) * (unipotentGL2 x₂)⁻¹ := by group
    _ = unipotentGL2 x₁ * centralScalar (𝓞 K) K z₁ *
          ((centralScalar (𝓞 K) K z₂)⁻¹ * (diagOne s₁ * (diagOne s₂)⁻¹)) * (unipotentGL2 x₂)⁻¹ := by rw [hcomm]
    _ = _ := by group

private theorem isFiniteAdmissibleAt_iff_of_isFiniteAdmissibleAt {s : (AdeleRing (𝓞 K) K)ˣ}
    {k : AdelicGL2 (𝓞 K) K} (hs : IsFiniteAdmissibleAt K s k) (s' : (AdeleRing (𝓞 K) K)ˣ) :
    IsFiniteAdmissibleAt K s' k ↔
      NumberField.AdeleRing.finitePartUnits (𝓞 K) K (s' * s⁻¹) ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  obtain ⟨z, x, hzx⟩ := hs
  constructor
  · rintro ⟨z', x', hzx'⟩
    have hN := mul_mem hzx' (inv_mem hzx)
    have hN' := mul_mem hzx (inv_mem hzx')
    rw [← map_inv, ← map_mul, admissible_shape_mul_inv] at hN hN'
    have hd := glFin_unipotent_central_diagOne_unipotent_diag x' (-x) (z' * z⁻¹) (s' * s⁻¹)
    have hd' := glFin_unipotent_central_diagOne_unipotent_diag x (-x') (z * z'⁻¹) (s * s'⁻¹)
    have hw : NumberField.AdeleRing.finitePartUnits (𝓞 K) K (z' * z⁻¹) ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K :=
      finitePartUnits_mem_unitIdeles_of_entries hN hN' (z' * z⁻¹) 1 hd.2
        (by rw [hd'.2, _root_.mul_inv_rev, inv_inv])
    have hwu : NumberField.AdeleRing.finitePartUnits (𝓞 K) K (z' * z⁻¹ * (s' * s⁻¹)) ∈ FiniteAdeleRing.unitIdeles (𝓞
        K) K :=
      finitePartUnits_mem_unitIdeles_of_entries hN hN' (z' * z⁻¹ * (s' * s⁻¹)) 0 hd.1
        (by rw [hd'.1, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv, mul_comm])
    have hmem := mul_mem (inv_mem hw) hwu
    rwa [← map_inv, ← map_mul, inv_mul_cancel_left] at hmem
  · intro hu

    refine ⟨z, ((s' * s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x, ?_⟩
    have h1 : diagOne s' = diagOne (s' * s⁻¹) * diagOne s := by
      rw [← map_mul, inv_mul_cancel_right]
    have h2 : unipotentGL2 (((s' * s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x) * diagOne (s' * s⁻¹)
        = diagOne (s' * s⁻¹) * unipotentGL2 x := (diagOne_mul_unipotentGL2 _ _).symm
    have h3 : centralScalar (𝓞 K) K z * diagOne (s' * s⁻¹) = diagOne (s' * s⁻¹) * centralScalar (𝓞 K) K z :=
      centralScalar_mul_comm _ _
    have hrw : unipotentGL2 (((s' * s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x) *
          centralScalar (𝓞 K) K z * diagOne s' * k
        = diagOne (s' * s⁻¹) * (unipotentGL2 x * centralScalar (𝓞 K) K z * diagOne s * k) := by
      rw [h1]
      calc unipotentGL2 (((s' * s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x) * centralScalar (𝓞 K) K z *
              (diagOne (s' * s⁻¹) * diagOne s) * k
          = unipotentGL2 (((s' * s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x) *
              (centralScalar (𝓞 K) K z * diagOne (s' * s⁻¹)) * diagOne s * k := by
            simp only [mul_assoc]
        _ = unipotentGL2 (((s' * s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * x) * diagOne (s' * s⁻¹) *
              centralScalar (𝓞 K) K z * diagOne s * k := by
            rw [h3]
            simp only [mul_assoc]
        _ = diagOne (s' * s⁻¹) * unipotentGL2 x * centralScalar (𝓞 K) K z * diagOne s * k := by rw [h2]
        _ = _ := by simp only [mul_assoc]
    rw [hrw, map_mul]
    exact mul_mem (diagOne_mem_finiteIntegralGL2 hu) hzx

end CountsCoset

section CountsFinite

open NumberField.AdelicVolume NumberField.Idele

variable {K}

private theorem finitePartUnits_mem_unitIdeles_iff (b : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.AdeleRing.finitePartUnits (𝓞 K) K b ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ord K v b = 0 := by
  rw [FiniteAdeleRing.mem_unitIdeles_iff, ← forall_and]
  exact forall_congr' fun v => (ord_eq_zero_iff K v b).symm

private theorem ord_principalIdele (v : HeightOneSpectrum (𝓞 K)) (γ : Kˣ) :
    ord K v (principalIdele K γ) = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)) := by
  have h : ((principalIdele K γ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = ((γ : K) : v.adicCompletion K) :=
    rfl
  rw [ord, h, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    IsDedekindDomain.HeightOneSpectrum.valuation_eq_exp_neg_count K v γ.ne_zero, WithZero.log_exp, neg_neg]

private theorem count_finAssocFracIdeal_finitePartUnits (v : HeightOneSpectrum (𝓞 K))
    (b : (AdeleRing (𝓞 K) K)ˣ) :
    FractionalIdeal.count K v (finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K) K b)) = ord K v b := by
  rw [count_finAssocFracIdeal]
  rfl

private theorem fracIdeal_ext_of_count {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  calc I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v J :=
        finprod_congr fun v => by rw [h v]
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ

private theorem spanSingleton_eq_mul_iff_forall_ord_eq_zero {𝔫 : Ideal (𝓞 K)} (h𝔫 : 𝔫 ≠ 0)
    (b : (AdeleRing (𝓞 K) K)ˣ) (γ : Kˣ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)
        = (𝔫 : FractionalIdeal (𝓞 K)⁰ K) * finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K) K b)
      ↔ ∀ v : HeightOneSpectrum (𝓞 K), ord K v ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫 * b)) = 0 := by
  have h𝔫' : (𝔫 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr h𝔫
  have hb : finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K) K b) ≠ 0 := finAssocFracIdeal_ne_zero K _
  have hγ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K) ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).mpr γ.ne_zero

  have hord : ∀ v : HeightOneSpectrum (𝓞 K),
      ord K v ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫 * b))
        = FractionalIdeal.count K v ((𝔫 : FractionalIdeal (𝓞 K)⁰ K) * finAssocFracIdeal K
            (NumberField.AdeleRing.finitePartUnits (𝓞 K) K b))
          - FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)) := by
    intro v
    rw [ord_mul, ord_inv, ord_mul, idelePartition_ord_idealIdele K v h𝔫, ord_principalIdele,
      FractionalIdeal.count_mul K v h𝔫' hb, FractionalIdeal.count_coe K v h𝔫,
      count_finAssocFracIdeal_finitePartUnits]
    ring
  constructor
  · intro h v
    rw [hord v, h, sub_self]
  · intro h
    refine fracIdeal_ext_of_count hγ (mul_ne_zero h𝔫' hb) fun v => ?_
    have := h v
    rw [hord v, sub_eq_zero] at this
    exact this.symm

end CountsFinite

section IdealIdeleScaling

open NumberField.AdelicVolume NumberField.TateGlobal

variable {K}

private theorem fst_apply_eq_one_pow {z : (AdeleRing (𝓞 K) K)ˣ}
    (hz : ∀ w : InfinitePlace K, (z : AdeleRing (𝓞 K) K).1 w = 1) (n : ℕ)
    (w : InfinitePlace K) : ((z ^ n : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, fst_mul_apply, ih, hz, one_mul]

private theorem uniformizerIdele_fst_apply (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 :=
  rfl

private theorem idealIdele_fst_apply (𝔫 : Ideal (𝓞 K)) (w : InfinitePlace K) :
    ((idealIdele K 𝔫 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := by
  unfold idealIdele
  refine finprod_induction (fun z : (AdeleRing (𝓞 K) K)ˣ => (z : AdeleRing (𝓞 K) K).1 w = 1) rfl
    (fun a b ha hb => by
      show ((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1
      rw [fst_mul_apply, ha, hb, one_mul]) fun v => ?_
  exact fst_apply_eq_one_pow (fun w => uniformizerIdele_fst_apply v w) _ w

private theorem norm_idealIdele_mul_fst_apply (𝔫 : Ideal (𝓞 K)) (t : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ‖((idealIdele K 𝔫 * t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ = ‖(t : AdeleRing (𝓞 K) K).1 w‖ := by
  rw [fst_mul_apply, idealIdele_fst_apply, one_mul]

private theorem pointFactor_idealIdele_mul {𝔫 : Ideal (𝓞 K)} (h𝔫 : 𝔫 ≠ 0) (e : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ)
    (k : AdelicGL2 (𝓞 K) K) :
    pointFactor K e (idealIdele K 𝔫 * t) k
      = ENNReal.ofReal ((Ideal.absNorm 𝔫 : ℝ) ^ (e / 2)) * pointFactor K e t k := by
  have hN : (0 : ℝ) < ((Ideal.absNorm 𝔫 : ℕ) : ℝ) := by
    have h0 : Ideal.absNorm 𝔫 ≠ 0 := fun h =>
      h𝔫 ((Ideal.absNorm_eq_zero_iff.mp h).trans Submodule.zero_eq_bot.symm)
    exact_mod_cast Nat.pos_of_ne_zero h0
  have ht := ideleNorm_pos t
  have hk := ideleNorm_pos (GeneralLinearGroup.det k)
  unfold pointFactor
  rw [idelePartition_ideleNorm_idealIdele_mul K h𝔫, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)]
  congr 1
  have hx : ideleNorm K t / ((Ideal.absNorm 𝔫 : ℕ) : ℝ) * ideleNorm K (GeneralLinearGroup.det k)
      = ideleNorm K t * ideleNorm K (GeneralLinearGroup.det k) * (((Ideal.absNorm 𝔫 : ℕ) : ℝ))⁻¹ := by
    ring
  rw [hx, Real.mul_rpow (mul_pos ht hk).le (inv_nonneg.2 hN.le), Real.inv_rpow hN.le, Real.rpow_neg hN.le,
    inv_inv, mul_comm]

end IdealIdeleScaling

section CountsSets

open NumberField.AdelicVolume AutomorphicForm.SiegelCoordinates

variable {K}

private noncomputable def boxBound (c : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K)
    (w : InfinitePlace K) : ℝ :=
  ‖(t : AdeleRing (𝓞 K) K).1 w‖ * localHeight (archComponent K w (glArch (𝓞 K) K k)) / c

private theorem boxBound_pos {c : ℝ} (hc : 0 < c) (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K)
    (w : InfinitePlace K) : 0 < boxBound c t k w :=
  div_pos (mul_pos (norm_pos_iff.2 (fst_apply_ne_zero t w)) (localHeight_pos _)) hc

private theorem isAdmissibleAt_twist_iff {c : ℝ} (hc : 0 < c) {𝔫 : Ideal (𝓞 K)} (h𝔫 : 𝔫 ≠ 0)
    {s₀ : (AdeleRing (𝓞 K) K)ˣ} {k : AdelicGL2 (𝓞 K) K} (hs₀ : IsFiniteAdmissibleAt K s₀ k)
    (t : (AdeleRing (𝓞 K) K)ˣ) (γ : Kˣ) :
    IsAdmissibleAt K c ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫 * t)) k
      ↔ FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)
            = (𝔫 : FractionalIdeal (𝓞 K)⁰ K) * finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K) K (t *
                s₀⁻¹)) ∧
          ∀ w : InfinitePlace K, w (γ : K) ≤ boxBound c t k w := by
  unfold IsAdmissibleAt
  rw [and_comm, isFiniteAdmissibleAt_iff_of_isFiniteAdmissibleAt hs₀, finitePartUnits_mem_unitIdeles_iff,
    spanSingleton_eq_mul_iff_forall_ord_eq_zero h𝔫]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [mul_assoc, mul_assoc]
  · rw [le_localHeight_twist_iff hc, norm_idealIdele_mul_fst_apply]
    rfl

private theorem isAmpleAdmissibleAt_twist_iff {c : ℝ} (hc : 0 < c) (κ : ℝ) {𝔫 : Ideal (𝓞 K)} (h𝔫 : 𝔫 ≠ 0)
    {s₀ : (AdeleRing (𝓞 K) K)ˣ} {k : AdelicGL2 (𝓞 K) K} (hs₀ : IsFiniteAdmissibleAt K s₀ k)
    (t : (AdeleRing (𝓞 K) K)ˣ) (γ : Kˣ) :
    IsAmpleAdmissibleAt K c κ ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫 * t)) k
      ↔ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)
              = (𝔫 : FractionalIdeal (𝓞 K)⁰ K) * finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K) K (t
                  * s₀⁻¹)) ∧
            ∀ w : InfinitePlace K, w (γ : K) ≤ boxBound c t k w) ∧
          ∀ w w' : InfinitePlace K, boxBound c t k w * w' (γ : K) ≤ κ * (boxBound c t k w' * w (γ : K)) := by
  unfold IsAmpleAdmissibleAt
  rw [isAdmissibleAt_twist_iff hc h𝔫 hs₀]
  refine and_congr Iff.rfl (forall_congr' fun w => forall_congr' fun w' => ?_)
  rw [balance_twist_iff hc, norm_idealIdele_mul_fst_apply, norm_idealIdele_mul_fst_apply]
  rfl

private theorem not_isAdmissibleAt_of_forall_not {k : AdelicGL2 (𝓞 K) K}
    (h : ∀ s : (AdeleRing (𝓞 K) K)ˣ, ¬ IsFiniteAdmissibleAt K s k) (c : ℝ) (s : (AdeleRing (𝓞 K) K)ˣ) :
    ¬ IsAdmissibleAt K c s k :=
  fun hs => h s hs.2

end CountsSets

section CountsBox

open NumberField.AdelicVolume NumberField.TateGlobal

variable {K}

attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

private theorem isCompact_setOf_val_mem_and_inv_mem {U : Set (AdeleRing (𝓞 K) K)} (hU : IsCompact U) :
    IsCompact {b : (AdeleRing (𝓞 K) K)ˣ |
      (b : AdeleRing (𝓞 K) K) ∈ U ∧ ((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) ∈ U} := by
  have h : {b : (AdeleRing (𝓞 K) K)ˣ |
        (b : AdeleRing (𝓞 K) K) ∈ U ∧ ((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) ∈ U}
      = Units.embedProduct (AdeleRing (𝓞 K) K) ⁻¹' (U ×ˢ (MulOpposite.op '' U)) := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      MulOpposite.op_injective.mem_set_image]
  rw [h]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hU.prod (hU.image MulOpposite.continuous_op))

omit [NumberField K] in

private theorem isCompact_setOf_norm_le_completion (w : InfinitePlace K) (R : ℝ) :
    IsCompact {x : w.Completion | ‖x‖ ≤ R} := by
  have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hnorm : ∀ x : w.Completion, ‖NumberField.InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
    hiso.norm_map_of_map_zero (map_zero _)
  have heq : {x : w.Completion | ‖x‖ ≤ R}
      = NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall 0 R := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, hnorm]
  rw [heq]
  exact hiso.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)

private theorem isCompact_setOf_integral_and_norm_le (R : ℝ) :
    IsCompact {a : AdeleRing (𝓞 K) K |
      a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ R} := by
  have h : {a : AdeleRing (𝓞 K) K |
        a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ R}
      = (Set.pi Set.univ fun w : InfinitePlace K => {x : w.Completion | ‖x‖ ≤ R}) ×ˢ
          NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    ext a
    constructor
    · rintro ⟨h2, h1⟩
      exact ⟨Set.mem_univ_pi.mpr h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Set.mem_univ_pi.mp h1⟩
  rw [h]
  exact (isCompact_univ_pi fun w => isCompact_setOf_norm_le_completion w R).prod
    (NumberField.AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)

private theorem le_max_of_sq_mem_Icc {d₁ d₂ r : ℝ} (hd₁ : 0 < d₁) (hr : 0 ≤ r) (h : r ^ 2 ∈ Set.Icc d₁ d₂) :
    r ≤ max 1 d₂ ∧ r⁻¹ ≤ max 1 d₁⁻¹ := by
  obtain ⟨h1, h2⟩ := h
  have hr0 : 0 < r := by
    rcases hr.lt_or_eq with hr | hr
    · exact hr
    · subst hr; simp at h1; linarith
  constructor
  · rcases le_or_gt r 1 with hle | hgt
    · exact hle.trans (le_max_left _ _)
    · exact le_max_of_le_right (by nlinarith)
  · rcases le_or_gt 1 r with hle | hgt
    · exact (inv_le_one_of_one_le₀ hle).trans (le_max_left _ _)
    · refine le_max_of_le_right ?_
      rw [inv_le_inv₀ hr0 hd₁]
      nlinarith

private theorem normBox_subset_compact {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) :
    normBox K d₁ d₂ ⊆ {b : (AdeleRing (𝓞 K) K)ˣ |
      (b : AdeleRing (𝓞 K) K) ∈ {a : AdeleRing (𝓞 K) K |
          a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K ∧
            ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ max (max 1 d₂) (max 1 d₁⁻¹)} ∧
        ((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) ∈ {a : AdeleRing (𝓞 K) K |
          a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K ∧
            ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ max (max 1 d₂) (max 1 d₁⁻¹)}} := by
  rintro b ⟨harch, hfin⟩
  rw [mem_unitIdelesOutside_empty_iff, FiniteAdeleRing.mem_unitIdeles_iff] at hfin
  refine ⟨⟨hfin.1, fun w => ?_⟩, ⟨?_, fun w => ?_⟩⟩
  · exact (le_max_of_sq_mem_Icc hd₁ (norm_nonneg _) (harch w)).1.trans (le_max_left _ _)
  · exact hfin.2
  · rw [fst_inv_apply, norm_inv]
    exact (le_max_of_sq_mem_Icc hd₁ (norm_nonneg _) (harch w)).2.trans (le_max_right _ _)

private theorem idelicHaar_normBox_lt_top {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) :
    NumberField.Idele.idelicHaar K (normBox K d₁ d₂) < ⊤ :=
  (measure_mono (normBox_subset_compact hd₁)).trans_lt
    (isCompact_setOf_val_mem_and_inv_mem (isCompact_setOf_integral_and_norm_le _)).measure_lt_top

private theorem ideleNorm_eq_prod_of_finitePartUnits_mem (μ : (AdeleRing (𝓞 K) K)ˣ)
    (hfin : NumberField.AdeleRing.finitePartUnits (𝓞 K) K μ ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K) :
    ideleNorm K μ = ∏ w : InfinitePlace K, ‖(μ : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult := by
  set β : (AdeleRing (𝓞 K) K)ˣ :=
    archIdele fun w => Units.mk0 ((μ : AdeleRing (𝓞 K) K).1 w) (fst_apply_ne_zero μ w) with hβ
  have hβnorm : ideleNorm K β = ∏ w : InfinitePlace K, ‖(μ : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult := by
    rw [hβ, ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (archIdele_snd _)]
    exact Finset.prod_congr rfl fun w _ => by rw [archIdele_fst]; rfl
  have hrest : ideleNorm K (μ * β⁻¹) = 1 := by
    refine ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K (μ * β⁻¹) ?_ ?_
    · funext w
      rw [fst_mul_apply, fst_inv_apply, hβ, archIdele_fst]
      exact mul_inv_cancel₀ (fst_apply_ne_zero μ w)
    · rw [map_mul, map_inv, hβ, finitePartUnits_archIdele, inv_one, mul_one]
      exact hfin
  calc ideleNorm K μ = ideleNorm K (μ * β⁻¹ * β) := by rw [inv_mul_cancel_right]
    _ = ideleNorm K (μ * β⁻¹) * ideleNorm K β := ideleNorm_mul _ _
    _ = _ := by rw [hrest, one_mul, hβnorm]

private theorem ideleNorm_mem_Icc_of_mem_normBox {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) {b : (AdeleRing (𝓞 K) K)ˣ}
    (hb : b ∈ normBox K d₁ d₂) :
    ideleNorm K b ∈ Set.Icc (∏ w : InfinitePlace K, (min 1 d₁) ^ w.mult)
      (∏ w : InfinitePlace K, (max 1 d₂) ^ w.mult) := by
  obtain ⟨harch, hfin⟩ := hb
  rw [mem_unitIdelesOutside_empty_iff] at hfin
  rw [ideleNorm_eq_prod_of_finitePartUnits_mem b hfin]
  have hbound : ∀ w : InfinitePlace K,
      min 1 d₁ ≤ ‖(b : AdeleRing (𝓞 K) K).1 w‖ ∧ ‖(b : AdeleRing (𝓞 K) K).1 w‖ ≤ max 1 d₂ := by
    intro w
    obtain ⟨h1, h2⟩ := harch w
    have hr := norm_nonneg ((b : AdeleRing (𝓞 K) K).1 w)
    refine ⟨?_, (le_max_of_sq_mem_Icc hd₁ hr ⟨h1, h2⟩).1⟩
    rcases le_or_gt 1 ‖(b : AdeleRing (𝓞 K) K).1 w‖ with hle | hgt
    · exact (min_le_left _ _).trans hle
    · exact (min_le_right _ _).trans (by nlinarith)
  constructor
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (le_min zero_le_one hd₁.le) _)
      fun w _ => pow_le_pow_left₀ (le_min zero_le_one hd₁.le) (hbound w).1 _
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hbound w).2 _

private theorem boxWeight_ne_top {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (e : ℝ) : boxWeight K d₁ d₂ e ≠ ⊤ := by
  set lo : ℝ := ∏ w : InfinitePlace K, (min 1 d₁) ^ w.mult with hlo
  set hi : ℝ := ∏ w : InfinitePlace K, (max 1 d₂) ^ w.mult with hhi
  have hlo_pos : 0 < lo := Finset.prod_pos fun w _ => pow_pos (lt_min one_pos hd₁) _

  have hbdd : ∀ b ∈ normBox K d₁ d₂, normPowWeight K e b ≤ ENNReal.ofReal (max (lo ^ e) (hi ^ e)) := by
    intro b hb
    obtain ⟨h1, h2⟩ := ideleNorm_mem_Icc_of_mem_normBox hd₁ hb
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt 0 e with he | he
    · exact (Real.rpow_le_rpow (hlo_pos.le.trans h1) h2 he).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hlo_pos h1 he.le).trans (le_max_left _ _)
  refine ne_of_lt ?_
  calc boxWeight K d₁ d₂ e
      ≤ ∫⁻ _ in normBox K d₁ d₂, ENNReal.ofReal (max (lo ^ e) (hi ^ e)) ∂(NumberField.Idele.idelicHaar K) :=
        setLIntegral_mono' (measurableSet_normBox d₁ d₂) hbdd
    _ = ENNReal.ofReal (max (lo ^ e) (hi ^ e)) * NumberField.Idele.idelicHaar K (normBox K d₁ d₂) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (idelicHaar_normBox_lt_top hd₁)

end CountsBox

private theorem exists_forall_windowWeight_idealIdele_mul_eq_mul_boxGenCount (c u u₁ d₁ d₂ : ℝ) (hc : 0 < c)
    (hd₁ : 0 < d₁) (S : Finset (HeightOneSpectrum (𝓞 K))) (σ κ : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ)
    (k' : AdelicGL2 (𝓞 K) K) :
    ∃ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) (H : InfinitePlace K → ℝ), (∀ w : InfinitePlace K, 0 < H w) ∧
      ∃ Λ : ℝ≥0∞, Λ ≠ ⊤ ∧ ∀ 𝔫 : GoodIdeal K S,
        windowWeight K (centreCutSiegelSet K c u d₁ d₂)
              (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ)))
              (idealIdele K 𝔫.1 * t) k' =
            Λ * ENNReal.ofReal ((Ideal.absNorm 𝔫.1 : ℝ) ^ σ) *
              boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H ∧
          windowWeight K (centreCutSiegelSetAmple K c u₁ d₁ d₂ κ)
              (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ)))
              (idealIdele K 𝔫.1 * t) k' =
            Λ * ENNReal.ofReal ((Ideal.absNorm 𝔫.1 : ℝ) ^ σ) *
              boxGenCountBal K κ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H := by
  have hw : (fun z : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ)))
      = normPowWeight K (2 * σ) := rfl
  by_cases hadm : ∃ s : (AdeleRing (𝓞 K) K)ˣ, IsFiniteAdmissibleAt K s k'
  · obtain ⟨s₀, hs₀⟩ := hadm
    refine ⟨finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K) K (t * s₀⁻¹)), boxBound c t k',
        boxBound_pos hc t k',
      boxWeight K d₁ d₂ (2 * σ) * pointFactor K (2 * σ) t k',
      ENNReal.mul_ne_top (boxWeight_ne_top hd₁ _) ENNReal.ofReal_ne_top, fun 𝔫 => ?_⟩
    have h𝔫 : 𝔫.1 ≠ 0 := 𝔫.2.1
    have hpf := pointFactor_idealIdele_mul h𝔫 (2 * σ) t k'
    rw [show 2 * σ / 2 = σ by ring] at hpf
    have hset : {γ : Kˣ | IsAdmissibleAt K c ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫.1 * t)) k'}
        = {γ : Kˣ | FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)
              = (𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K) K
                  (t * s₀⁻¹)) ∧
            ∀ w : InfinitePlace K, w (γ : K) ≤ boxBound c t k' w} :=
      Set.ext fun γ => isAdmissibleAt_twist_iff hc h𝔫 hs₀ t γ
    have hsetBal : {γ : Kˣ | IsAmpleAdmissibleAt K c κ ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫.1 * t)) k'}
        = {γ : Kˣ | (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)
                = (𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * finAssocFracIdeal K (NumberField.AdeleRing.finitePartUnits (𝓞 K)
                    K (t * s₀⁻¹)) ∧
              ∀ w : InfinitePlace K, w (γ : K) ≤ boxBound c t k' w) ∧
            ∀ w w' : InfinitePlace K, boxBound c t k' w * w' (γ : K) ≤ κ * (boxBound c t k' w' * w (γ : K))} :=
      Set.ext fun γ => isAmpleAdmissibleAt_twist_iff hc κ h𝔫 hs₀ t γ
    constructor
    · rw [hw, windowWeight_centreCutSiegelSet, hpf, hset]
      unfold boxGenCount
      ring
    · rw [hw, windowWeight_centreCutSiegelSetAmple, hpf, hsetBal]
      unfold boxGenCountBal
      ring
  · have hnone : ∀ s : (AdeleRing (𝓞 K) K)ˣ, ¬ IsFiniteAdmissibleAt K s k' := fun s hs => hadm ⟨s, hs⟩
    refine ⟨1, fun _ => 1, fun _ => one_pos, 0, ENNReal.zero_ne_top, fun 𝔫 => ?_⟩
    have hempty : ∀ s : (AdeleRing (𝓞 K) K)ˣ, ¬ IsAdmissibleAt K c s k' := not_isAdmissibleAt_of_forall_not hnone c
    have h1 : {γ : Kˣ | IsAdmissibleAt K c ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫.1 * t)) k'} = ∅ :=
      Set.eq_empty_of_forall_notMem fun γ hγ => hempty _ hγ
    have h2 : {γ : Kˣ | IsAmpleAdmissibleAt K c κ ((principalIdele K γ)⁻¹ * (idealIdele K 𝔫.1 * t)) k'} = ∅ :=
      Set.eq_empty_of_forall_notMem fun γ hγ => hempty _ hγ.1
    constructor
    · rw [hw, windowWeight_centreCutSiegelSet, h1]
      simp
    · rw [hw, windowWeight_centreCutSiegelSetAmple, h2]
      simp

private theorem massSeq_one_mul_ofReal_rpow (Ψ : HeckeEigensystem K ℂ) (σ : ℝ) (𝔫 : Ideal (𝓞 K)) (h𝔫 : 𝔫 ≠ 0) :
    massSeq K Ψ 1 𝔫 * ENNReal.ofReal ((Ideal.absNorm 𝔫 : ℝ) ^ σ) = massSeq K Ψ (1 + σ) 𝔫 := by
  have h0 : Ideal.absNorm 𝔫 ≠ 0 := fun h =>
    h𝔫 ((Ideal.absNorm_eq_zero_iff.mp h).trans Submodule.zero_eq_bot.symm)
  have hN : 0 < (Ideal.absNorm 𝔫 : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
  simp only [massSeq, mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]

private theorem exists_forall_tsum_massSeq_mul_windowWeight_le (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {x | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (σ : ℝ) (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ σ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (Ψ : HeckeEigensystem K ℂ)
    (hV : ∃ g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ, g ≠ 0) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (u₁ : ℝ) (t : (AdeleRing (𝓞 K) K)ˣ) (k' : AdelicGL2 (𝓞 K) K),
        ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ 1 𝔫.1 *
            windowWeight K (centreCutSiegelSet K c u d₁ d₂)
              (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ)))
              (idealIdele K 𝔫.1 * t) k' ≤
          C * ∑' 𝔫 : GoodIdeal K S, massSeq K Ψ 1 𝔫.1 *
            windowWeight K (centreCutSiegelSetAmple K c u₁ d₁ d₂ κ)
              (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ)))
              (idealIdele K 𝔫.1 * t) k' := by
  obtain ⟨κ, hκ, C, hC, h1⟩ := exists_forall_tsum_massSeq_mul_boxGenCount_le K α β hβ hαβ Φ₀ hΦ₀ ξ σ hξ N hN S
    hS hSψ Ψ hV
  refine ⟨κ, hκ, C, hC, fun u₁ t k' => ?_⟩
  obtain ⟨𝔟, H, hH, Λ, -, h2⟩ :=
    exists_forall_windowWeight_idealIdele_mul_eq_mul_boxGenCount K c u u₁ d₁ d₂ hc hd₁ S σ κ t k'
  have hl : ∀ 𝔫 : GoodIdeal K S,
      massSeq K Ψ 1 𝔫.1 * windowWeight K (centreCutSiegelSet K c u d₁ d₂)
          (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) (idealIdele K 𝔫.1 * t) k' =
        Λ * (massSeq K Ψ (1 + σ) 𝔫.1 * boxGenCount K ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H) := fun 𝔫 => by
    rw [(h2 𝔫).1, ← massSeq_one_mul_ofReal_rpow K Ψ σ 𝔫.1 𝔫.2.1]; ring
  have hr : ∀ 𝔫 : GoodIdeal K S,
      massSeq K Ψ 1 𝔫.1 * windowWeight K (centreCutSiegelSetAmple K c u₁ d₁ d₂ κ)
          (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) (idealIdele K 𝔫.1 * t) k' =
        Λ * (massSeq K Ψ (1 + σ) 𝔫.1 * boxGenCountBal K κ ((𝔫.1 : FractionalIdeal (𝓞 K)⁰ K) * 𝔟) H) := fun 𝔫 => by
    rw [(h2 𝔫).2, ← massSeq_one_mul_ofReal_rpow K Ψ σ 𝔫.1 𝔫.2.1]; ring
  rw [tsum_congr hl, tsum_congr hr, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc, mul_comm C Λ, mul_assoc]
  exact mul_le_mul_right (h1 𝔟 H hH) Λ

section IwasawaMeasurability

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open IsDedekindDomain
open scoped ENNReal

attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_secondCountableTopology_idele cov_sigmaFinite_idelicHaar cov_countable_units

private theorem measurable_shadowIntegrand (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (γ : Kˣ) (k : AdelicGL2 (𝓞 K) K) :
    Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      E.indicator 1 (centralScalar (𝓞 K) K p.2 * diagOne ((principalIdele K γ)⁻¹ * p.1) * k) * m p.2 :=
  ((measurable_one.indicator hEm).comp
    ((((cov_continuous_centralScalar K).measurable.comp measurable_snd).mul
      ((cov_continuous_diagOne K).measurable.comp
        ((measurable_const_mul ((principalIdele K γ)⁻¹)).comp measurable_fst))).mul_const k)).mul
    (hm.comp measurable_snd)

private theorem measurable_shadowWeight (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E)
    (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m) (k : AdelicGL2 (𝓞 K) K) :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => shadowWeight K E m t k := by
  unfold shadowWeight
  exact Measurable.tsum fun γ => Measurable.lintegral_prod_right (ν := NumberField.Idele.idelicHaar K)
    (f := fun t z : (AdeleRing (𝓞 K) K)ˣ =>
      E.indicator 1 (centralScalar (𝓞 K) K z * diagOne ((principalIdele K γ)⁻¹ * t) * k) * m z)
    (measurable_shadowIntegrand K E hEm m hm γ k)

private theorem measurable_windowWeight_mul_left (W : Set (AdelicGL2 (𝓞 K) K))
    (hW : MeasurableSet (unipotentShadow K W)) (m : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hm : Measurable m)
    (a : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => windowWeight K W m (a * t) k :=
  (measurable_shadowWeight K (unipotentShadow K W) hW m hm k).comp (measurable_const_mul a)

private theorem measurable_nnnorm_whittakerCoefficient_diagOne_sq_mul (D : Set (AdelicGL2 (𝓞 K) K))
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (k : AdelicGL2 (𝓞 K) K) :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ =>
      (‖whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * k)‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) := by
  have hW : Continuous fun g : AdelicGL2 (𝓞 K) K => whittakerCoefficient K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) φ 1 g :=
    AutomorphicForm.continuous_whittakerCoefficient K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous φ hφ 1
  have hd : Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => diagOne t * k :=
    (cov_continuous_diagOne K).mul continuous_const
  exact (((hW.comp hd).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2).mul (cov_measurable_weight K)

end IwasawaMeasurability

section ArchBoxCover
variable {K}

omit [NumberField K] in

private theorem norm_algebraMap_apply (o : 𝓞 K) (w : InfinitePlace K) :
    ‖algebraMap K (InfiniteAdeleRing K) (o : K) w‖ = w (o : K) := by
  have hcoe : w.embedding (o : K) =
      InfinitePlace.Completion.extensionEmbedding w (algebraMap K w.Completion (o : K)) := by
    rw [show algebraMap K w.Completion (o : K) = ((WithAbs.equiv w.1).symm (o : K) : w.Completion)
        from rfl,
      InfinitePlace.Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply]
  show ‖algebraMap K w.Completion (o : K)‖ = w (o : K)
  rw [← InfinitePlace.norm_embedding_eq, hcoe,
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]

private theorem finite_setOf_forall_apply_le (M : ℝ) :
    {o : 𝓞 K | ∀ w : InfinitePlace K, w (o : K) ≤ M}.Finite := by
  have hfin := Embeddings.finite_of_norm_le K ℂ M
  refine (hfin.preimage (f := fun o : 𝓞 K => (o : K)) ?_).subset ?_
  · exact fun a _ b _ hab => RingOfIntegers.ext hab
  · intro o ho
    refine ⟨RingOfIntegers.isIntegral_coe o, fun φ => ?_⟩
    have h := ho (InfinitePlace.mk φ)
    rwa [InfinitePlace.apply] at h

private theorem exists_forall_exists_finset_size_le_forall_exists_mem_add_mem
    (B : Set (InfiniteAdeleRing K)) (R : ℝ)
    (hB : ∀ y ∈ B, ∀ w : InfinitePlace K, ‖y w‖ ≤ R)
    (hcov : ∀ x : InfiniteAdeleRing K, ∃ o : 𝓞 K, algebraMap K (InfiniteAdeleRing K) (o : K) + x ∈ B)
    (r : ℝ) :
    ∃ N : ℕ, ∀ z : InfiniteAdeleRing K, ∃ A : Finset (𝓞 K), A.card ≤ N ∧
      ∀ y : InfiniteAdeleRing K, (∀ w : InfinitePlace K, ‖y w - z w‖ ≤ r) →
        ∃ o ∈ A, algebraMap K (InfiniteAdeleRing K) (o : K) + y ∈ B := by
  have hS := finite_setOf_forall_apply_le (K := K) (2 * R + r)
  classical
  refine ⟨hS.toFinset.card, fun z => ?_⟩
  obtain ⟨oz, hoz⟩ := hcov z
  refine ⟨hS.toFinset.image (fun η => η + oz), Finset.card_image_le, fun y hy => ?_⟩
  obtain ⟨oy, hoy⟩ := hcov y
  refine ⟨oy, ?_, hoy⟩
  rw [Finset.mem_image]
  refine ⟨oy - oz, ?_, sub_add_cancel oy oz⟩
  rw [Set.Finite.mem_toFinset]
  intro w
  rw [← norm_algebraMap_apply]
  have hsplit : algebraMap K (InfiniteAdeleRing K) ((oy - oz : 𝓞 K) : K) w =
      (algebraMap K (InfiniteAdeleRing K) (oy : K) + y) w
        - (algebraMap K (InfiniteAdeleRing K) (oz : K) + z) w - (y w - z w) := by
    simp only [map_sub]
    show algebraMap K (InfiniteAdeleRing K) (oy : K) w - algebraMap K (InfiniteAdeleRing K) (oz : K) w
      = (algebraMap K (InfiniteAdeleRing K) (oy : K) w + y w)
        - (algebraMap K (InfiniteAdeleRing K) (oz : K) w + z w) - (y w - z w)
    ring
  rw [hsplit]
  calc ‖(algebraMap K (InfiniteAdeleRing K) (oy : K) + y) w
          - (algebraMap K (InfiniteAdeleRing K) (oz : K) + z) w - (y w - z w)‖
      ≤ ‖(algebraMap K (InfiniteAdeleRing K) (oy : K) + y) w
          - (algebraMap K (InfiniteAdeleRing K) (oz : K) + z) w‖ + ‖y w - z w‖ := norm_sub_le _ _
    _ ≤ (‖(algebraMap K (InfiniteAdeleRing K) (oy : K) + y) w‖
          + ‖(algebraMap K (InfiniteAdeleRing K) (oz : K) + z) w‖) + ‖y w - z w‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (R + R) + r := add_le_add (add_le_add (hB _ hoy w) (hB _ hoz w)) (hy w)
    _ = 2 * R + r := by ring

end ArchBoxCover

section Unfolding

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

omit [NumberField K] in

private theorem norm_sub_le_of_xWindowSq_le (w : InfinitePlace K) {u : ℝ} {y y' : w.Completion}
    {g : GL (Fin 2) w.Completion} (hy : xWindowSq (unipotentGL2 y * g) ≤ u ^ 2)
    (hy' : xWindowSq (unipotentGL2 y' * g) ≤ u ^ 2) :
    ‖y - y'‖ ≤ 2 * |u| := by
  rw [xWindowSq_unipotentGL2_mul] at hy hy'
  set φ := InfinitePlace.Completion.extensionEmbedding w
  set c := SiegelCoordinates.xCoord ((g : Matrix (Fin 2) (Fin 2) w.Completion).map φ)
  have h1 : ‖c + φ y‖ ≤ |u| :=
    le_of_pow_le_pow_left₀ two_ne_zero (abs_nonneg u) (by rw [sq_abs]; exact hy)
  have h2 : ‖c + φ y'‖ ≤ |u| :=
    le_of_pow_le_pow_left₀ two_ne_zero (abs_nonneg u) (by rw [sq_abs]; exact hy')
  calc ‖y - y'‖ = ‖φ (y - y')‖ := (SiegelCoordinates.norm_extensionEmbedding w _).symm
    _ = ‖(c + φ y) - (c + φ y')‖ := by rw [map_sub]; congr 1; ring
    _ ≤ ‖c + φ y‖ + ‖c + φ y'‖ := norm_sub_le _ _
    _ ≤ |u| + |u| := add_le_add h1 h2
    _ = 2 * |u| := by ring

private theorem algebraMap_int_mem_integralFiniteAdeles (o : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (o : K) ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
  fun v => NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 K) K v o

private theorem fibre_facts {c u d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 K) K} {x : AdeleRing (𝓞 K) K}
    (hx : unipotentGL2 x * g ∈ centreCutSiegelSet K c u d₁ d₂) :
    (∀ w : InfinitePlace K,
      xWindowSq (unipotentGL2 (AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K x)) *
        AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g)) ≤ u ^ 2) ∧
    unipotentGL2 (AdelicLevel.adeleFin (𝓞 K) K x) * AdelicLevel.glFin (𝓞 K) K g ∈
      AdelicLevel.finiteIntegralGL2 (𝓞 K) K := by
  obtain ⟨hfin, -, hwin, -⟩ := mem_centreCutSiegelSet_iff.mp hx
  refine ⟨fun w => ?_, ?_⟩
  · have h := hwin w
    rwa [map_mul, glArch_unipotentGL2_adeleArch, map_mul, archComponent_unipotentGL2] at h
  · rwa [map_mul, glFin_unipotentGL2_adeleFin] at hfin

private theorem sub_mem_integralFiniteAdeles_of_mul_mem {G : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    {a b : FiniteAdeleRing (𝓞 K) K}
    (ha : unipotentGL2 a * G ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K)
    (hb : unipotentGL2 b * G ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) :
    a - b ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hm : unipotentGL2 (a - b) ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K := by
    have h := Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)
    have hEq : unipotentGL2 a * G * (unipotentGL2 b * G)⁻¹ = unipotentGL2 (a - b) := by
      rw [_root_.mul_inv_rev, unipotentGL2_inv, sub_eq_add_neg, unipotentGL2_add, mul_assoc,
        ← mul_assoc G, mul_inv_cancel, one_mul]
    rwa [hEq] at h
  have h01 := (AdelicLevel.mem_finiteIntegralGL2_iff.mp hm).1 0 1
  simpa using h01

private theorem mem_image_mul_right_iff {S : Set (AdelicGL2 (𝓞 K) K)} {x₀ h : AdelicGL2 (𝓞 K) K}
    (x : AdeleRing (𝓞 K) K) :
    unipotentGL2 x * h ∈ (· * x₀) '' S ↔ unipotentGL2 x * (h * x₀⁻¹) ∈ S := by
  rw [Set.image_mul_right, Set.mem_preimage, mul_assoc]

omit [NumberField K] in

private theorem xWindowSq_unipotentGL2_mul_le_of_close (w : InfinitePlace K) {u₁ u' δ : ℝ}
    {y y₁ : w.Completion} {g : GL (Fin 2) w.Completion}
    (hy₁ : xWindowSq (unipotentGL2 y₁ * g) ≤ u₁ ^ 2) (hd : ‖y - y₁‖ ≤ δ) (hu : |u₁| + δ ≤ u') :
    xWindowSq (unipotentGL2 y * g) ≤ u' ^ 2 := by
  rw [xWindowSq_unipotentGL2_mul] at hy₁ ⊢
  set φ := InfinitePlace.Completion.extensionEmbedding w
  set c := SiegelCoordinates.xCoord ((g : Matrix (Fin 2) (Fin 2) w.Completion).map φ)
  have h₁ : ‖c + φ y₁‖ ≤ |u₁| :=
    le_of_pow_le_pow_left₀ two_ne_zero (abs_nonneg u₁) (by rw [sq_abs]; exact hy₁)
  have h₂ : ‖c + φ y‖ ≤ u' :=
    calc ‖c + φ y‖ = ‖(c + φ y₁) + φ (y - y₁)‖ := by rw [map_sub]; congr 1; ring
      _ ≤ ‖c + φ y₁‖ + ‖φ (y - y₁)‖ := norm_add_le _ _
      _ = ‖c + φ y₁‖ + ‖y - y₁‖ := by rw [SiegelCoordinates.norm_extensionEmbedding]
      _ ≤ |u₁| + δ := add_le_add h₁ hd
      _ ≤ u' := hu
  exact pow_le_pow_left₀ (norm_nonneg _) h₂ 2

private theorem unipotentGL2_mul_mem_ample_of_close {c u₁ u' d₁ d₂ κ δ : ℝ} {g : AdelicGL2 (𝓞 K) K}
    {x₁ y : AdeleRing (𝓞 K) K} (hx₁ : unipotentGL2 x₁ * g ∈ centreCutSiegelSetAmple K c u₁ d₁ d₂ κ)
    (hu : |u₁| + δ ≤ u')
    (harch : ∀ w : InfinitePlace K,
      ‖AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K y) -
        AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K x₁)‖ ≤ δ)
    (hfin : AdelicLevel.adeleFin (𝓞 K) K y - AdelicLevel.adeleFin (𝓞 K) K x₁ ∈
      AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    unipotentGL2 y * g ∈ centreCutSiegelSetAmple K c u' d₁ d₂ κ := by
  obtain ⟨hplain, hbal⟩ := mem_centreCutSiegelSetAmple_iff.mp hx₁
  obtain ⟨hint, hht, hwin, hdet⟩ := mem_centreCutSiegelSet_iff.mp hplain
  refine mem_centreCutSiegelSetAmple_iff.mpr ⟨mem_centreCutSiegelSet_iff.mpr
    ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩, fun w w' => ?_⟩
  · rw [glFin_unipotentGL2_mul] at hint ⊢
    have hsplit : unipotentGL2 (AdelicLevel.adeleFin (𝓞 K) K y) =
        unipotentGL2 (AdelicLevel.adeleFin (𝓞 K) K y - AdelicLevel.adeleFin (𝓞 K) K x₁) *
          unipotentGL2 (AdelicLevel.adeleFin (𝓞 K) K x₁) := by
      rw [← unipotentGL2_add, sub_add_cancel]
    rw [hsplit, mul_assoc]
    exact Subgroup.mul_mem _ (unipotentGL2_mem_finiteIntegralGL2 hfin) hint
  · have h := hht w
    rw [archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul] at h ⊢
    exact h
  · have h := hwin w
    rw [archComponent_glArch_unipotentGL2_mul] at h ⊢
    exact xWindowSq_unipotentGL2_mul_le_of_close K w h (harch w) hu
  · rw [archDetNorm_unipotentGL2_mul]
    have h := hdet w
    rwa [archDetNorm_unipotentGL2_mul] at h
  · have h := hbal w w'
    rw [archComponent_glArch_unipotentGL2_mul, archComponent_glArch_unipotentGL2_mul,
      localHeight_unipotentGL2_mul, localHeight_unipotentGL2_mul] at h ⊢
    exact h

private def UnipotentPeriodic (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞) : Prop :=
  ∀ (ξ : K) (x : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
    F (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ + x) * h) = F (unipotentGL2 x * h)

private noncomputable def boxMass (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (h : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  ∫⁻ x in adelicBox K, F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K)

private theorem measurableSet_image_add_adelicBox (a : AdeleRing (𝓞 K) K) :
    MeasurableSet ((fun x => a + x) '' adelicBox K) := by
  rw [Set.image_add_left]
  exact (continuous_const_add (-a)).measurable (measurableSet_adelicBox K)

private theorem setLIntegral_image_add_adelicBox (G : AdeleRing (𝓞 K) K → ℝ≥0∞) (a : AdeleRing (𝓞 K) K) :
    ∫⁻ x in (fun x => a + x) '' adelicBox K, G x ∂(adelicAddHaar (𝓞 K) K) =
      ∫⁻ b in adelicBox K, G (a + b) ∂(adelicAddHaar (𝓞 K) K) := by
  have hpre : MeasurableSet ((fun x => -a + x) ⁻¹' adelicBox K) :=
    (continuous_const_add (-a)).measurable (measurableSet_adelicBox K)
  rw [Set.image_add_left, ← lintegral_indicator hpre, ← lintegral_indicator (measurableSet_adelicBox K),
    ← lintegral_add_left_eq_self (((fun x => -a + x) ⁻¹' adelicBox K).indicator G) a]
  refine lintegral_congr fun x => ?_
  have hmem : a + x ∈ (fun x => -a + x) ⁻¹' adelicBox K ↔ x ∈ adelicBox K := by
    show -a + (a + x) ∈ adelicBox K ↔ _
    rw [neg_add_cancel_left]
  by_cases hx : x ∈ adelicBox K
  · rw [Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (hmem.1 h)), Set.indicator_of_notMem hx]

private theorem setLIntegral_image_add_adelicBox_eq_boxMass {F : AdelicGL2 (𝓞 K) K → ℝ≥0∞}
    (hper : UnipotentPeriodic K F) (ξ : K) (h : AdelicGL2 (𝓞 K) K) :
    ∫⁻ x in (fun x => algebraMap K (AdeleRing (𝓞 K) K) ξ + x) '' adelicBox K, F (unipotentGL2 x * h)
        ∂(adelicAddHaar (𝓞 K) K) = boxMass K F h := by
  rw [setLIntegral_image_add_adelicBox]
  exact lintegral_congr fun b => hper ξ b h

private theorem exists_forall_exists_finset_le_fibre_subset_iUnion_vadd_adelicBox (u : ℝ) :
    ∃ N : ℕ, ∀ (c d₁ d₂ : ℝ) (x₀ h : AdelicGL2 (𝓞 K) K),
      ∃ A : Finset K, A.card ≤ N ∧
        {x : AdeleRing (𝓞 K) K | unipotentGL2 x * h ∈ (· * x₀) '' centreCutSiegelSet K c u d₁ d₂} ⊆
          ⋃ ξ ∈ A, (fun x => algebraMap K (AdeleRing (𝓞 K) K) ξ + x) '' adelicBox K := by
  classical
  obtain ⟨R, hR⟩ := exists_forall_norm_apply_le_of_mem_infiniteBox K
  obtain ⟨N, hN⟩ := exists_forall_exists_finset_size_le_forall_exists_mem_add_mem
    (infiniteBox K) R hR (fun z => (existsUnique_int_add_mem_infiniteBox K z).exists) (2 * |u|)
  refine ⟨N, fun c d₁ d₂ x₀ h => ?_⟩
  by_cases hne : ∃ x₁ : AdeleRing (𝓞 K) K,
    unipotentGL2 x₁ * h ∈ (· * x₀) '' centreCutSiegelSet K c u d₁ d₂
  swap
  · exact ⟨∅, by simp, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨x₁, hx₁⟩ := hne
  obtain ⟨ξ₁, hξ₁, -⟩ := existsUnique_algebraMap_add_mem_adelicBox K x₁
  obtain ⟨A₀, hA₀, hcover⟩ := hN (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).1
  refine ⟨A₀.image (fun o : 𝓞 K => -((o : K) + ξ₁)), Finset.card_image_le.trans hA₀, fun x hx => ?_⟩
  have hx' := fibre_facts K ((mem_image_mul_right_iff K x).mp hx)
  have hx₁' := fibre_facts K ((mem_image_mul_right_iff K x₁).mp hx₁)

  have harch : ∀ w : InfinitePlace K,
      ‖(algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x).1 w -
        (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).1 w‖ ≤ 2 * |u| := fun w => by
    have hsep := norm_sub_le_of_xWindowSq_le K w (hx'.1 w) (hx₁'.1 w)
    have hEq : (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x).1 w -
        (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).1 w =
          AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K x) -
            AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K x₁) := by
      show (algebraMap K (InfiniteAdeleRing K) ξ₁ w + x.1 w) -
        (algebraMap K (InfiniteAdeleRing K) ξ₁ w + x₁.1 w) = x.1 w - x₁.1 w
      ring
    rw [hEq]
    exact hsep
  obtain ⟨o, ho, hbox⟩ := hcover _ harch

  have hfin : (algebraMap K (AdeleRing (𝓞 K) K) ((o : K) + ξ₁) + x).2 ∈
      AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    have h1 : (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).2 ∈
        AdelicLevel.integralFiniteAdeles (𝓞 K) K := hξ₁.2
    have h2 := sub_mem_integralFiniteAdeles_of_mul_mem K hx'.2 hx₁'.2
    have h3 := algebraMap_int_mem_integralFiniteAdeles K o
    have hEq : (algebraMap K (AdeleRing (𝓞 K) K) ((o : K) + ξ₁) + x).2 =
        algebraMap K (FiniteAdeleRing (𝓞 K) K) (o : K) +
          ((algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).2 +
            (AdelicLevel.adeleFin (𝓞 K) K x - AdelicLevel.adeleFin (𝓞 K) K x₁)) := by
      show algebraMap K (FiniteAdeleRing (𝓞 K) K) ((o : K) + ξ₁) + x.2 =
        algebraMap K (FiniteAdeleRing (𝓞 K) K) (o : K) +
          ((algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ₁ + x₁.2) + (x.2 - x₁.2))
      rw [map_add]
      ring
    rw [hEq]
    exact AdelicLevel.add_mem_integralFiniteAdeles h3 (AdelicLevel.add_mem_integralFiniteAdeles h1 h2)
  refine Set.mem_iUnion₂.mpr ⟨-((o : K) + ξ₁), Finset.mem_image_of_mem _ ho,
    algebraMap K (AdeleRing (𝓞 K) K) ((o : K) + ξ₁) + x, ⟨?_, hfin⟩, ?_⟩
  · have hEq : (algebraMap K (AdeleRing (𝓞 K) K) ((o : K) + ξ₁) + x).1 =
        algebraMap K (InfiniteAdeleRing K) (o : K) + (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x).1 := by
      show algebraMap K (InfiniteAdeleRing K) ((o : K) + ξ₁) + x.1 =
        algebraMap K (InfiniteAdeleRing K) (o : K) + (algebraMap K (InfiniteAdeleRing K) ξ₁ + x.1)
      rw [map_add, add_assoc]
    rw [hEq]
    exact hbox
  · simp only [map_neg, neg_add_cancel_left]

private theorem exists_forall_setLIntegral_image_centreCutSiegelSet_le_mul_lintegral_boxMass (u : ℝ) :
    ∃ N : ℕ, ∀ (c d₁ d₂ : ℝ) (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞), Measurable F → UnipotentPeriodic K F →
      ∀ x₀ : AdelicGL2 (𝓞 K) K,
        ∫⁻ g in (· * x₀) '' centreCutSiegelSet K c u d₁ d₂, F g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
          N * (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ *
            ∫⁻ q, (unipotentShadow K ((· * x₀) '' centreCutSiegelSet K c u d₁ d₂)).indicator
              (boxMass K F) q.out ∂(unipotentQuotientMeasure K)) := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_exists_finset_le_fibre_subset_iUnion_vadd_adelicBox K u
  refine ⟨N, fun c d₁ d₂ F hF hper x₀ => ?_⟩
  set W := (· * x₀) '' centreCutSiegelSet K c u d₁ d₂ with hW
  have hWm : MeasurableSet W := by
    rw [hW, Set.image_mul_right]
    exact (continuous_mul_const x₀⁻¹).measurable (measurableSet_centreCutSiegelSet c u d₁ d₂)
  rw [← lintegral_indicator hWm F,
    lintegral_adelicGLHaar_eq_mul_lintegral_unipotentQuotientMeasure K _ (hF.indicator hWm)]

  have hfibre : ∀ h : AdelicGL2 (𝓞 K) K,
      ∫⁻ x, W.indicator F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K) ≤
        (unipotentShadow K W).indicator (fun h => (N : ℝ≥0∞) * boxMass K F h) h := by
    intro h
    by_cases hsh : h ∈ unipotentShadow K W
    · rw [Set.indicator_of_mem hsh]
      obtain ⟨A, hA, hsub⟩ := hN c d₁ d₂ x₀ h
      set U : Set (AdeleRing (𝓞 K) K) :=
        ⋃ ξ ∈ A, (fun x => algebraMap K (AdeleRing (𝓞 K) K) ξ + x) '' adelicBox K with hU
      have hpw : ∀ x, W.indicator F (unipotentGL2 x * h) ≤
          U.indicator (fun x => F (unipotentGL2 x * h)) x := by
        intro x
        by_cases hx : unipotentGL2 x * h ∈ W
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub hx)]
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
      have hUm : MeasurableSet U :=
        A.measurableSet_biUnion fun ξ _ => measurableSet_image_add_adelicBox K _
      calc ∫⁻ x, W.indicator F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K)
          ≤ ∫⁻ x, U.indicator (fun x => F (unipotentGL2 x * h)) x ∂(adelicAddHaar (𝓞 K) K) :=
            lintegral_mono hpw
        _ = ∫⁻ x in U, F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K) := lintegral_indicator hUm _
        _ ≤ ∫⁻ x in ⋃ ξ : A, (fun x => algebraMap K (AdeleRing (𝓞 K) K) ξ.1 + x) '' adelicBox K,
              F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K) :=
            lintegral_mono_set fun x hx => by
              obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hx
              exact Set.mem_iUnion.mpr ⟨⟨ξ, hξ⟩, hxξ⟩
        _ ≤ ∑' ξ : A, ∫⁻ x in (fun x => algebraMap K (AdeleRing (𝓞 K) K) ξ.1 + x) '' adelicBox K,
              F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K) := lintegral_iUnion_le _ _
        _ = ∑' _ξ : A, boxMass K F h :=
            tsum_congr fun ξ => setLIntegral_image_add_adelicBox_eq_boxMass K hper ξ.1 h
        _ = (A.card : ℝ≥0∞) * boxMass K F h := by
            rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        _ ≤ (N : ℝ≥0∞) * boxMass K F h :=
            mul_le_mul (by exact_mod_cast hA) le_rfl zero_le zero_le
    · rw [Set.indicator_of_notMem hsh]
      have hzero : ∀ x : AdeleRing (𝓞 K) K, W.indicator F (unipotentGL2 x * h) = 0 := fun x =>
        Set.indicator_of_notMem (fun hx => hsh ⟨x, hx⟩) F
      simp only [hzero, lintegral_zero, le_refl]
  refine le_trans (mul_le_mul le_rfl (lintegral_mono fun q => hfibre q.out) zero_le zero_le)
    (le_of_eq ?_)
  have hind : ∀ h : AdelicGL2 (𝓞 K) K,
      (unipotentShadow K W).indicator (fun h => (N : ℝ≥0∞) * boxMass K F h) h =
        (N : ℝ≥0∞) * (unipotentShadow K W).indicator (boxMass K F) h := fun h => by
    by_cases hsh : h ∈ unipotentShadow K W
    · rw [Set.indicator_of_mem hsh, Set.indicator_of_mem hsh]
    · rw [Set.indicator_of_notMem hsh, Set.indicator_of_notMem hsh, mul_zero]
  simp only [hind]
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N), mul_left_comm]

private theorem exists_forall_lintegral_boxMass_le_setLIntegral_image_centreCutSiegelSetAmple :
    ∃ δ : ℝ, ∀ (c u₁ u' d₁ d₂ κ : ℝ), |u₁| + δ ≤ u' →
      ∀ (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞), Measurable F → UnipotentPeriodic K F →
        ∀ x₀ : AdelicGL2 (𝓞 K) K,
          ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ *
              ∫⁻ q, (unipotentShadow K ((· * x₀) '' centreCutSiegelSetAmple K c u₁ d₁ d₂ κ)).indicator
                (boxMass K F) q.out ∂(unipotentQuotientMeasure K) ≤
            ∫⁻ g in (· * x₀) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, F g
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨R, hR⟩ := exists_forall_norm_apply_le_of_mem_infiniteBox K
  refine ⟨2 * R, fun c u₁ u' d₁ d₂ κ hu F hF hper x₀ => ?_⟩
  set W₁ := (· * x₀) '' centreCutSiegelSetAmple K c u₁ d₁ d₂ κ with hW₁
  set W' := (· * x₀) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ with hW'
  have hW'm : MeasurableSet W' := by
    rw [hW', Set.image_mul_right]
    exact (continuous_mul_const x₀⁻¹).measurable (measurableSet_centreCutSiegelSetAmple c u' d₁ d₂ κ)
  rw [← lintegral_indicator hW'm F,
    lintegral_adelicGLHaar_eq_mul_lintegral_unipotentQuotientMeasure K _ (hF.indicator hW'm)]

  have hfibre : ∀ h : AdelicGL2 (𝓞 K) K,
      (unipotentShadow K W₁).indicator (boxMass K F) h ≤
        ∫⁻ x, W'.indicator F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K) := by
    intro h
    by_cases hsh : h ∈ unipotentShadow K W₁
    swap
    · rw [Set.indicator_of_notMem hsh]
      exact zero_le
    rw [Set.indicator_of_mem hsh]
    obtain ⟨x₁, hx₁⟩ := hsh
    rw [hW₁] at hx₁
    have hx₁' := (mem_image_mul_right_iff K x₁).mp hx₁
    obtain ⟨ξ₁, hξ₁, -⟩ := existsUnique_algebraMap_add_mem_adelicBox K x₁

    have hpiece : ∀ b ∈ adelicBox K,
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) (-ξ₁) + b) * h ∈ W' := by
      intro b hb
      rw [hW']
      refine (mem_image_mul_right_iff K _).mpr (unipotentGL2_mul_mem_ample_of_close K hx₁' hu
        (fun w => ?_) ?_)
      · have hEq : AdelicLevel.archEval K w
              (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (-ξ₁) + b)) -
            AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K x₁) =
              b.1 w - (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).1 w := by
          show algebraMap K (InfiniteAdeleRing K) (-ξ₁) w + b.1 w - x₁.1 w =
            b.1 w - (algebraMap K (InfiniteAdeleRing K) ξ₁ w + x₁.1 w)
          rw [map_neg]
          show -(algebraMap K (InfiniteAdeleRing K) ξ₁ w) + b.1 w - x₁.1 w =
            b.1 w - (algebraMap K (InfiniteAdeleRing K) ξ₁ w + x₁.1 w)
          ring
        rw [hEq]
        calc ‖b.1 w - (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).1 w‖
            ≤ ‖b.1 w‖ + ‖(algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).1 w‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (hR _ hb.1 w) (hR _ hξ₁.1 w)
          _ = 2 * R := by ring
      · have hEq : AdelicLevel.adeleFin (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (-ξ₁) + b) -
            AdelicLevel.adeleFin (𝓞 K) K x₁ =
              b.2 - (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).2 := by
          show algebraMap K (FiniteAdeleRing (𝓞 K) K) (-ξ₁) + b.2 - x₁.2 =
            b.2 - (algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ₁ + x₁.2)
          rw [map_neg]
          ring
        rw [hEq]
        have hb2 : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := hb.2
        have hβ2 : (algebraMap K (AdeleRing (𝓞 K) K) ξ₁ + x₁).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
          hξ₁.2
        exact AdelicLevel.sub_mem_integralFiniteAdeles hb2 hβ2

    calc boxMass K F h
        = ∫⁻ x in (fun x => algebraMap K (AdeleRing (𝓞 K) K) (-ξ₁) + x) '' adelicBox K,
            F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K) :=
          (setLIntegral_image_add_adelicBox_eq_boxMass K hper (-ξ₁) h).symm
      _ = ∫⁻ x, ((fun x => algebraMap K (AdeleRing (𝓞 K) K) (-ξ₁) + x) '' adelicBox K).indicator
            (fun x => F (unipotentGL2 x * h)) x ∂(adelicAddHaar (𝓞 K) K) :=
          (lintegral_indicator (measurableSet_image_add_adelicBox K _) _).symm
      _ ≤ ∫⁻ x, W'.indicator F (unipotentGL2 x * h) ∂(adelicAddHaar (𝓞 K) K) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ (fun x => algebraMap K (AdeleRing (𝓞 K) K) (-ξ₁) + x) '' adelicBox K
          · obtain ⟨b, hb, rfl⟩ := hx
            rw [Set.indicator_of_mem
              (Set.mem_image_of_mem (fun x => algebraMap K (AdeleRing (𝓞 K) K) (-ξ₁) + x) hb),
              Set.indicator_of_mem (hpiece b hb)]
          · rw [Set.indicator_of_notMem hx]
            exact zero_le
  exact mul_le_mul le_rfl (lintegral_mono fun q => hfibre q.out) zero_le zero_le

end Unfolding

section SiegelTranslateMass

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem unipotentGL2_mul_mem_unipotentShadow_iff (W : Set (AdelicGL2 (𝓞 K) K))
    (x : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K) :
    unipotentGL2 x * h ∈ unipotentShadow K W ↔ h ∈ unipotentShadow K W := by
  simp only [unipotentShadow, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y + x, by rwa [unipotentGL2_add, mul_assoc]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y - x, ?_⟩
    rwa [← mul_assoc, ← unipotentGL2_add, sub_add_cancel]

private theorem massSeq_one_eq (Ψ : HeckeEigensystem K ℂ) (𝔫 : Ideal (𝓞 K)) :
    massSeq K Ψ 1 𝔫 = (‖recValue K Ψ 𝔫‖₊ : ℝ≥0∞) ^ 2 * ((Ideal.absNorm 𝔫 : ℕ) : ℝ≥0∞) := by
  rw [massSeq, Real.rpow_one, ENNReal.ofReal_natCast]

private theorem nnnorm_sq_eq_ofReal_ideleNorm_rpow (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (σ : ℝ)
    (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖χ z‖ = NumberField.TateGlobal.ideleNorm K z ^ σ) :
    (fun z : (AdeleRing (𝓞 K) K)ˣ => (‖χ z‖₊ : ℝ≥0∞) ^ 2)
      = fun z : (AdeleRing (𝓞 K) K)ˣ =>
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ)) := by
  funext z
  rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hχ z, ← Real.rpow_natCast,
    ← Real.rpow_mul (NumberField.TateGlobal.ideleNorm_pos z).le, mul_comm σ]
  norm_num

private theorem measurable_ofReal_ideleNorm_rpow (e : ℝ) :
    Measurable fun z : (AdeleRing (𝓞 K) K)ˣ =>
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ e) :=
  ENNReal.measurable_ofReal.comp
    ((NumberField.TateGlobal.continuous_ideleNorm K).rpow_const
      fun z => Or.inl (NumberField.TateGlobal.ideleNorm_pos z).ne').measurable

private theorem measurable_coe_nnnorm_sq {X : Type} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (φ : X → ℂ) (hφ : Continuous φ) :
    Measurable fun x : X => (‖φ x‖₊ : ℝ≥0∞) ^ 2 :=
  (measurable_coe_nnreal_ennreal.comp hφ.measurable.nnnorm).pow_const 2

private theorem tsum_mul_setLIntegral_mul_eq {ι : Type} [Countable ι] (s : Set (AdeleRing (𝓞 K) K)ˣ)
    (a : ι → ℝ≥0∞) (f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hf : Measurable f)
    (ω : ι → (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hω : ∀ i, Measurable (ω i)) :
    ∑' i, a i * ∫⁻ t in s, f t * ω i t ∂(NumberField.Idele.idelicHaar K)
      = ∫⁻ t in s, f t * ∑' i, a i * ω i t ∂(NumberField.Idele.idelicHaar K) := by
  simp_rw [← lintegral_const_mul _ (hf.fun_mul (hω _))]
  rw [← lintegral_tsum fun i => ((hf.fun_mul (hω i)).const_mul (a i)).aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun i => by ring

private theorem apply_unipotentGL2_algebraMap_add_mul (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (β : K) (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + x) * g) = φ (unipotentGL2 x * g) := by
  rw [unipotentGL2_add, ← iwasawa_globalPoints_unipotentGL2, mul_assoc, hleft]

private theorem laws_of_mem_isotypicCuspSubmodule (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ)
    (hφ0 : φ ≠ 0) :
    (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        φ (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) ∧
      (∀ h : AdelicGL2 (𝓞 K) K,
        whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 0 h = 0) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        φ (g * u) = φ g) := by
  have hI := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ξ N S Ψ
    φ hφ hφ0
  obtain ⟨⟨hA, hcusp⟩, -⟩ := hI.smoothCusp
  obtain ⟨hL, -⟩ := hA
  refine ⟨hL.left_invariant, fun z g => hL.central_transform ⟨z, Subgroup.mem_top z⟩ g,
    fun h => ?_, hI.level_invariant⟩
  rw [AutomorphicForm.whittakerCoefficient_zero_eq_constantTerm]
  exact hcusp h

private theorem recursion_of_mem_isotypicCuspSubmodule (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (D : Set (AdelicGL2 (𝓞 K) K))
    (hD : IsFundamentalDomain (globalPoints (𝓞 K) K).range D
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (Ψ : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ) :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
    ∀ y : AdelicGL2 (𝓞 K) K,
      Valued.v ((((Matrix.GeneralLinearGroup.det y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
          (Valued.v (((y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
      ∀ m : ℕ,
        ‖whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) φ 1 ((heckeGen (𝓞 K) K v) ^ m * y * k)‖ ^ 2 =
          ‖UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
              (Ψ.toRawCentral.a v) (Ψ.toRawCentral.b v) m‖ ^ 2 *
            ‖whittakerCoefficient K
                (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) φ 1 (y * k)‖ ^ 2 := by
  obtain ⟨T, c, hc, u, hcov⟩ := exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  exact whittakerCoefficient_recursion_of_mem K c u 1 2 T α β D ξ N S Ψ hc one_pos one_lt_two
    (hcov 1 2 two_pos one_le_two) hβ hαβ hD hN hS hSψ φ hφ

private theorem shadowWeight_image_eq_windowWeight (W : Set (AdelicGL2 (𝓞 K) K))
    (x₀ : AdelicGL2 (𝓞 K) K) (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (σ : ℝ)
    (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖χ z‖ = NumberField.TateGlobal.ideleNorm K z ^ σ)
    (t : (AdeleRing (𝓞 K) K)ˣ) (k : AdelicGL2 (𝓞 K) K) :
    shadowWeight K (unipotentShadow K ((· * x₀) '' W)) (fun z => (‖χ z‖₊ : ℝ≥0∞) ^ 2) t k
      = windowWeight K W
          (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) t (k * x₀⁻¹) := by
  rw [← windowWeight_eq_shadowWeight, windowWeight_image_mul_right,
    nnnorm_sq_eq_ofReal_ideleNorm_rpow K χ σ hχ]

private theorem exists_finset_supset_and_dvd_mem (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S') ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S' := by
  classical
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨S ∪ (Ideal.finite_factors hN).toFinset ∪ (Ideal.finite_factors hd).toFinset,
    fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), fun v hv => ?_, fun v hv => ?_⟩
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ ((Ideal.finite_factors hN).mem_toFinset.2 hv))
  · exact Finset.mem_union_right _ ((Ideal.finite_factors hd).mem_toFinset.2 hv)

private theorem tsum_mul_setLIntegral_mul_le_of_forall {ι : Type} [Countable ι]
    (s : Set (AdeleRing (𝓞 K) K)ˣ) (a : ι → ℝ≥0∞) (e : ι → (AdeleRing (𝓞 K) K)ˣ)
    (f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (hf : Measurable f) (ω₁ ω₂ : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    (hω₁ : ∀ i, Measurable fun t => ω₁ (e i * t)) (hω₂ : ∀ i, Measurable fun t => ω₂ (e i * t))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hpt : ∀ t : (AdeleRing (𝓞 K) K)ˣ, ∑' i, a i * ω₁ (e i * t) ≤ C * ∑' i, a i * ω₂ (e i * t)) :
    ∑' i, a i * ∫⁻ t in s, f t * ω₁ (e i * t) ∂(NumberField.Idele.idelicHaar K)
      ≤ C * ∑' i, a i * ∫⁻ t in s, f t * ω₂ (e i * t) ∂(NumberField.Idele.idelicHaar K) := by
  rw [tsum_mul_setLIntegral_mul_eq K s a f hf (fun i t => ω₁ (e i * t)) hω₁,
    tsum_mul_setLIntegral_mul_eq K s a f hf (fun i t => ω₂ (e i * t)) hω₂, ← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun t => ?_
  calc f t * ∑' i, a i * ω₁ (e i * t) ≤ f t * (C * ∑' i, a i * ω₂ (e i * t)) :=
        mul_le_mul_right (hpt t) _
    _ = C * (f t * ∑' i, a i * ω₂ (e i * t)) := mul_left_comm _ _ _

end SiegelTranslateMass

private theorem exists_forall_setLIntegral_image_mul_right_le_of_mem_isotypicCuspSubmodule (c u d₁ d₂ : ℝ)
    (hc : 0 < c) (hd₁ : 0 < d₁) (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∃ u' : ℝ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (x₀ : AdelicGL2 (𝓞 K) K), ∀ g ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ,
        ∫⁻ x in (· * x₀) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ C * ∫⁻ x in (· * x₀) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by

  obtain ⟨S', hSS', hS'N, hS'ψ⟩ := exists_finset_supset_and_dvd_mem K N hN S
  obtain ⟨Nup, hNup⟩ := exists_forall_setLIntegral_image_centreCutSiegelSet_le_mul_lintegral_boxMass K u
  obtain ⟨δ, hδ⟩ := exists_forall_lintegral_boxMass_le_setLIntegral_image_centreCutSiegelSetAmple K
  obtain ⟨cI, -, -, hcI⟩ := cov_exists_lintegral_unipotentQuotientMeasure_eq_mul_lintegral_iwasawa K
  by_cases hV : ∃ g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ, g ≠ 0
  swap
  ·
    refine ⟨1, le_rfl, u, 1, ENNReal.one_ne_top, fun x₀ g hg => ?_⟩
    have hg0 : g = 0 := by
      by_contra h
      exact hV ⟨g, hg, h⟩
    subst hg0
    simp
  obtain ⟨g₀, hg₀, hg₀0⟩ := hV
  obtain ⟨σ, hξ⟩ :=
    exists_forall_norm_apply_eq_ideleNorm_rpow_of_mem_isotypicCuspSubmodule K Φ₀ ξ N S Ψ g₀ hg₀ hg₀0
  have hV' : ∃ g ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S' Ψ, g ≠ 0 :=
    ⟨g₀, isotypicCuspSubmodule_mono K _ ξ N hSS' Ψ hg₀, hg₀0⟩
  obtain ⟨κ, hκ, C₃, hC₃, h3⟩ := exists_forall_tsum_massSeq_mul_windowWeight_le K c u d₁ d₂ hc hd₁ α β hβ hαβ
    Φ₀ hΦ₀ ξ σ hξ N hN S' hS'N hS'ψ Ψ hV'
  simp only [massSeq_one_eq] at h3
  refine ⟨κ, hκ, |u| + δ, Nup * C₃, ENNReal.mul_ne_top (ENNReal.natCast_ne_top Nup) hC₃, fun x₀ g hg => ?_⟩
  by_cases hg0 : g = 0
  · subst hg0
    simp

  have hg' := isotypicCuspSubmodule_mono K _ ξ N hSS' Ψ hg
  obtain ⟨hleft, hcentral, hcusp, hright⟩ := laws_of_mem_isotypicCuspSubmodule K Φ₀ ξ N S Ψ g hg hg0
  have hcont : Continuous g :=
    (AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K Φ₀
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ξ N S Ψ
      g hg hg0).continuous
  have hrec := recursion_of_mem_isotypicCuspSubmodule K α β hβ hαβ Φ₀ hΦ₀ ξ N hN S' hS'N hS'ψ Ψ g hg'
  have hper : ∀ (β : K) (x : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
      g (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + x) * h) = g (unipotentGL2 x * h) :=
    apply_unipotentGL2_algebraMap_add_mul K g hleft
  have hvan : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
      ∀ (k : adelicMaximalCompact K) (t : (AdeleRing (𝓞 K) K)ˣ),
        1 < Valued.v ((t : AdeleRing (𝓞 K) K).2 v) →
        whittakerCoefficient K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) g 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) = 0 :=
    fun v hv k t ht =>
      whittakerCoefficient_diagOne_mul_eq_zero_of_one_lt_valuation K Φ₀ N S' hS'N hS'ψ g hper hright v hv k
        t ht

  set F : AdelicGL2 (𝓞 K) K → ℝ≥0∞ := fun x => (‖g x‖₊ : ℝ≥0∞) ^ 2 with hF_def
  have hFm : Measurable F := measurable_coe_nnnorm_sq g hcont
  have hFper : UnipotentPeriodic K F := fun β x h => by
    simp only [hF_def, hper]

  have hbox : boxMass K F = fun h => adelicAddHaar (𝓞 K) K (adelicBox K) *
      ∑' a : Kˣ, (‖whittakerCoefficient K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) g 1 (globalPoints (𝓞 K) K (diagOne a) * h)‖₊ : ℝ≥0∞) ^ 2 :=
    funext fun h =>
      setLIntegral_adelicBox_nnnorm_sq_eq_mul_tsum_nnnorm_whittakerCoefficient_sq K Φ₀ g hcont hleft hcusp h
  have hμB : adelicAddHaar (𝓞 K) K (adelicBox K) ≠ ⊤ := (adelicAddHaar_adelicBox_lt_top K).ne

  have hquot : ∀ (W : Set (AdelicGL2 (𝓞 K) K)),
      MeasurableSet (unipotentShadow K ((· * x₀) '' W)) →
      ∫⁻ q, (unipotentShadow K ((· * x₀) '' W)).indicator (boxMass K F) q.out ∂(unipotentQuotientMeasure K)
        = adelicAddHaar (𝓞 K) K (adelicBox K) * (cI * ∫⁻ k, ∫⁻ t, (‖whittakerCoefficient K
            (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) g 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) *
            windowWeight K W (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) t
              ((k : AdelicGL2 (𝓞 K) K) * x₀⁻¹)
          ∂(NumberField.Idele.idelicHaar K) ∂(maximalCompactHaar K)) := by
    intro W hWm
    rw [hbox]
    simp only [Set.indicator_const_mul]
    rw [lintegral_const_mul' _ _ hμB,
      lintegral_unipotentQuotient_indicator_tsum_eq_mul_lintegral_shadowWeight K Φ₀ cI hcI _ hWm
        (fun x h => unipotentGL2_mul_mem_unipotentShadow_iff K _ x h) g hcont hleft
        (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hcentral]
    simp only [shadowWeight_image_eq_windowWeight K W x₀ _ σ hξ]

  have hinner : ∀ k : adelicMaximalCompact K,
      ∫⁻ t, (‖whittakerCoefficient K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) g 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) *
          windowWeight K (centreCutSiegelSet K c u d₁ d₂)
            (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) t
            ((k : AdelicGL2 (𝓞 K) K) * x₀⁻¹) ∂(NumberField.Idele.idelicHaar K)
        ≤ C₃ * ∫⁻ t, (‖whittakerCoefficient K
            (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) g 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) *
            windowWeight K (centreCutSiegelSetAmple K c u d₁ d₂ κ)
              (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) t
              ((k : AdelicGL2 (𝓞 K) K) * x₀⁻¹) ∂(NumberField.Idele.idelicHaar K) := by
    intro k
    haveI : Countable (GoodIdeal K S') := idelePartition_countable_goodIdeal K S'
    rw [lintegral_nnnorm_whittakerCoefficient_diagOne_sq_mul_eq_tsum_goodIdeal K Φ₀ S' Ψ g hrec hvan k,
      lintegral_nnnorm_whittakerCoefficient_diagOne_sq_mul_eq_tsum_goodIdeal K Φ₀ S' Ψ g hrec hvan k]
    exact tsum_mul_setLIntegral_mul_le_of_forall K (unitsOff K S') _ (fun 𝔫 : GoodIdeal K S' => idealIdele K 𝔫.1)
      _ (measurable_nnnorm_whittakerCoefficient_diagOne_sq_mul K Φ₀ g hcont k)
      (fun x => windowWeight K (centreCutSiegelSet K c u d₁ d₂)
        (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) x ((k : AdelicGL2 (𝓞 K) K) * x₀⁻¹))
      (fun x => windowWeight K (centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun z => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K z ^ (2 * σ))) x ((k : AdelicGL2 (𝓞 K) K) * x₀⁻¹))
      (fun 𝔫 => measurable_windowWeight_mul_left K _ (measurableSet_unipotentShadow_centreCutSiegelSet c u d₁ d₂)
        _ (measurable_ofReal_ideleNorm_rpow K (2 * σ)) _ _)
      (fun 𝔫 => measurable_windowWeight_mul_left K _
        (measurableSet_unipotentShadow_centreCutSiegelSetAmple c u d₁ d₂ κ) _
        (measurable_ofReal_ideleNorm_rpow K (2 * σ)) _ _)
      C₃ hC₃ (fun t => h3 u t ((k : AdelicGL2 (𝓞 K) K) * x₀⁻¹))

  have hJ := lintegral_mono (μ := maximalCompactHaar K) fun k => hinner k
  rw [lintegral_const_mul' _ _ hC₃] at hJ
  calc ∫⁻ x in (· * x₀) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫⁻ x in (· * x₀) '' centreCutSiegelSet K c u d₁ d₂, F x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := rfl
    _ ≤ Nup * ((adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ *
          ∫⁻ q, (unipotentShadow K ((· * x₀) '' centreCutSiegelSet K c u d₁ d₂)).indicator (boxMass K F) q.out
            ∂(unipotentQuotientMeasure K)) := hNup c d₁ d₂ F hFm hFper x₀
    _ ≤ (Nup * C₃) * ((adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ *
          ∫⁻ q, (unipotentShadow K ((· * x₀) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)).indicator (boxMass K F)
            q.out ∂(unipotentQuotientMeasure K)) := by
        rw [hquot _ (measurableSet_unipotentShadow_image_centreCutSiegelSet K c u d₁ d₂ x₀),
          hquot _ (measurableSet_unipotentShadow_image_centreCutSiegelSetAmple K c u d₁ d₂ κ x₀)]
        calc (Nup : ℝ≥0∞) * ((adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ * (adelicAddHaar (𝓞 K) K (adelicBox K) *
                (cI * _)))
            ≤ Nup * ((adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ * (adelicAddHaar (𝓞 K) K (adelicBox K) *
                (cI * (C₃ * _)))) :=
              mul_le_mul_right (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hJ _) _) _) _
          _ = (Nup * C₃) * ((adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ * (adelicAddHaar (𝓞 K) K (adelicBox K) *
                (cI * _))) := by ring
    _ ≤ (Nup * C₃) * ∫⁻ x in (· * x₀) '' centreCutSiegelSetAmple K c (|u| + δ) d₁ d₂ κ, F x
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        mul_le_mul_right (hδ c u (|u| + δ) d₁ d₂ κ le_rfl F hFm hFper x₀) _
    _ = (Nup * C₃) * ∫⁻ x in (· * x₀) '' centreCutSiegelSetAmple K c (|u| + δ) d₁ d₂ κ, (‖g x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := rfl

private theorem
    AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∃ u' : ℝ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ g ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ,
        ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ C * ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨κ, hκ, u', C, hC, h⟩ :=
    exists_forall_setLIntegral_image_mul_right_le_of_mem_isotypicCuspSubmodule K c u d₁ d₂ hc hd₁ α β hβ hαβ Φ₀ hΦ₀
      ξ N hN S Ψ
  refine ⟨κ, hκ, u', C * T.card, ENNReal.mul_ne_top hC (ENNReal.natCast_ne_top _), fun g hg => ?_⟩
  have hU : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) =
      ⋃ x : T, (· * (x : AdelicGL2 (𝓞 K) K)) '' centreCutSiegelSet K c u d₁ d₂ := by
    ext y; simp
  calc ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ∑' x : T, ∫⁻ y in (· * (x : AdelicGL2 (𝓞 K) K)) '' centreCutSiegelSet K c u d₁ d₂, (‖g y‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [hU]; exact lintegral_iUnion_le _ _
    _ = ∑ x ∈ T, ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g y‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        Finset.tsum_subtype T fun x =>
          ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
    _ ≤ ∑ x ∈ T, C * ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, (‖g y‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        Finset.sum_le_sum fun x hx => (h x g hg).trans (mul_le_mul_right (lintegral_mono_set
          (Set.subset_iUnion₂ (s := fun x (_ : x ∈ T) => (· * x) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ) x hx))
          C)
    _ = C * T.card * ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, (‖g y‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end WindowMultiplicity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule.WindowMultiplicity"

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∃ u' : ℝ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ g ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ,
        ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ C * ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  WindowMultiplicity.AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
    K c u d₁ d₂ T hc hd₁ α β hβ hαβ Φ₀ hΦ₀ ξ N hN S Ψ

end
end S_AutomorphicForm_exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule (solution)
