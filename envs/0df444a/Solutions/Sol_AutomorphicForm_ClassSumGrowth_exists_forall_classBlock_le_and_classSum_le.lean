-- Prove2me | solution 1 for AutomorphicForm.ClassSumGrowth.exists_forall_classBlock_le_and_classSum_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/26f6d0f9-cc4a-59b4-90e3-e18310a16a86

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
import Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_RepTheory_SmoothVectors
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_HaarQuotient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_ClassSumGrowth_exists_forall_classBlock_le_and_classSum_le
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv"
p2m_attr_erase "simp" "LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

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

private def idealIdele (𝔫 : Ideal (𝓞 K)) : (AdeleRing (𝓞 K) K)ˣ :=
  open scoped Classical in
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    uniformizerIdele K v ^ (Associates.mk v.asIdeal).count (Associates.mk 𝔫).factors

private def unitsOff (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 K) K)ˣ :=
  {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Valued.v ((t : AdeleRing (𝓞 K) K).2 v) = 1}

section

open scoped ComplexConjugate
open MeasureTheory Finset
open NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ProbabilityTheory
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
variable (F : Type) [Field F] [NumberField F]
local notation "𝔸" => AdeleRing (𝓞 F) F

private theorem isProbabilityMeasure_cond_adelicBox :
    IsProbabilityMeasure ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (adelicAddHaar_adelicBox_pos F).ne'
    (adelicAddHaar_adelicBox_lt_top F).ne

end

section

open scoped ComplexConjugate
open MeasureTheory Finset
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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_secondCountableTopology_adelicGL2 : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_isHaarMeasure_adelicGLHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_isHaarMeasure_unipotentHaar : (unipotentHaar K).IsHaarMeasure :=
  (isHaarMeasure_and_isMulRightInvariant_unipotentHaar K).1

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_isMulRightInvariant_unipotentHaar : (unipotentHaar K).IsMulRightInvariant :=
  (isHaarMeasure_and_isMulRightInvariant_unipotentHaar K).2

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_isHaarMeasure_rationalTorusUnipotentHaar : (rationalTorusUnipotentHaar K).IsHaarMeasure :=
  (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).1

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem cov_isMulRightInvariant_rationalTorusUnipotentHaar :
    (rationalTorusUnipotentHaar K).IsMulRightInvariant :=
  (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).2

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar

private theorem cov_regular_adelicAddHaar : (adelicAddHaar (𝓞 K) K).Regular := by
  unfold adelicAddHaar Measure.addHaar
  infer_instance

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar

private theorem cov_sFinite_unipotentHaar : SFinite (unipotentHaar K) := by
  unfold unipotentHaar
  infer_instance

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar

private theorem cov_secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ :=
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : AdeleRing (𝓞 K) K ≃ₜ (AdeleRing (𝓞 K) K)ᵐᵒᵖ).symm.isInducing.secondCountableTopology
  Units.isInducing_embedProduct.secondCountableTopology

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele

private theorem cov_sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  unfold NumberField.Idele.idelicHaar Measure.haar
  infer_instance

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele
attribute [local instance] cov_sigmaFinite_idelicHaar

private theorem cov_countable_units : Countable Kˣ :=
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  Units.val_injective.countable

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele
attribute [local instance] cov_sigmaFinite_idelicHaar
attribute [local instance] cov_countable_units

private theorem cov_val_globalPoints (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((globalPoints (𝓞 K) K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      (g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (AdeleRing (𝓞 K) K)) :=
  rfl

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele
attribute [local instance] cov_sigmaFinite_idelicHaar
attribute [local instance] cov_countable_units

private theorem cov_val_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(a : A), 1] :=
  rfl

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele
attribute [local instance] cov_sigmaFinite_idelicHaar
attribute [local instance] cov_countable_units

private theorem cov_det_diagOne (t : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne t : AdelicGL2 (𝓞 K) K) = t := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.det, cov_val_diagOne, Matrix.det_diagonal, Fin.prod_univ_two]

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele
attribute [local instance] cov_sigmaFinite_idelicHaar
attribute [local instance] cov_countable_units

private theorem cov_continuous_unipotentGL2 :
    Continuous fun x : AdeleRing (𝓞 K) K => (unipotentGL2 x : AdelicGL2 (𝓞 K) K) := by
  exact AutomorphicForm.continuous_unipotentGL2

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_isHaarMeasure_adelicGLHaar cov_isHaarMeasure_unipotentHaar cov_isMulRightInvariant_unipotentHaar
  cov_isHaarMeasure_rationalTorusUnipotentHaar cov_isMulRightInvariant_rationalTorusUnipotentHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
attribute [local instance] cov_regular_adelicAddHaar cov_sFinite_unipotentHaar cov_secondCountableTopology_idele
attribute [local instance] cov_sigmaFinite_idelicHaar
attribute [local instance] cov_countable_units

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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open IsDedekindDomain
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel NumberField.Idele.ideleBorel
  NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] cov_secondCountableTopology_adelicGL2 cov_secondCountableTopology_adeleRing
  cov_secondCountableTopology_idele cov_sigmaFinite_idelicHaar cov_countable_units
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem iwasawa_globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  apply Units.ext
  rw [cov_val_globalPoints, unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem neg_mem_idealBall {N : Ideal (𝓞 K)} {x : FiniteAdeleRing (𝓞 K) K}
    (hx : x ∈ idealBall (𝓞 K) K N) : -x ∈ idealBall (𝓞 K) K N := fun w => by
  rw [show (-x) w = -(x w) from rfl, Valuation.map_neg]
  exact hx w

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem neg_mem_integralFiniteAdeles' {x : FiniteAdeleRing (𝓞 K) K}
    (hx : x ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    -x ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := fun w => by
  rw [show (-x) w = -(x w) from rfl]
  exact neg_mem (hx w)

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem finAdeleSingleAt_mem_idealBall {N : Ideal (𝓞 K)} (hN : N ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ N) {y : v.adicCompletion K}
    (hy : Valued.v y ≤ 1) : finAdeleSingleAt K v y ∈ idealBall (𝓞 K) K N := fun w => by
  by_cases hw : w = v
  · subst hw
    rw [finAdeleSingleAt_apply_self, idealBound_eq_one_of_not_dvd hN hv]
    exact hy
  · rw [finAdeleSingleAt_apply_of_ne K v y hw]
    simp

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

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

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

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

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

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

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem glFin_unipotentGL2 (a : AdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 a) = unipotentGL2 a.2 := by
  ext i j
  rw [glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem glArch_unipotentGL2 (a : AdeleRing (𝓞 K) K) :
    glArch (𝓞 K) K (unipotentGL2 a) = unipotentGL2 a.1 := by
  ext i j
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

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

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem diagOne_mul_unipotentGL2 (t : (AdeleRing (𝓞 K) K)ˣ) (a : AdeleRing (𝓞 K) K) :
    diagOne t * unipotentGL2 a = unipotentGL2 ((t : AdeleRing (𝓞 K) K) * a) * diagOne t := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem finAdele_mul_apply (a b : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 K)) :
    (a * b) w = a w * b w := rfl

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

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

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem exp_one_le_of_one_lt {g : WithZero (Multiplicative ℤ)} (hg : 1 < g) :
    WithZero.exp (1 : ℤ) ≤ g := by
  have hg0 : g ≠ 0 := (zero_le'.trans_lt hg).ne'
  rw [← WithZero.exp_log hg0] at hg ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hg
  rw [WithZero.exp_le_exp]
  omega

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem count_differentIdeal_eq_zero_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K)) :
    FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
  classical
  by_cases hd : differentIdeal ℤ (𝓞 K) = 0
  · rw [hd, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot, FractionalIdeal.count_zero]
  · rw [FractionalIdeal.count_coe K v hd]
    exact_mod_cast not_not.mp ((Associates.count_ne_zero_iff_dvd hd v.irreducible).not.mpr hv)

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

private theorem addCharLevel_psiLocal_eq_zero_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K)) :
    LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0 := by
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K v]
  exact count_differentIdeal_eq_zero_of_not_dvd hv

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal AutomorphicForm
variable {K}

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

end

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

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_ord_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.Idele.ord K v t = 0 ↔ Valued.v ((t : AdeleRing (𝓞 K) K).2 v) = 1 :=
  (NumberField.Idele.ord_eq_zero_iff K v t).trans
    (IsDedekindDomain.FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one v _)

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_mem_unitsOff_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (t : (AdeleRing (𝓞 K) K)ˣ) :
    t ∈ unitsOff K S ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → NumberField.Idele.ord K v t = 0 :=
  forall_congr' fun v => imp_congr_right fun _ => (idelePartition_ord_eq_zero_iff K v t).symm

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_unitsOff_eq (S : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsOff K S =
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) :
        Set (AdeleRing (𝓞 K) K)ˣ) := by
  ext t
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff, idelePartition_mem_unitsOff_iff]
  exact forall_congr' fun v => imp_congr_right fun _ => NumberField.Idele.ord_eq_zero_iff K v t

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_measurableSet_unitsOff (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSet (unitsOff K S) := by
  rw [idelePartition_unitsOff_eq]
  exact (NumberField.Idele.isOpen_unitIdelesOutside K (↑S : Set (HeightOneSpectrum (𝓞 K)))).measurableSet

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private def idelePartition_piece (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S) :
    Set (AdeleRing (𝓞 K) K)ˣ :=
  (fun t : (AdeleRing (𝓞 K) K)ˣ => (idealIdele K 𝔫.1)⁻¹ * t) ⁻¹' unitsOff K S

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_measurableSet_piece (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S) :
    MeasurableSet (idelePartition_piece K S 𝔫) :=
  (idelePartition_measurableSet_unitsOff K S).preimage (continuous_const.mul continuous_id).measurable

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_ord_prod (v : HeightOneSpectrum (𝓞 K)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (f : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.Idele.ord K v (∏ w ∈ s, f w) = ∑ w ∈ s, NumberField.Idele.ord K v (f w) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, NumberField.Idele.ord_one]
  | insert w s hw ih => rw [Finset.prod_insert hw, Finset.sum_insert hw, NumberField.Idele.ord_mul, ih]

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_ord_pow (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) :
    NumberField.Idele.ord K v (a ^ n) = n * NumberField.Idele.ord K v a := by
  induction n with
  | zero => rw [pow_zero, NumberField.Idele.ord_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, NumberField.Idele.ord_mul, ih, Nat.cast_succ, add_mul, one_mul]

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_mem_piece_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S)
    (t : (AdeleRing (𝓞 K) K)ˣ) :
    t ∈ idelePartition_piece K S 𝔫 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      NumberField.Idele.ord K v t = ((Associates.mk v.asIdeal).count (Associates.mk 𝔫.1).factors : ℤ) := by
  rw [idelePartition_piece, Set.mem_preimage, idelePartition_mem_unitsOff_iff]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [NumberField.Idele.ord_mul, NumberField.Idele.ord_inv, idelePartition_ord_idealIdele K v 𝔫.2.1,
    neg_add_eq_zero, eq_comm]

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_pairwise_disjoint_piece (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise (Function.onFun Disjoint (idelePartition_piece K S)) := fun 𝔫 𝔪 hne => by
  show Disjoint (idelePartition_piece K S 𝔫) (idelePartition_piece K S 𝔪)
  rw [Set.disjoint_left]
  intro t h𝔫 h𝔪
  rw [idelePartition_mem_piece_iff] at h𝔫 h𝔪
  exact hne (idelePartition_goodIdeal_ext K S fun v hv => by exact_mod_cast (h𝔫 v hv).symm.trans (h𝔪 v hv))

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_finite_setOf_ord_ne_zero (t : (AdeleRing (𝓞 K) K)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) | NumberField.Idele.ord K v t ≠ 0}.Finite := by
  have hu : IsUnit ((t : AdeleRing (𝓞 K) K).2) := ⟨NumberField.AdeleRing.finitePartUnits (𝓞 K) K t, rfl⟩
  refine (Filter.eventually_cofinite.mp (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp hu).2).subset fun v hv => ?_
  exact fun h1 => hv ((idelePartition_ord_eq_zero_iff K v t).mpr h1)

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_setLIntegral_piece (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔫 : GoodIdeal K S)
    (F : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) :
    ∫⁻ t in idelePartition_piece K S 𝔫, F t ∂(NumberField.Idele.idelicHaar K) =
      ∫⁻ t in unitsOff K S, F (idealIdele K 𝔫.1 * t) ∂(NumberField.Idele.idelicHaar K) := by
  rw [← lintegral_indicator (idelePartition_measurableSet_piece K S 𝔫),
    ← lintegral_indicator (idelePartition_measurableSet_unitsOff K S),
    ← lintegral_mul_left_eq_self (fun t => (idelePartition_piece K S 𝔫).indicator F t) (idealIdele K 𝔫.1)]
  refine lintegral_congr fun t => ?_
  simp only [Set.indicator, idelePartition_piece, Set.mem_preimage, inv_mul_cancel_left]

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

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

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_nnnorm_sq_eq {a b c : ℂ} (h : ‖a‖ ^ 2 = ‖b‖ ^ 2 * ‖c‖ ^ 2) :
    (‖a‖₊ : ℝ≥0∞) ^ 2 = (‖b‖₊ : ℝ≥0∞) ^ 2 * (‖c‖₊ : ℝ≥0∞) ^ 2 := by
  have h' : ‖a‖₊ ^ 2 = ‖b‖₊ ^ 2 * ‖c‖₊ ^ 2 :=
    NNReal.coe_injective (by simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using h)
  rw [← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul, h']

end

section

open scoped Classical
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem idelePartition_ofReal_inv_ideleNorm_idealIdele_mul {𝔫 : Ideal (𝓞 K)} (h0 : 𝔫 ≠ 0)
    (t : (AdeleRing (𝓞 K) K)ˣ) :
    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫 * t))⁻¹) =
      ((Ideal.absNorm 𝔫 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) := by
  rw [idelePartition_ideleNorm_idealIdele_mul K h0, inv_div, div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

end

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

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory

private def IsLevelKernel (N : Ideal (𝓞 K)) (f : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  IsFactorizableTestFn K f ∧
    ∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
      ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧
        k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory

private abbrev pinsOf (D : Set (AdelicGL2 (𝓞 K) K)) :=
  productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory

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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {a b : AdelicGL2 (𝓞 K) K}
    (ha : glFin (𝓞 K) K a = 1) (hb : glArch (𝓞 K) K b = 1) : a * b = b * a := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul, hb, mul_one, one_mul]
  · rw [map_mul, map_mul, ha, mul_one, one_mul]

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem glArch_eq_one_of_mem_level {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : glArch (𝓞 K) K k = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff K k).mp hk.2

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem glArch_eq_one_of_mem_doubleCoset {U : Subgroup (AdelicGL2 (𝓞 K) K)}
    (hU : U ≤ finiteAdelicGL2Subgroup K) {gv : AdelicGL2 (𝓞 K) K} (hgv : gv ∈ finiteAdelicGL2Subgroup K)
    {x : AdelicGL2 (𝓞 K) K} (hx : x ∈ HeckePair.doubleCoset U gv) : glArch (𝓞 K) K x = 1 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact (mem_finiteAdelicGL2Subgroup_iff K _).mp
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu₁) hgv) (hU hu₂))

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

private theorem integrand_mul_level (hf : IsLevelKernel K N f)
    (hg : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u) = g y)
    (h : AdelicGL2 (𝓞 K) K) {u : AdelicGL2 (𝓞 K) K} (hu : u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (x : AdelicGL2 (𝓞 K) K) : g (h * u * x) * f x = g (h * x) * f x := by
  by_cases hx : f x = 0
  · simp [hx]
  obtain ⟨a, ha, h₁, h₂⟩ := apply_mul_mul_mul_eq_of_levelKernel hf hg h u x (glArch_eq_one_of_mem_level hu) hx
  rw [h₁, h₂, hg _ u hu]

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

private theorem integrable_smoothing_integrand (hg : Continuous g) (hf : IsFactorizableTestFn K f)
    (y : AdelicGL2 (𝓞 K) K) : Integrable (fun x => g (y * x) * f x) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  exact ((hg.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport
    (hfs.mul_left)

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

private theorem heckeGen_mem_finite (v : HeightOneSpectrum (𝓞 K)) :
    heckeGen (𝓞 K) K v ∈ finiteAdelicGL2Subgroup K := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := heckeGenAt_fst (R := 𝓞 K) (K := K) (v := v) (uniformizerUnit K v) i j
  exact h

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

private theorem rightConv_mul_level (hf : IsLevelKernel K N f)
    (hg : ∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (y * u) = g y)
    (h : AdelicGL2 (𝓞 K) K) {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    rightConv K g f (h * u) = rightConv K g f h := by
  simp only [rightConv_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integrand_mul_level hf hg h hu x)

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
variable {N : Ideal (𝓞 K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}

private theorem rightConv_mul_left_eq (hgc : Continuous g) (hf : IsFactorizableTestFn K f)
    {z : AdelicGL2 (𝓞 K) K} {l : ℂ} (hz : ∀ y : AdelicGL2 (𝓞 K) K, g (z * y) = l * g y) (h : AdelicGL2 (𝓞 K) K) :
    rightConv K g f (z * h) = l * rightConv K g f h := by
  have _ := hgc; have _ := hf
  simp only [rightConv_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [mul_assoc z h x, hz, mul_assoc]

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private abbrev windowSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem measure_windowSet_lt_top (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (hd₁ : 0 < d₁) : adelicGLHaar (Fin 2) (𝓞 K) K (windowSet c u d₁ d₂ T) < ⊤ := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  refine (measure_biUnion_finset_le (μ := adelicGLHaar (Fin 2) (𝓞 K) K) T _).trans_lt
    (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  rw [Set.image_mul_right, measure_preimage_mul_right]
  exact SiegelVolume.measure_centreCutSiegelSet_lt_top (adelicGLHaar (Fin 2) (𝓞 K) K) hc u hd₁ d₂

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem isCuspidalFn_rightConv_pinsOf (D : Set (AdelicGL2 (𝓞 K) K)) {φ f : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hf : IsFactorizableTestFn K f)
    (hcusp : @IsCuspidalFn _ (pinsOf K D).nS _ _ (pinsOf K D).ν unipotentGL2 φ) :
    @IsCuspidalFn _ (pinsOf K D).nS _ _ (pinsOf K D).ν unipotentGL2 (rightConv K φ f) :=
  AutomorphicForm.isCuspidalFn_rightConv K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) φ hφ hcusp f hf

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem measurableSet_windowSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    MeasurableSet (windowSet c u d₁ d₂ T) :=
  T.measurableSet_biUnion fun x _ => by
    rw [Set.image_mul_right]
    exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const x⁻¹)

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
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
    first | simpa only [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply] using h | (simp only [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]; exact h) | exact h
  · apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K
    intro w
    ext i j
    have h0 := Units.val_inj.mpr (hfin w)
    have h := congrFun (congrFun h0 i) j
    first | simpa only [finComponent_apply, glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply] using h | (simp only [finComponent_apply, glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply]; exact h) | exact h

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory

private theorem globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, Matrix.GeneralLinearGroup.map]

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem ne_zero_of_rightConv_apply_ne_zero {g f : AdelicGL2 (𝓞 K) K → ℂ} {x : AdelicGL2 (𝓞 K) K}
    (hx : rightConv K g f x ≠ 0) : g ≠ 0 := by
  rintro rfl
  apply hx
  rw [show rightConv K (0 : AdelicGL2 (𝓞 K) K → ℂ) f = fun _ => 0 from AutomorphicForm.rightConv_zero_left K f]

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem finComponent_glFin_mem_localIntegralSet {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (v : HeightOneSpectrum (𝓞 K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K k) ∈ localIntegralSet K v := by
  have h : glFin (𝓞 K) K k ∈ finiteLevelZero (𝓞 K) K N :=
    finiteLevelOne_le_finiteLevelZero (𝓞 K) K N (mem_levelOne_iff.mp (Subgroup.mem_inf.mp hk).1)
  refine ⟨fun i j => h.1.integral i j v, fun i j => ?_⟩
  rw [← map_inv]
  exact h.2.integral i j v

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem conj_heckeRecursionSeq (n : ℕ) (a b : ℂ) :
    ∀ m : ℕ, (starRingEnd ℂ) (UnramifiedWhittaker.heckeRecursionSeq (n : ℂ) a b m)
      = UnramifiedWhittaker.heckeRecursionSeq (n : ℂ) ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) m
  | 0 => by simp [UnramifiedWhittaker.heckeRecursionSeq]
  | 1 => by simp [UnramifiedWhittaker.heckeRecursionSeq, map_div₀]
  | m + 2 => by
    simp only [UnramifiedWhittaker.heckeRecursionSeq, map_div₀, map_sub, map_mul, map_natCast,
      conj_heckeRecursionSeq n a b (m + 1), conj_heckeRecursionSeq n a b m]

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private def eigensystemAtLevel (Ψ : HeckeEigensystem K ℂ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) : HeckeEigensystem K ℂ where
  level := N
  level_ne_bot := hN
  a := Ψ.a
  b := Ψ.b

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
variable {K}

private theorem realizationOfIsIsotypicCuspFormAt_toFun {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)}
    (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 K))} {Ψ : HeckeEigensystem K ℂ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsIsotypicCuspFormAt K pins ξ N S Ψ φ) (hne : ∃ x, φ x ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hN hφ hne).toFun = φ := rfl

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
open scoped Topology
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

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology
open AdelicDock
open scoped ProbabilityTheory
open scoped Topology
variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
variable (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
variable (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)

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

end

section UpperGrowthEstimates

section IdeleNormIdentities

open MeasureTheory NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped NNReal

private noncomputable def upper_ideleNormHom : (AdeleRing (𝓞 K) K)ˣ →* ℝ :=
  (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 K) K))

private theorem upper_ideleNormHom_apply (a : (AdeleRing (𝓞 K) K)ˣ) : upper_ideleNormHom K a = ideleNorm K a :=
  rfl

private theorem upper_ideleNorm_map_algebraMap (α : Kˣ) :
    ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α) = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K (diagOne α)) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α := by
    ext
    show ((globalPoints (𝓞 K) K (diagOne α) : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det = algebraMap K (AdeleRing (𝓞 K) K) (α : K)
    rw [Matrix.det_fin_two]
    simp [globalPoints, diagOne_coe_apply]
  rw [← hdet]
  exact ideleNorm_det_globalPoints (diagOne α)

private theorem upper_ideleNorm_mul_of_mem_principalIdeles (γ : (AdeleRing (𝓞 K) K)ˣ)
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K) (t : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (γ * t) = ideleNorm K t := by
  obtain ⟨α, rfl⟩ := hγ
  rw [ideleNorm_mul, upper_ideleNorm_map_algebraMap, one_mul]

private theorem upper_unipotentGL2_mul_centralScalar (x : AdeleRing (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    unipotentGL2 x * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * unipotentGL2 x :=
  Units.ext (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun _ => Commute.all _ _)
    (unipotentGL2 x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).eq.symm

private theorem upper_globalPoints_diagOne (α : Kˣ) :
    globalPoints (𝓞 K) K (diagOne α) =
      diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, diagOne_coe_apply]

end IdeleNormIdentities

section FirstCoefficientOfSmoothing

open NumberField AutomorphicForm

private theorem upper_exists_whittakerCoefficient_one_rightConv_ne_zero
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      rightConv K φ f (globalPoints (𝓞 K) K γ * g) = rightConv K φ f g)
    (hKf : IsKfSmooth K (rightConv K φ f))
    (g₀ : AdelicGL2 (𝓞 K) K)
    (hcusp : whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ (rightConv K φ f) 0 g₀
      = 0)
    (hg₀ : rightConv K φ f g₀ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 K) K,
      whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ (rightConv K φ f) 1 g ≠ 0 := by
  obtain ⟨hΦ, harch⟩ := continuous_rightConv_and_contDiff_of_isFactorizableTestFn K φ hφ f hf
  have hleft' : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      rightConv K φ f (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = rightConv K φ f g := by
    intro β g
    rw [← iwasawa_globalPoints_unipotentGL2 K β]
    exact hleft _ g
  have hsum := (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace K D U gen ψ hψ
    (rightConv K φ f) hleft' hKf harch).2 g₀
  exact exists_whittakerCoefficient_one_ne_zero K D U gen ψ hψ (rightConv K φ f) hleft g₀ hcusp
    (hΦ.comp ((cov_continuous_unipotentGL2 K).mul continuous_const)) hsum hg₀

end FirstCoefficientOfSmoothing

section SmoothingWitness

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm FLT.SmoothVectors

private theorem upper_rightConv_mul_of_mem (φ f : AdelicGL2 (𝓞 K) K → ℂ) (L : Subgroup (AdelicGL2 (𝓞 K) K))
    (hf : ∀ k ∈ L, ∀ x, f (k * x) = f x) (g : AdelicGL2 (𝓞 K) K) (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ L) :
    rightConv K φ f (g * k) = rightConv K φ f g := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  simp only [rightConv]
  calc ∫ x, φ (g * k * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ x, φ (g * (k * x)) * f (k⁻¹ * (k * x)) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1
        funext x
        rw [mul_assoc, inv_mul_cancel_left]
    _ = ∫ x, φ (g * x) * f (k⁻¹ * x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
        integral_mul_left_eq_self (fun x => φ (g * x) * f (k⁻¹ * x)) k
    _ = ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1
        funext x
        rw [hf k⁻¹ (L.inv_mem hk) x]

private theorem upper_rightConv_globalPoints_mul (φ f : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ f (globalPoints (𝓞 K) K γ * g) = rightConv K φ f g := by
  simp only [rightConv]
  congr 1
  funext x
  rw [mul_assoc, hφ]

private theorem upper_rightConv_centralScalar_mul (φ f : AdelicGL2 (𝓞 K) K → ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hφ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), φ (centralScalar (𝓞 K) K z * g) = χ z * φ g)
    (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ f (centralScalar (𝓞 K) K z * g) = χ z * rightConv K φ f g := by
  simp only [rightConv]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [mul_assoc, hφ, mul_assoc]

private theorem upper_isKfSmooth_of_levelOne_invariant (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * k) = φ g) :
    IsKfSmooth K φ := by
  rw [isKfSmooth_iff]
  refine IsSmoothVector.of_isOpen_subgroup ((levelOne (𝓞 K) K N).comap (finiteAdelicGL2Subgroup K).subtype) ?_ ?_
  · exact (isOpen_levelOne (𝓞 K) K hN).preimage continuous_subtype_val
  · rw [isSmoothVector_iff_isOpen_stabilizer]
    convert isOpen_univ
    rw [Set.eq_univ_iff_forall]
    intro h
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def, Subgroup.smul_def]
    refine RightTranslationFn.ext fun x => ?_
    rw [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
    exact hφ x _ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mp h.2, (h.1 : ↥(finiteAdelicGL2Subgroup K)).2⟩)

private theorem upper_exists_level_kernels_rightConv_rightConv (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (g₀ : AdelicGL2 (𝓞 K) K → ℂ) (hcont₀ : Continuous g₀) (hne₀ : ∃ g, g₀ g ≠ 0)
    (hlev₀ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g₀ (g * k) = g₀ g)
    (hleft₀ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      g₀ (globalPoints (𝓞 K) K γ * g) = g₀ g)
    (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hχ₀ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), g₀ (centralScalar (𝓞 K) K z * g) = χ z * g₀ g) :
    ∃ f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ,
      (IsFactorizableTestFn K f₁ ∧
        (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f₁ (k * x) = f₁ x) ∧
        (∀ x, f₁ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
          glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k)) ∧
      (IsFactorizableTestFn K f₂ ∧
        (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f₂ (k * x) = f₂ x) ∧
        (∀ x, f₂ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
          glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k)) ∧
      Continuous (rightConv K g₀ f₁) ∧
      Continuous (rightConv K (rightConv K g₀ f₁) f₂) ∧
      (∃ g, rightConv K (rightConv K g₀ f₁) f₂ g ≠ 0) ∧
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightConv K (rightConv K g₀ f₁) f₂ (globalPoints (𝓞 K) K γ * g) = rightConv K (rightConv K g₀ f₁) f₂ g) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        rightConv K (rightConv K g₀ f₁) f₂ (g * k) = rightConv K (rightConv K g₀ f₁) f₂ g) ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        rightConv K (rightConv K g₀ f₁) f₂ (centralScalar (𝓞 K) K z * g) =
          χ z * rightConv K (rightConv K g₀ f₁) f₂ g) ∧
      IsKfSmooth K (rightConv K (rightConv K g₀ f₁) f₂) := by
  obtain ⟨f₁, hf₁, hl₁, hs₁, hne₁⟩ :=
    exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant K N hN g₀ hcont₀ hne₀ hlev₀
  have hcont₁ : Continuous (rightConv K g₀ f₁) :=
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K g₀ hcont₀ f₁ hf₁).1
  have hlev₁ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      rightConv K g₀ f₁ (g * k) = rightConv K g₀ f₁ g :=
    fun g k hk => upper_rightConv_mul_of_mem K g₀ f₁ _ hl₁ g k hk
  obtain ⟨f₂, hf₂, hl₂, hs₂, hne₂⟩ :=
    exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant K N hN (rightConv K g₀ f₁) hcont₁ hne₁
      hlev₁
  have hlev₂ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      rightConv K (rightConv K g₀ f₁) f₂ (g * k) = rightConv K (rightConv K g₀ f₁) f₂ g :=
    fun g k hk => upper_rightConv_mul_of_mem K (rightConv K g₀ f₁) f₂ _ hl₂ g k hk
  refine ⟨f₁, f₂, ⟨hf₁, hl₁, hs₁⟩, ⟨hf₂, hl₂, hs₂⟩, hcont₁,
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K _ hcont₁ f₂ hf₂).1, hne₂, ?_, hlev₂, ?_,
    upper_isKfSmooth_of_levelOne_invariant K N hN _ hlev₂⟩
  · intro γ g
    exact upper_rightConv_globalPoints_mul K _ f₂ (upper_rightConv_globalPoints_mul K g₀ f₁ hleft₀) γ g
  · intro z g
    exact upper_rightConv_centralScalar_mul K _ f₂ χ (upper_rightConv_centralScalar_mul K g₀ f₁ χ hχ₀) z g

end SmoothingWitness

section CuspidalityOfSmoothing

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open AutomorphicForm.CuspidalSpectrum

private theorem upper_whittakerCoefficient_rightConv_eq_zero (D : Set (AdelicGL2 (𝓞 K) K))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : Continuous ψ) (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) (α : K)
    (hvan : ∀ g, whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g = 0)
    (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ (rightConv K φ f) α g = 0 := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  obtain ⟨C, hC, hsubC⟩ := exists_isCompact_adelicBox_subset K
  set μA : Measure (AdeleRing (𝓞 K) K) := (adelicAddHaar (𝓞 K) K).restrict (adelicBox K) with hμA
  haveI : IsFiniteMeasure μA :=
    isFiniteMeasure_restrict.mpr (adelicAddHaar_adelicBox_lt_top K).ne
  set μG : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K
  set w : AdeleRing (𝓞 K) K → ℂ := fun x => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
  have hwc : Continuous w := hψ.comp (continuous_const.mul continuous_id).neg

  have hvan' : ∀ h : AdelicGL2 (𝓞 K) K, ∫ x, φ (unipotentGL2 x * h) * w x ∂μA = 0 := by
    intro h
    have h0 := hvan h
    change ∫ x, φ (unipotentGL2 x * h) * w x
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K)) = 0 at h0
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_zero] at h0
    refine h0.resolve_left ?_
    have hpos := adelicAddHaar_adelicBox_pos K
    have hlt := adelicAddHaar_adelicBox_lt_top K
    exact ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr hlt.ne, ENNReal.inv_ne_top.mpr hpos.ne'⟩

  have hint : Integrable (Function.uncurry fun x y => φ (unipotentGL2 x * g * y) * f y * w x) (μA.prod μG) := by
    have hcont : Continuous (Function.uncurry fun x y => φ (unipotentGL2 x * g * y) * f y * w x) := by
      have hn : Continuous fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => unipotentGL2 p.1 * g * p.2 :=
        (((continuous_unipotentGL2_adele K).comp continuous_fst).mul continuous_const).mul continuous_snd
      exact ((hφ.comp hn).mul (hfc.comp continuous_snd)).mul (hwc.comp continuous_fst)

    have hnull : (μA.prod μG) (Cᶜ ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 K) K))) = 0 := by
      rw [Measure.prod_prod, hμA, Measure.restrict_apply hC.isClosed.measurableSet.compl,
        (Set.disjoint_compl_left_iff_subset.mpr hsubC).inter_eq, measure_empty, zero_mul]
    refine integrableOn_univ.mp
      ((hcont.continuousOn.integrableOn_compact (hC.prod hfs)).of_ae_diff_eq_zero
        MeasurableSet.univ.nullMeasurableSet ?_)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp hdiff
    have hpC : p.1 ∈ C := by
      by_contra hpc
      exact hp ⟨hpc, Set.mem_univ _⟩
    have hy : p.2 ∉ tsupport f := fun hy => hdiff.2 ⟨hpC, hy⟩
    have hfy : f p.2 = 0 := by
      by_contra hne
      exact hy (subset_tsupport f hne)
    simp [Function.uncurry, hfy]

  change ∫ x, rightConv K φ f (unipotentGL2 x * g) * w x
      ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K)) = 0
  rw [ProbabilityTheory.cond, integral_smul_measure]
  refine smul_eq_zero_of_right _ ?_
  calc ∫ x, rightConv K φ f (unipotentGL2 x * g) * w x ∂μA
      = ∫ x, ∫ y, φ (unipotentGL2 x * g * y) * f y * w x ∂μG ∂μA := by
        congr 1
        funext x
        simp only [rightConv]
        rw [← integral_mul_const]
    _ = ∫ y, ∫ x, φ (unipotentGL2 x * g * y) * f y * w x ∂μA ∂μG := integral_integral_swap hint
    _ = ∫ y, (0 : ℂ) ∂μG := by
        congr 1
        funext y
        have h1 : (fun x => φ (unipotentGL2 x * g * y) * f y * w x) =
            fun x => φ (unipotentGL2 x * (g * y)) * w x * f y := by
          funext x
          rw [mul_assoc (unipotentGL2 x)]
          ring
        rw [h1, integral_mul_const, hvan' (g * y), zero_mul]
    _ = 0 := integral_zero _ _

end CuspidalityOfSmoothing

section ShellUnfolding

open MeasureTheory NumberField NumberField.TateGlobal NumberField.Idele NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem upper_tsum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (f : ι → α → ℝ≥0∞) :
    ∑' i, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑' i, f i x ∂μ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          simp_rw [Finset.sum_insert ha]
          exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
    _ ≤ ∫⁻ x, ∑' i, f i x ∂μ := lintegral_mono fun x => ENNReal.sum_le_tsum s

private theorem upper_coe_nnnorm_sq (z : ℂ) : ((‖z‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm, enorm_eq_nnnorm]

private theorem upper_tsum_nnnorm_whittakerCoefficient_sq_le
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    [IsFiniteMeasure (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (h : AdelicGL2 (𝓞 K) K) (c : ℝ)
    (hbound : ∀ u : AdeleRing (𝓞 K) K, ‖φ (unipotentGL2 u * h)‖ ^ 2 ≤ c) :
    ∑' α : K, ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ α h‖₊ : ℝ≥0∞)) ^ 2
      ≤ ENNReal.ofReal c * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ := by
  set ν := (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν
  have hcont : Continuous fun u : AdeleRing (𝓞 K) K => φ (unipotentGL2 u * h) :=
    hφ.comp ((cov_continuous_unipotentGL2 K).mul continuous_const)
  have hint : ∫ u, ‖φ (unipotentGL2 u * h)‖ ^ 2 ∂ν ≤ (ν Set.univ).toReal * c := by
    calc ∫ u, ‖φ (unipotentGL2 u * h)‖ ^ 2 ∂ν ≤ ∫ _u, c ∂ν :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) (integrable_const c)
            (Filter.Eventually.of_forall hbound)
      _ = (ν Set.univ).toReal * c := by rw [integral_const, smul_eq_mul, measureReal_def]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun A => ?_
  calc ∑ α ∈ A, ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ α h‖₊ : ℝ≥0∞)) ^ 2
      = ENNReal.ofReal (∑ α ∈ A,
          ‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ α h‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun α _ => sq_nonneg _]
        exact Finset.sum_congr rfl fun α _ => upper_coe_nnnorm_sq _
    _ ≤ ENNReal.ofReal (∫ u, ‖φ (unipotentGL2 u * h)‖ ^ 2 ∂ν) :=
        ENNReal.ofReal_le_ofReal
          (sum_norm_whittakerCoefficient_sq_le_integral_norm_sq K D U gen ψ hψ φ h hcont A)
    _ ≤ ENNReal.ofReal ((ν Set.univ).toReal * c) := ENNReal.ofReal_le_ofReal hint
    _ = ENNReal.ofReal c * ν Set.univ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top ν _), mul_comm]

private theorem upper_lintegral_nnnorm_whittakerCoefficient_sq_mul_le
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    [IsFiniteMeasure (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (k₀ : AdelicGL2 (𝓞 K) K)
    (Dₚ : Set (AdeleRing (𝓞 K) K)ˣ) (hDm : MeasurableSet Dₚ)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) Dₚ (idelicHaar K))
    (hnorm : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K, ∀ t : (AdeleRing (𝓞 K) K)ˣ,
      ideleNorm K (γ * t) = ideleNorm K t)
    (a b : ℝ) (w : ℝ → ℝ≥0∞) (G : ℝ → ℝ)
    (hG : ∀ (u : AdeleRing (𝓞 K) K) (t : (AdeleRing (𝓞 K) K)ˣ), ideleNorm K t ∈ Set.Icc a b →
      ‖φ (unipotentGL2 u * (diagOne t * k₀))‖ ^ 2 ≤ G (ideleNorm K t))
    (M : ℝ≥0∞) (hM : ∀ r ∈ Set.Icc a b, ENNReal.ofReal (G r) * w r ≤ M) :
    ∫⁻ t, ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ 1
          (diagOne t * k₀)‖₊ : ℝ≥0∞)) ^ 2 * w (ideleNorm K t) * (Set.Icc a b).indicator 1 (ideleNorm K t)
        ∂idelicHaar K
      ≤ M * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ
          * idelicHaar K (Dₚ ∩ {t | ideleNorm K t ∈ Set.Icc a b}) := by

  have hsurj : Function.Surjective
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  haveI : Countable Kˣ := cov_countable_units K
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 K) K) := hsurj.countable

  have hidx : ∀ g : M4aHerbrand.principalIdeles (𝓞 K) K, ((g⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) :
      (AdeleRing (𝓞 K) K)ˣ) = Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
        (Function.surjInv hsurj g⁻¹) := by
    intro g
    rw [← MonoidHom.coe_rangeRestrict, Function.surjInv_eq hsurj]
    rfl
  have hidx_inj : Function.Injective fun g : M4aHerbrand.principalIdeles (𝓞 K) K =>
      ((Function.surjInv hsurj g⁻¹ : Kˣ) : K) :=
    fun g₁ g₂ hg => inv_injective (Function.injective_surjInv hsurj (Units.ext hg))

  have hterm : ∀ (g : M4aHerbrand.principalIdeles (𝓞 K) K) (x : (AdeleRing (𝓞 K) K)ˣ),
      ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ 1
          (diagOne (g⁻¹ • x) * k₀)‖₊ : ℝ≥0∞)) ^ 2 * w (ideleNorm K (g⁻¹ • x))
          * (Set.Icc a b).indicator 1 (ideleNorm K (g⁻¹ • x))
        = ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ
            ((Function.surjInv hsurj g⁻¹ : Kˣ) : K) (diagOne x * k₀)‖₊ : ℝ≥0∞)) ^ 2
          * (w (ideleNorm K x) * (Set.Icc a b).indicator 1 (ideleNorm K x)) := by
    intro g x
    have hcov := whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul K D U gen ψ hψ φ hleft
      ((Function.surjInv hsurj g⁻¹ : Kˣ) : K) (Function.surjInv hsurj g⁻¹).ne_zero (diagOne x * k₀)
    rw [Units.mk0_val, upper_globalPoints_diagOne, ← hidx, ← mul_assoc, ← map_mul] at hcov
    rw [Subgroup.smul_def, smul_eq_mul, hnorm _ (g⁻¹).2, hcov, mul_assoc]
  calc ∫⁻ t, ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ 1
          (diagOne t * k₀)‖₊ : ℝ≥0∞)) ^ 2 * w (ideleNorm K t) * (Set.Icc a b).indicator 1 (ideleNorm K t)
          ∂idelicHaar K
      = ∑' g : M4aHerbrand.principalIdeles (𝓞 K) K, ∫⁻ x in Dₚ,
          ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ
            ((Function.surjInv hsurj g⁻¹ : Kˣ) : K) (diagOne x * k₀)‖₊ : ℝ≥0∞)) ^ 2
          * (w (ideleNorm K x) * (Set.Icc a b).indicator 1 (ideleNorm K x)) ∂idelicHaar K := by
        rw [hDF.lintegral_eq_tsum']
        simp_rw [hterm]
    _ ≤ ∫⁻ x in Dₚ, ∑' g : M4aHerbrand.principalIdeles (𝓞 K) K,
          ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ
            ((Function.surjInv hsurj g⁻¹ : Kˣ) : K) (diagOne x * k₀)‖₊ : ℝ≥0∞)) ^ 2
          * (w (ideleNorm K x) * (Set.Icc a b).indicator 1 (ideleNorm K x)) ∂idelicHaar K :=
        upper_tsum_lintegral_le _ _
    _ ≤ ∫⁻ x in Dₚ, {t : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K t ∈ Set.Icc a b}.indicator
          (fun _ => M * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ) x ∂idelicHaar K := by
        refine lintegral_mono fun x => ?_
        by_cases hx : ideleNorm K x ∈ Set.Icc a b
        · rw [Set.indicator_of_mem (show x ∈ {t : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K t ∈ Set.Icc a b} from hx),
            Set.indicator_of_mem hx, Pi.one_apply, mul_one, ENNReal.tsum_mul_right]
          calc (∑' g : M4aHerbrand.principalIdeles (𝓞 K) K,
                ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ
                  ((Function.surjInv hsurj g⁻¹ : Kˣ) : K) (diagOne x * k₀)‖₊ : ℝ≥0∞)) ^ 2) * w (ideleNorm K x)
              ≤ (∑' α : K, ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ α
                  (diagOne x * k₀)‖₊ : ℝ≥0∞)) ^ 2) * w (ideleNorm K x) :=
                mul_le_mul_of_nonneg_right (ENNReal.tsum_comp_le_tsum_of_injective hidx_inj _) zero_le
            _ ≤ (ENNReal.ofReal (G (ideleNorm K x))
                  * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ) * w (ideleNorm K x) :=
                mul_le_mul_of_nonneg_right (upper_tsum_nnnorm_whittakerCoefficient_sq_le K D U gen ψ hψ φ hφ
                  (diagOne x * k₀) (G (ideleNorm K x)) fun u => hG u x hx) zero_le
            _ = (ENNReal.ofReal (G (ideleNorm K x)) * w (ideleNorm K x))
                  * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ := mul_right_comm _ _ _
            _ ≤ M * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ :=
                mul_le_mul_of_nonneg_right (hM _ hx) zero_le
        · rw [Set.indicator_of_notMem
            (show x ∉ {t : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K t ∈ Set.Icc a b} from hx)]
          simp [Set.indicator_of_notMem hx]
    _ ≤ M * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ
          * (idelicHaar K).restrict Dₚ {t : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K t ∈ Set.Icc a b} :=
        lintegral_indicator_const_le _ _
    _ = M * (productionPinsOf K D U gen (AdelicBox.adelicBox K)).ν Set.univ
          * idelicHaar K (Dₚ ∩ {t | ideleNorm K t ∈ Set.Icc a b}) := by
        rw [Measure.restrict_apply' hDm, Set.inter_comm]

end ShellUnfolding

section TorusBasePoint

open MeasureTheory NumberField NumberField.TateGlobal NumberField.AdelicHaar NumberField.AdelicLevel NumberField.Idele AutomorphicForm

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel NumberField.Idele.isHaarMeasure_idelicHaar

private theorem upper_globalPoints_scalar_coe (a : Kˣ) :
    ((globalPoints (𝓞 K) K
        (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) : AdelicGL2 (𝓞 K) K) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K)) := by
  ext i j
  show algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K) : Matrix (Fin 2) (Fin 2) K) i j) = _
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

private theorem upper_unipotentGL2_mul_globalPoints_scalar (x : AdeleRing (𝓞 K) K) (a : Kˣ) :
    unipotentGL2 x
        * globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
      = globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
          * unipotentGL2 x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, upper_globalPoints_scalar_coe]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm

private theorem upper_diagOne_mul_centralScalar (u z : (AdeleRing (𝓞 K) K)ˣ) :
    (diagOne u : AdelicGL2 (𝓞 K) K) * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * diagOne u :=
  Units.ext (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun _ => Commute.all _ _)
    (diagOne u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).eq.symm

private theorem upper_whittakerCoefficient_globalPoints_scalar_mul (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (a : Kˣ) (α : K) (h : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α
        (globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) * h)
      = whittakerCoefficient K pins ψ φ α h := by
  simp only [whittakerCoefficient]
  congr 1
  funext x
  rw [← mul_assoc, upper_unipotentGL2_mul_globalPoints_scalar, mul_assoc, hleft]

private theorem upper_whittakerCoefficient_one_centralScalar_mul_of_forall (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hχ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), φ (centralScalar (𝓞 K) K z * g) = χ z * φ g)
    (z : (AdeleRing (𝓞 K) K)ˣ) (h : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ 1 (centralScalar (𝓞 K) K z * h) = χ z * whittakerCoefficient K pins ψ φ 1 h := by
  simp only [whittakerCoefficient]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← mul_assoc, upper_unipotentGL2_mul_centralScalar, mul_assoc, hχ, mul_assoc]

variable (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
  (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
  (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)

private noncomputable def upper_mass (g : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  ∑' α : Kˣ,
    ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ (α : K) g‖₊ : ℝ≥0∞)) ^ 2

private theorem upper_mass_unipotentGL2_mul (hψ : IsGlobalAddChar K ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    upper_mass K D U gen ψ φ (unipotentGL2 x * g) = upper_mass K D U gen ψ φ g := by
  unfold upper_mass
  refine tsum_congr fun α => ?_
  have hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = φ (unipotentGL2 u * g) := by
    intro β u
    rw [unipotentGL2_add, ← iwasawa_globalPoints_unipotentGL2, mul_assoc, hleft]
  have h1 : ‖ψ (algebraMap K (AdeleRing (𝓞 K) K) (α : K) * x)‖₊ = 1 :=
    NNReal.coe_eq_one.1 ((coe_nnnorm _).trans (hψ1 _))
  rw [whittakerCoefficient_unipotentGL2_mul K D U gen ψ hψ.principalInvariant φ g hper (α : K) x, nnnorm_mul, h1,
    one_mul]

private theorem upper_mass_globalPoints_diagOne_mul (hψ : IsGlobalAddChar K ψ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (β : Kˣ) (g : AdelicGL2 (𝓞 K) K) :
    upper_mass K D U gen ψ φ (globalPoints (𝓞 K) K (diagOne β) * g) = upper_mass K D U gen ψ φ g := by
  unfold upper_mass
  have hcov : ∀ α : Kˣ,
      whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ (α : K)
          (globalPoints (𝓞 K) K (diagOne β) * g)
        = whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ ((α * β : Kˣ) : K) g := by
    intro α
    rw [whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul K D U gen ψ hψ φ hleft (α : K)
        α.ne_zero, whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul K D U gen ψ hψ φ hleft
        ((α * β : Kˣ) : K) (α * β).ne_zero, Units.mk0_val, Units.mk0_val, ← mul_assoc, ← map_mul, ← map_mul]
  simp_rw [hcov]
  exact Equiv.tsum_eq (Equiv.mulRight β) fun α : Kˣ =>
    ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ (α : K) g‖₊ : ℝ≥0∞)) ^ 2

private theorem upper_mass_mul_of_mem (hψ : IsGlobalAddChar K ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (x : AdelicGL2 (𝓞 K) K) (hx : x ∈ rationalTorusUnipotent K) (g : AdelicGL2 (𝓞 K) K) :
    upper_mass K D U gen ψ φ (x * g) = upper_mass K D U gen ψ φ g := by
  let S : Subgroup (AdelicGL2 (𝓞 K) K) :=
    { carrier := {y | ∀ h, upper_mass K D U gen ψ φ (y * h) = upper_mass K D U gen ψ φ h}
      one_mem' := fun h => by rw [one_mul]
      mul_mem' := fun {y₁ y₂} h₁ h₂ h => by rw [mul_assoc, h₁, h₂]
      inv_mem' := fun {y} hy h => by simpa using (hy (y⁻¹ * h)).symm }
  have hle : rationalTorusUnipotent K ≤ S := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨a, rfl⟩ h
      unfold upper_mass
      simp_rw [MonoidHom.comp_apply, upper_whittakerCoefficient_globalPoints_scalar_mul K _ ψ φ hleft a]
    · rintro _ ⟨β, rfl⟩ h
      exact upper_mass_globalPoints_diagOne_mul K D U gen ψ φ hψ hleft β h
    · rintro _ ⟨y, rfl⟩ h
      exact upper_mass_unipotentGL2_mul K D U gen ψ φ hψ hψ1 hleft _ h
  exact hle hx g

private theorem upper_continuous_term (hψ : IsGlobalAddChar K ψ) (hφ : Continuous φ) (α : Kˣ) :
    Continuous fun g : AdelicGL2 (𝓞 K) K =>
      ((‖whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ (α : K) g‖₊ : ℝ≥0∞)) ^ 2 := by
  simpa only [ENNReal.coe_pow, Function.comp_def] using
    ENNReal.continuous_coe.comp ((continuous_whittakerCoefficient K D U gen ψ hψ.continuous φ hφ (α : K)).nnnorm.fun_pow 2)

private theorem upper_measurable_mass (hψ : IsGlobalAddChar K ψ) (hφ : Continuous φ) :
    Measurable (upper_mass K D U gen ψ φ) := by
  haveI := cov_countable_units K
  show Measurable fun g : AdelicGL2 (𝓞 K) K => ∑' α : Kˣ, _
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s =>
    Finset.measurable_sum s fun α _ => (upper_continuous_term K D U gen ψ φ hψ hφ α).measurable

private theorem upper_isOpen_setOf_lt_mass (hψ : IsGlobalAddChar K ψ) (hφ : Continuous φ) (ε : ℝ≥0∞) :
    IsOpen {g : AdelicGL2 (𝓞 K) K | ε < upper_mass K D U gen ψ φ g} := by
  have hl : LowerSemicontinuous (upper_mass K D U gen ψ φ) :=
    lowerSemicontinuous_tsum fun α => (upper_continuous_term K D U gen ψ φ hψ hφ α).lowerSemicontinuous
  exact hl.isOpen_preimage ε

private theorem upper_exists_whittakerCoefficient_one_diagOne_mul_ne_zero (hψ : IsGlobalAddChar K ψ)
    (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (hφ : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hχ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), φ (centralScalar (𝓞 K) K z * g) = χ z * φ g)
    (hne : ∃ g, whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ 1 g ≠ 0) :
    ∃ (t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      whittakerCoefficient K (productionPinsOf K D U gen (AdelicBox.adelicBox K)) ψ φ 1
        (diagOne t * (k : AdelicGL2 (𝓞 K) K)) ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := hne

  have hpos : 0 < upper_mass K D U gen ψ φ g₀ := by
    unfold upper_mass
    refine lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.coe_pos.2 (nnnorm_pos.2 ?_)) 2) (ENNReal.le_tsum (1 : Kˣ))
    simpa using hg₀
  obtain ⟨ε, hε0, hεlt⟩ := exists_between hpos
  set V : Set (AdelicGL2 (𝓞 K) K) := {g | ε < upper_mass K D U gen ψ φ g} with hV
  have hVopen : IsOpen V := upper_isOpen_setOf_lt_mass K D U gen ψ φ hψ hφ ε
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hVstable : ∀ (x : rationalTorusUnipotent K) (g : AdelicGL2 (𝓞 K) K),
      (x : AdelicGL2 (𝓞 K) K) * g ∈ V ↔ g ∈ V := by
    intro x g
    simp only [hV, Set.mem_setOf_eq, upper_mass_mul_of_mem K D U gen ψ φ hψ hψ1 hleft (x : AdelicGL2 (𝓞 K) K) x.2 g]
  have hVpos : 0 < adelicGLHaar (Fin 2) (𝓞 K) K V := hVopen.measure_pos _ ⟨g₀, hεlt⟩

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (rationalTorusUnipotentHaar K).IsHaarMeasure :=
    (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).1
  haveI : (rationalTorusUnipotentHaar K).IsMulRightInvariant :=
    (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).2

  have hdesc : ∀ q : RationalTorusUnipotentQuotient K, ∀ x : rationalTorusUnipotent K,
      V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) ((x : AdelicGL2 (𝓞 K) K) * q.out)
        = V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) q.out := by
    intro q x
    by_cases hq : q.out ∈ V
    · simp only [Set.indicator_of_mem hq, Set.indicator_of_mem ((hVstable x _).2 hq), Pi.one_apply]
    · simp only [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq ((hVstable x _).1 h))]
  have hind_meas : Measurable fun q : RationalTorusUnipotentQuotient K =>
      V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) q.out := by
    refine measurable_from_quotient.2 ?_
    have hfun : ((fun q : RationalTorusUnipotentQuotient K => V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) q.out)
        ∘ Quotient.mk'') = V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) := by
      funext g
      obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out
        (s := MulAction.orbitRel (rationalTorusUnipotent K) (AdelicGL2 (𝓞 K) K)) g))
      show V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) _ = V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) g
      rw [← hx, Subgroup.smul_def, smul_eq_mul]
      by_cases hg : g ∈ V
      · simp only [Set.indicator_of_mem hg, Set.indicator_of_mem ((hVstable x g).2 hg), Pi.one_apply]
      · simp only [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hVstable x g).1 h))]
    rw [hfun]
    exact measurable_one.indicator hVmeas

  have hquot : adelicGLHaar (Fin 2) (𝓞 K) K V
      = (∫⁻ q, V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) q.out
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
            (rationalTorusUnipotentHaar K)))
        * rationalTorusUnipotentHaar K Set.univ := by
    rw [← lintegral_indicator_one hVmeas,
      HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
        (isClosed_rationalTorusUnipotent K) (rationalTorusUnipotentHaar K) _ (measurable_one.indicator hVmeas),
      ← lintegral_mul_const _ hind_meas]
    refine lintegral_congr fun q => ?_
    simp_rw [hdesc q]
    exact lintegral_const _
  have hQ : (∫⁻ q, V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) q.out
      ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)))
        ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hquot
    exact hVpos.ne' hquot

  have hmassQ : (∫⁻ q, upper_mass K D U gen ψ φ q.out
      ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)))
        ≠ 0 := by
    have hle : ∫⁻ q, ε * V.indicator (1 : AdelicGL2 (𝓞 K) K → ℝ≥0∞) q.out
        ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
          (rationalTorusUnipotentHaar K))
          ≤ ∫⁻ q, upper_mass K D U gen ψ φ q.out
        ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
          (rationalTorusUnipotentHaar K)) := by
      refine lintegral_mono fun q => ?_
      by_cases hq : q.out ∈ V
      · rw [Set.indicator_of_mem hq, Pi.one_apply, mul_one]
        exact le_of_lt hq
      · rw [Set.indicator_of_notMem hq, mul_zero]
        exact zero_le
    rw [lintegral_const_mul' _ _ (ne_top_of_lt hεlt)] at hle
    exact fun h0 => mul_ne_zero hε0.ne' hQ (le_antisymm (h0 ▸ hle) zero_le)

  obtain ⟨c, -, -, hc⟩ := exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa K
  obtain ⟨Dom, hDom, hDomF, -⟩ :=
    exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K (idelicHaar K)
  have hmain := hc Dom Dom hDom hDom hDomF hDomF (upper_mass K D U gen ψ φ) (upper_measurable_mass K D U gen ψ φ hψ hφ)
    (fun x hx g => upper_mass_mul_of_mem K D U gen ψ φ hψ hψ1 hleft x hx g)
  rw [rationalTorusUnipotentQuotientMeasure] at hmain
  have htriple := right_ne_zero_of_mul (hmain ▸ hmassQ)

  by_contra hcon
  push Not at hcon
  refine htriple ?_
  have hzero : ∀ (z t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      upper_mass K D U gen ψ φ (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) = 0 := by
    intro z t k
    unfold upper_mass
    refine ENNReal.tsum_eq_zero.2 fun α => ?_
    have hpt : (diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α) :
          AdelicGL2 (𝓞 K) K) * (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K))
        = centralScalar (𝓞 K) K z *
            (diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α * t) *
              (k : AdelicGL2 (𝓞 K) K)) := by
      rw [map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc, upper_diagOne_mul_centralScalar, mul_assoc]
    rw [whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul K D U gen ψ hψ φ hleft (α : K)
      α.ne_zero, Units.mk0_val, upper_globalPoints_diagOne, hpt,
      upper_whittakerCoefficient_one_centralScalar_mul_of_forall K _ ψ φ χ hχ,
      hcon, mul_zero, nnnorm_zero, ENNReal.coe_zero, zero_pow two_ne_zero]
  simp only [hzero, zero_mul, lintegral_zero]

end TorusBasePoint

section ShellWeightBound

private theorem upper_rpow_le_max_of_mem_Icc {L U x σ : ℝ} (hL : 0 < L) (hx : x ∈ Set.Icc L U) :
    x ^ σ ≤ max (L ^ σ) (U ^ σ) := by
  obtain ⟨hLx, hxU⟩ := Set.mem_Icc.mp hx
  rcases le_or_gt 0 σ with hσ | hσ
  · exact le_max_of_le_right (Real.rpow_le_rpow (hL.le.trans hLx) hxU hσ)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos hL hLx hσ.le)

private theorem upper_exists_forall_mul_rpow_le (c ρ σ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (ρ / 4) (2 * ρ), (r * c) ^ σ ≤ B := by
  refine ⟨max ((ρ / 4 * c) ^ σ) ((2 * ρ * c) ^ σ), le_max_of_le_left (Real.rpow_nonneg (by positivity) _), ?_⟩
  intro r hr
  obtain ⟨hr1, hr2⟩ := Set.mem_Icc.mp hr
  exact upper_rpow_le_max_of_mem_Icc (by positivity)
    (Set.mem_Icc.mpr ⟨mul_le_mul_of_nonneg_right hr1 hc.le, mul_le_mul_of_nonneg_right hr2 hc.le⟩)

private theorem upper_sq_rpow_half_mul_inv {s Y : ℝ} (hs : 0 < s) (hY : 0 < Y) (σ : ℝ) :
    ((s * Y⁻¹) ^ (σ / 2)) ^ 2 = s ^ σ * Y ^ (-σ) := by
  have hsY : 0 < s * Y⁻¹ := by positivity
  rw [sq, ← Real.rpow_add hsY, add_halves, Real.mul_rpow hs.le (inv_nonneg.mpr hY.le), Real.inv_rpow hY.le,
    ← Real.rpow_neg hY.le]

private theorem upper_exists_forall_sq_mul_le_mul_rpow (M a b κ ρ σ : ℝ) (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ)
    (hρ : 0 < ρ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ Y : ℝ, 0 < Y → ∀ r ∈ Set.Icc (ρ / 4) (2 * ρ),
      (M * max ((r * (Y⁻¹ * κ) / a) ^ (σ / 2)) ((r * (Y⁻¹ * κ) / b) ^ (σ / 2))) ^ 2 * (Y * r⁻¹) ≤
        G * Y ^ (1 - σ) := by
  obtain ⟨Ba, hBa0, hBa⟩ := upper_exists_forall_mul_rpow_le (κ / a) ρ σ (by positivity) hρ
  obtain ⟨Bb, hBb0, hBb⟩ := upper_exists_forall_mul_rpow_le (κ / b) ρ σ (by positivity) hρ
  refine ⟨M ^ 2 * (Ba + Bb) * (ρ / 4)⁻¹, by positivity, ?_⟩
  intro Y hY r hr
  have hr1 : ρ / 4 ≤ r := (Set.mem_Icc.mp hr).1
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hYσ : 0 ≤ Y ^ (-σ) := Real.rpow_nonneg hY.le _
  have hpa : ((r * (Y⁻¹ * κ) / a) ^ (σ / 2)) ^ 2 = (r * (κ / a)) ^ σ * Y ^ (-σ) := by
    rw [show r * (Y⁻¹ * κ) / a = r * (κ / a) * Y⁻¹ by ring]
    exact upper_sq_rpow_half_mul_inv (by positivity) hY σ
  have hpb : ((r * (Y⁻¹ * κ) / b) ^ (σ / 2)) ^ 2 = (r * (κ / b)) ^ σ * Y ^ (-σ) := by
    rw [show r * (Y⁻¹ * κ) / b = r * (κ / b) * Y⁻¹ by ring]
    exact upper_sq_rpow_half_mul_inv (by positivity) hY σ
  have hmax : (max ((r * (Y⁻¹ * κ) / a) ^ (σ / 2)) ((r * (Y⁻¹ * κ) / b) ^ (σ / 2))) ^ 2 ≤
      (Ba + Bb) * Y ^ (-σ) := by
    rcases max_choice ((r * (Y⁻¹ * κ) / a) ^ (σ / 2)) ((r * (Y⁻¹ * κ) / b) ^ (σ / 2)) with h | h
    · rw [h, hpa]
      exact mul_le_mul_of_nonneg_right (by linarith [hBa r hr]) hYσ
    · rw [h, hpb]
      exact mul_le_mul_of_nonneg_right (by linarith [hBb r hr]) hYσ
  set m : ℝ := max ((r * (Y⁻¹ * κ) / a) ^ (σ / 2)) ((r * (Y⁻¹ * κ) / b) ^ (σ / 2))
  have hrinv : r⁻¹ ≤ (ρ / 4)⁻¹ := inv_anti₀ (by positivity) hr1
  have hY1 : Y ^ (1 - σ) = Y ^ (-σ) * Y := by
    rw [show (1 : ℝ) - σ = -σ + 1 by ring, Real.rpow_add hY, Real.rpow_one]
  have key : m ^ 2 * r⁻¹ ≤ (Ba + Bb) * Y ^ (-σ) * (ρ / 4)⁻¹ :=
    mul_le_mul hmax hrinv (inv_nonneg.mpr hr0.le) (by positivity)
  calc (M * m) ^ 2 * (Y * r⁻¹) = M ^ 2 * Y * (m ^ 2 * r⁻¹) := by ring
    _ ≤ M ^ 2 * Y * ((Ba + Bb) * Y ^ (-σ) * (ρ / 4)⁻¹) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = M ^ 2 * (Ba + Bb) * (ρ / 4)⁻¹ * Y ^ (1 - σ) := by rw [hY1]; ring

end ShellWeightBound

section WindowBandBound

private theorem upper_rpow_eq_div_rpow_half {n D D' σ : ℝ} (hn : 0 < n) (hD : 0 < D) (h : D' = n ^ 2 * D) :
    n ^ σ = (D' / D) ^ (σ / 2) := by
  have h1 : D' / D = n ^ (2 : ℝ) := by
    rw [h, Real.rpow_two]
    field_simp
  have h2 : (2 : ℝ) * (σ / 2) = σ := by ring
  rw [h1, ← Real.rpow_mul hn.le, h2]

private theorem upper_le_mul_max_rpow {G Z Γ : Type} (f d : G → ℝ) (hf0 : ∀ q, 0 ≤ f q) (hd : ∀ q, 0 < d q)
    (n : Z → ℝ) (hn : ∀ z, 0 < n z) (actZ : Z → G → G) (actΓ : Γ → G → G) (σ : ℝ)
    (hfΓ : ∀ γ q, f (actΓ γ q) = f q) (hdΓ : ∀ γ q, d (actΓ γ q) = d q)
    (hfZ : ∀ z q, f (actZ z q) = n z ^ σ * f q) (hdZ : ∀ z q, d (actZ z q) = n z ^ 2 * d q)
    (W : Set G) (hcov : ∀ q, ∃ z γ, actZ z (actΓ γ q) ∈ W) (M : ℝ) (hW : ∀ w ∈ W, f w ≤ M)
    (a b : ℝ) (ha : 0 < a) (hdet : ∀ w ∈ W, a ≤ d w ∧ d w ≤ b) (q : G) :
    f q ≤ M * max ((d q / a) ^ (σ / 2)) ((d q / b) ^ (σ / 2)) := by
  obtain ⟨z, γ, hw⟩ := hcov q
  set w := actZ z (actΓ γ q) with hw_def
  have hfw : f w = n z ^ σ * f q := by rw [hw_def, hfZ, hfΓ]
  have hdw : d w = n z ^ 2 * d q := by rw [hw_def, hdZ, hdΓ]
  have hM : 0 ≤ M := (hf0 w).trans (hW w hw)
  have hnσ : 0 < n z ^ σ := Real.rpow_pos_of_pos (hn z) σ
  obtain ⟨hwa, hwb⟩ := hdet w hw
  have hdwpos : 0 < d w := hd w
  have hdq : 0 < d q := hd q
  have hb : 0 < b := lt_of_lt_of_le hdwpos hwb

  have hratio : n z ^ σ = (d w / d q) ^ (σ / 2) := upper_rpow_eq_div_rpow_half (hn z) (hd q) hdw
  have hinv : (d q / d w) ^ (σ / 2) = (n z ^ σ)⁻¹ := by
    rw [hratio, ← Real.inv_rpow (div_pos hdwpos (hd q)).le, inv_div]
  have hq : f q = f w * (d q / d w) ^ (σ / 2) := by
    rw [hinv, hfw]
    field_simp

  have hband : (d q / d w) ^ (σ / 2) ≤ max ((d q / a) ^ (σ / 2)) ((d q / b) ^ (σ / 2)) := by
    rcases le_or_gt 0 σ with hσ | hσ
    · refine le_max_of_le_left (Real.rpow_le_rpow (div_pos (hd q) hdwpos).le ?_ (by linarith))
      gcongr
    · refine le_max_of_le_right (Real.rpow_le_rpow_of_nonpos (div_pos (hd q) hb) ?_ (by linarith))
      gcongr
  calc f q = f w * (d q / d w) ^ (σ / 2) := hq
    _ ≤ M * (d q / d w) ^ (σ / 2) :=
        mul_le_mul_of_nonneg_right (hW w hw) (Real.rpow_nonneg (div_pos hdq hdwpos).le _)
    _ ≤ M * max ((d q / a) ^ (σ / 2)) ((d q / b) ^ (σ / 2)) := by gcongr

end WindowBandBound

section DyadicSummation

open scoped ENNReal

private theorem upper_exists_lt_and_le_div_two_pow {ι : Type} (n : ι → ℝ) {i : ι} (hi : 0 < n i) {Y : ℝ}
    (hY : n i ≤ Y) : ∃ j : ℕ, Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j := by
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near ((one_le_div hi).mpr hY) (one_lt_two (α := ℝ))
  refine ⟨j, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    calc Y < 2 ^ (j + 1) * n i := (div_lt_iff₀ hi).mp hj'
      _ = n i * 2 ^ (j + 1) := mul_comm _ _
  · rw [le_div_iff₀ (by positivity)]
    calc n i * 2 ^ j = 2 ^ j * n i := mul_comm _ _
      _ ≤ Y := (le_div_iff₀ hi).mp hj

private theorem upper_tsum_le_tsum_tsum_dyadic {ι : Type} (n : ι → ℝ) (hn : ∀ i, 0 < n i) (f : ι → ℝ≥0∞)
    (Y : ℝ) :
    ∑' i : {i // n i ≤ Y}, f i ≤
      ∑' j : ℕ, ∑' i : {i // Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j}, f i := by
  have hL : ∑' i : {i // n i ≤ Y}, f i = ∑' i : ι, {i | n i ≤ Y}.indicator f i :=
    tsum_subtype {i | n i ≤ Y} f
  have hR : ∀ j : ℕ, ∑' i : {i // Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j}, f i =
      ∑' i : ι, {i | Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j}.indicator f i :=
    fun j => tsum_subtype {i | Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j} f
  rw [hL]
  simp_rw [hR]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun i => ?_
  by_cases hi : n i ≤ Y
  · obtain ⟨j, hj₁, hj₂⟩ := upper_exists_lt_and_le_div_two_pow n (hn i) hi
    have hmem : i ∈ {i | Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j} := ⟨hj₁, hj₂⟩
    have hmemY : i ∈ {i | n i ≤ Y} := hi
    calc {i | n i ≤ Y}.indicator f i = f i := Set.indicator_of_mem hmemY f
      _ = {i | Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j}.indicator f i :=
          (Set.indicator_of_mem hmem f).symm
      _ ≤ ∑' j : ℕ, {i | Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j}.indicator f i :=
          ENNReal.le_tsum j
  · simp [Set.indicator_apply, hi]

end DyadicSummation

section DyadicPartialSums

open scoped ENNReal

private theorem upper_tsum_le_of_forall_block_le {ι : Type} (P : ι → Prop) (n : ι → ℝ) (hn : ∀ i, 0 < n i)
    (g : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hblock : ∀ Y : ℝ, 0 < Y → ∑' i : {i : ι // P i ∧ Y < n i ∧ n i ≤ 2 * Y}, g i.1 ≤ C * ENNReal.ofReal Y)
    (Y : ℝ) (hY : 0 < Y) :
    ∑' i : {i : ι // P i ∧ n i ≤ Y}, g i.1 ≤ 2 * C * ENNReal.ofReal Y := by
  have h1 : ∑' i : {i : ι // P i ∧ n i ≤ Y}, g i.1 = ∑' i : {i : {i : ι // P i} // n i.1 ≤ Y}, g i.1.1 :=
    (Equiv.tsum_eq (Equiv.subtypeSubtypeEquivSubtypeInter P (fun i => n i ≤ Y)) (fun i => g i.1)).symm
  have h2 : ∑' i : {i : {i : ι // P i} // n i.1 ≤ Y}, g i.1.1 ≤
      ∑' j : ℕ, ∑' i : {i : {i : ι // P i} // Y / 2 ^ (j + 1) < n i.1 ∧ n i.1 ≤ Y / 2 ^ j}, g i.1.1 :=
    upper_tsum_le_tsum_tsum_dyadic (fun i : {i : ι // P i} => n i.1) (fun i => hn i.1) (fun i => g i.1) Y
  have h2inv : ENNReal.ofReal (2⁻¹ : ℝ) = 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have h3 : ∀ j : ℕ,
      ∑' i : {i : {i : ι // P i} // Y / 2 ^ (j + 1) < n i.1 ∧ n i.1 ≤ Y / 2 ^ j}, g i.1.1 ≤
        C * (ENNReal.ofReal Y * 2⁻¹ ^ j) := by
    intro j
    have hYj : 0 < Y / 2 ^ (j + 1) := by positivity
    have htwo : 2 * (Y / 2 ^ (j + 1)) = Y / 2 ^ j := by
      rw [pow_succ, ← div_div]
      ring
    have hre : ∑' i : {i : {i : ι // P i} // Y / 2 ^ (j + 1) < n i.1 ∧ n i.1 ≤ Y / 2 ^ j}, g i.1.1 =
        ∑' i : {i : ι // P i ∧ Y / 2 ^ (j + 1) < n i ∧ n i ≤ 2 * (Y / 2 ^ (j + 1))}, g i.1 := by
      rw [htwo]
      exact Equiv.tsum_eq
        (Equiv.subtypeSubtypeEquivSubtypeInter P (fun i => Y / 2 ^ (j + 1) < n i ∧ n i ≤ Y / 2 ^ j))
        (fun i => g i.1)
    have hreal : Y / 2 ^ (j + 1) ≤ Y * 2⁻¹ ^ j := by
      have hx : 0 ≤ Y * 2⁻¹ ^ j := by positivity
      calc Y / 2 ^ (j + 1) = Y * 2⁻¹ ^ j / 2 := by rw [pow_succ, inv_pow]; ring
        _ ≤ Y * 2⁻¹ ^ j := half_le_self hx
    have hj : ENNReal.ofReal (Y / 2 ^ (j + 1)) ≤ ENNReal.ofReal Y * 2⁻¹ ^ j := by
      calc ENNReal.ofReal (Y / 2 ^ (j + 1)) ≤ ENNReal.ofReal (Y * 2⁻¹ ^ j) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal Y * 2⁻¹ ^ j := by
          rw [ENNReal.ofReal_mul hY.le, ENNReal.ofReal_pow (by positivity), h2inv]
    rw [hre]
    exact (hblock _ hYj).trans (mul_le_mul_of_nonneg_left hj zero_le)
  have h4 : ∑' j : ℕ, ∑' i : {i : {i : ι // P i} // Y / 2 ^ (j + 1) < n i.1 ∧ n i.1 ≤ Y / 2 ^ j}, g i.1.1 ≤
      ∑' j : ℕ, C * (ENNReal.ofReal Y * 2⁻¹ ^ j) :=
    ENNReal.tsum_le_tsum h3
  have h5 : ∑' j : ℕ, C * (ENNReal.ofReal Y * 2⁻¹ ^ j) = 2 * C * ENNReal.ofReal Y := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    ring
  rw [h1]
  exact h2.trans (h4.trans_eq h5)

end DyadicPartialSums

section WindowDeterminantBounds

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel

private theorem upper_ideleNorm_det_mem_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁)
    {y : AdelicGL2 (𝓞 K) K} (hy : y ∈ centreCutSiegelSet K c u d₁ d₂) :
    (∏ w : InfinitePlace K, d₁ ^ w.mult) ≤ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ∧
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ≤ ∏ w : InfinitePlace K, d₂ ^ w.mult := by
  obtain ⟨hfin, -, -, hdet⟩ := mem_centreCutSiegelSet_iff.mp hy
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K y hfin]
  constructor
  · refine Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _) (fun w _ => ?_)
    have h1 : d₁ ≤ archDetNorm w y := (Set.mem_Icc.mp (hdet w)).1
    gcongr
  · refine Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w y).le _) (fun w _ => ?_)
    have h0 : 0 ≤ archDetNorm w y := (archDetNorm_pos w y).le
    have h2 : archDetNorm w y ≤ d₂ := (Set.mem_Icc.mp (hdet w)).2
    gcongr

private theorem upper_prod_min_one_le {α : Type} [DecidableEq α] (T : Finset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) {x : α}
    (hx : x ∈ T) : (∏ x' ∈ T, min 1 (f x')) ≤ f x := by
  rw [← Finset.mul_prod_erase T _ hx]
  have h1 : (∏ x' ∈ T.erase x, min 1 (f x')) ≤ 1 :=
    Finset.prod_le_one (fun x' _ => (lt_min one_pos (hf x')).le) (fun x' _ => min_le_left _ _)
  calc min 1 (f x) * ∏ x' ∈ T.erase x, min 1 (f x') ≤ min 1 (f x) :=
        mul_le_of_le_one_right (lt_min one_pos (hf x)).le h1
    _ ≤ f x := min_le_right _ _

private theorem upper_le_prod_max_one {α : Type} [DecidableEq α] (T : Finset α) (f : α → ℝ) {x : α} (hx : x ∈ T) :
    f x ≤ ∏ x' ∈ T, max 1 (f x') := by
  rw [← Finset.mul_prod_erase T _ hx]
  have h1 : (1 : ℝ) ≤ ∏ x' ∈ T.erase x, max 1 (f x') :=
    calc (1 : ℝ) = ∏ _x' ∈ T.erase x, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ x' ∈ T.erase x, max 1 (f x') :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun x' _ => le_max_left _ _)
  calc f x ≤ max 1 (f x) := le_max_right _ _
    _ ≤ max 1 (f x) * ∏ x' ∈ T.erase x, max 1 (f x') :=
        le_mul_of_one_le_right (le_max_of_le_left zero_le_one) h1

private theorem upper_exists_ideleNorm_det_mem_of_mem_iUnion_centreCutSiegelSet (c u d₁ d₂ : ℝ) (hd₁ : 0 < d₁)
    (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ w ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
      a ≤ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det w) ∧
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det w) ≤ b := by
  classical
  have hN : ∀ x : AdelicGL2 (𝓞 K) K, 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) :=
    fun x => NumberField.TateGlobal.ideleNorm_pos _
  have hL : 0 < ∏ w : InfinitePlace K, d₁ ^ w.mult := Finset.prod_pos fun w _ => pow_pos hd₁ _
  have hP : 0 < ∏ x ∈ T, min 1 (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) :=
    Finset.prod_pos fun x _ => lt_min one_pos (hN x)
  refine ⟨(∏ w : InfinitePlace K, d₁ ^ w.mult) *
      ∏ x ∈ T, min 1 (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)),
    max ((∏ w : InfinitePlace K, d₁ ^ w.mult) *
        ∏ x ∈ T, min 1 (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)))
      ((∏ w : InfinitePlace K, d₂ ^ w.mult) *
        ∏ x ∈ T, max 1 (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x))),
    mul_pos hL hP, le_max_left _ _, ?_⟩
  intro w hw
  obtain ⟨x, hxT, hw⟩ := Set.mem_iUnion₂.mp hw
  obtain ⟨y, hy, hyw⟩ := hw
  have hyw' : y * x = w := hyw
  subst hyw'
  have hmul : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (y * x)) =
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  obtain ⟨hy₁, hy₂⟩ := upper_ideleNorm_det_mem_of_mem_centreCutSiegelSet K hd₁ hy
  have hx₁ := upper_prod_min_one_le T _ hN hxT
  have hx₂ := upper_le_prod_max_one T
    (fun x : AdelicGL2 (𝓞 K) K => NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) hxT
  rw [hmul]
  exact ⟨mul_le_mul hy₁ hx₁ hP.le (hN y).le,
    le_max_of_le_right (mul_le_mul hy₂ hx₂ (hN x).le ((hN y).le.trans hy₂))⟩

end WindowDeterminantBounds

section UnitIdeleNormalisation

private theorem upper_ord_prod {ι : Type} (s : Finset ι) (a : ι → (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.Idele.ord K v (∏ i ∈ s, a i) = ∑ i ∈ s, NumberField.Idele.ord K v (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [NumberField.Idele.ord_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, NumberField.Idele.ord_mul, ih]

open scoped Classical in

private theorem upper_count_factors_prod_pow (T : Finset (HeightOneSpectrum (𝓞 K))) (e : HeightOneSpectrum (𝓞 K) → ℕ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((Associates.mk v.asIdeal).count (Associates.mk (∏ w ∈ T, w.asIdeal ^ e w)).factors : ℤ) =
      if v ∈ T then (e v : ℤ) else 0 := by
  classical
  have hne : (∏ w ∈ T, w.asIdeal ^ e w) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ w.ne_bot
  have hcoe : ((∏ w ∈ T, w.asIdeal ^ e w : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ w ∈ T, ((w.asIdeal ^ e w : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    map_prod (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) (fun w => w.asIdeal ^ e w) T
  rw [← FractionalIdeal.count_coe K v hne, hcoe]
  rw [FractionalIdeal.count_prod K v T (fun w => ((w.asIdeal ^ e w : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    fun w _ => by
      show ((w.asIdeal ^ e w : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0
      rw [FractionalIdeal.coeIdeal_pow]
      exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)]
  have hterm : ∀ w ∈ T, FractionalIdeal.count K v ((w.asIdeal ^ e w : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      if w = v then (e w : ℤ) else 0 := by
    intro w _
    rw [FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]
    split_ifs with hwv
    · subst hwv; rw [FractionalIdeal.count_self, mul_one]
    · rw [FractionalIdeal.count_maximal_coprime K v hwv, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T v]

open scoped Classical in

private theorem upper_ord_idealIdele_prod_pow (T : Finset (HeightOneSpectrum (𝓞 K))) (e : HeightOneSpectrum (𝓞 K) → ℕ)
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.Idele.ord K v (idealIdele K (∏ w ∈ T, w.asIdeal ^ e w)) = if v ∈ T then (e v : ℤ) else 0 := by
  classical
  have hsupp : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 K) =>
      uniformizerIdele K w ^
        (Associates.mk w.asIdeal).count (Associates.mk (∏ u ∈ T, u.asIdeal ^ e u)).factors) ⊆ T := by
    intro w hw
    by_contra hwT
    apply hw
    have hwT' : w ∉ T := fun h => hwT (Finset.mem_coe.mpr h)
    have h0 := upper_count_factors_prod_pow K T e w
    rw [if_neg hwT', Nat.cast_eq_zero] at h0
    show uniformizerIdele K w ^ (Associates.mk w.asIdeal).count (Associates.mk (∏ u ∈ T, u.asIdeal ^ e u)).factors = 1
    rw [h0, pow_zero]
  unfold idealIdele
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, upper_ord_prod]
  have hterm : ∀ w ∈ T, NumberField.Idele.ord K v
      (uniformizerIdele K w ^ (Associates.mk w.asIdeal).count (Associates.mk (∏ u ∈ T, u.asIdeal ^ e u)).factors) =
        if w = v then (e w : ℤ) else 0 := by
    intro w hw
    rw [idelePartition_ord_pow]
    split_ifs with hwv
    · subst hwv
      rw [NumberField.Idele.ord_uniformizerIdele_self, mul_one]
      have h := upper_count_factors_prod_pow K T e w
      rwa [if_pos hw] at h
    · rw [NumberField.Idele.ord_uniformizerIdele_of_ne K (Ne.symm hwv), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T v]

private theorem upper_exists_mem_unitsOff_whittakerCoefficient_ne_zero (D : Set (AdelicGL2 (𝓞 K) K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hvan : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ (k : adelicMaximalCompact K) (t : (AdeleRing (𝓞 K) K)ˣ),
      1 < Valued.v ((t : AdeleRing (𝓞 K) K).2 v) →
        whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) = 0)
    (hrec : ∀ (k : adelicMaximalCompact K) (t : (AdeleRing (𝓞 K) K)ˣ), t ∈ unitsOff K S → ∀ 𝔫 : GoodIdeal K S,
      ‖whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1
          (diagOne (idealIdele K 𝔫.1 * t) * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2 =
        ‖recValue K Ψ 𝔫.1‖ ^ 2 * ‖whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2)
    (k : adelicMaximalCompact K) (t₀ : (AdeleRing (𝓞 K) K)ˣ)
    (h₀ : whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t₀ * (k : AdelicGL2 (𝓞 K) K)) ≠ 0) :
    ∃ t ∈ unitsOff K S, whittakerCoefficient K
          (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) ≠ 0 := by
  classical

  have hnonneg : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → 0 ≤ NumberField.Idele.ord K v t₀ := by
    intro v hv
    by_contra hlt
    push Not at hlt
    refine h₀ (hvan v hv k t₀ ?_)
    rw [NumberField.Idele.valued_snd_eq_exp_neg_ord, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

  set T : Finset (HeightOneSpectrum (𝓞 K)) :=
    ((idelePartition_finite_setOf_ord_ne_zero K t₀).toFinset).filter (fun v => v ∉ S) with hT
  set e : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (NumberField.Idele.ord K v t₀).toNat with he
  set 𝔫 : Ideal (𝓞 K) := ∏ w ∈ T, w.asIdeal ^ e w with h𝔫
  have hmemT : ∀ v, v ∈ T ↔ NumberField.Idele.ord K v t₀ ≠ 0 ∧ v ∉ S := by
    intro v
    simp [hT, Finset.mem_filter, Set.Finite.mem_toFinset]
  have h𝔫ne : 𝔫 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ w.ne_bot
  have h𝔫S : ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔫 := by
    intro v hv hdvd
    have hcount := upper_count_factors_prod_pow K T e v
    rw [if_neg (fun hvT => ((hmemT v).mp hvT).2 hv), Nat.cast_eq_zero] at hcount
    have hprime : Prime v.asIdeal := v.prime
    exact (Associates.count_ne_zero_iff_dvd h𝔫ne (by simpa using hprime.irreducible)).mpr hdvd hcount

  have hord : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      NumberField.Idele.ord K v (idealIdele K 𝔫) = NumberField.Idele.ord K v t₀ := by
    intro v hv
    rw [h𝔫, upper_ord_idealIdele_prod_pow]
    by_cases hvT : v ∈ T
    · rw [if_pos hvT, he]
      exact Int.toNat_of_nonneg (hnonneg v hv)
    · rw [if_neg hvT]
      by_contra hne
      exact hvT ((hmemT v).mpr ⟨Ne.symm hne, hv⟩)

  refine ⟨(idealIdele K 𝔫)⁻¹ * t₀, ?_, ?_⟩
  · intro v hv
    rw [NumberField.Idele.valued_snd_eq_exp_neg_ord, NumberField.Idele.ord_mul, NumberField.Idele.ord_inv, hord v hv,
      neg_add_cancel, neg_zero, WithZero.exp_zero]
  · intro hzero
    have h := hrec k ((idealIdele K 𝔫)⁻¹ * t₀) ?_ ⟨𝔫, h𝔫ne, h𝔫S⟩
    · rw [mul_inv_cancel_left, hzero, norm_zero] at h
      simp only [zero_pow two_ne_zero, mul_zero] at h
      exact h₀ (by simpa using h)
    · intro v hv
      rw [NumberField.Idele.valued_snd_eq_exp_neg_ord, NumberField.Idele.ord_mul, NumberField.Idele.ord_inv,
        hord v hv, neg_add_cancel, neg_zero, WithZero.exp_zero]

end UnitIdeleNormalisation

section StandardDeterminants

open NumberField AutomorphicForm

private theorem upper_det_centralScalar_eq (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  rw [← sq, show centralScalar (𝓞 K) K z = Matrix.GeneralLinearGroup.scalar (Fin 2) z from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem upper_det_unipotentGL2_eq (x : AdeleRing (𝓞 K) K) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 K) K) = 1 :=
  Units.ext (by simp [Matrix.det_fin_two])

end StandardDeterminants

section ShellMassAndBlockBound

private theorem upper_valued_eq_one_iff_mem_and_inv_mem (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K)
    (hx : x ≠ 0) :
    Valued.v x = 1 ↔ x ∈ v.adicCompletionIntegers K ∧ x⁻¹ ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

private theorem upper_snd_apply_inv_mul_snd_apply (t : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * ((t : AdeleRing (𝓞 K) K).2) v = 1 :=
  congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) (Units.inv_mul t)

private theorem upper_snd_apply_inv (t : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = (((t : AdeleRing (𝓞 K) K).2) v)⁻¹ :=
  eq_inv_of_mul_eq_one_left (upper_snd_apply_inv_mul_snd_apply K t v)

private theorem upper_mem_unitsOff_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (t : (AdeleRing (𝓞 K) K)ˣ) :
    t ∈ unitsOff K S ↔ t ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall_congr' fun v => ?_
  refine imp_congr_right fun _ => ?_
  have hne : ((t : AdeleRing (𝓞 K) K).2) v ≠ 0 := right_ne_zero_of_mul_eq_one (upper_snd_apply_inv_mul_snd_apply K t v)
  show Valued.v (((t : AdeleRing (𝓞 K) K).2) v) = 1 ↔
    ((t : AdeleRing (𝓞 K) K).2) v ∈ v.adicCompletionIntegers K ∧
      ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K
  rw [upper_valued_eq_one_iff_mem_and_inv_mem K v _ hne, upper_snd_apply_inv]

private theorem upper_isOpen_unitsOff (S : Finset (HeightOneSpectrum (𝓞 K))) : IsOpen (unitsOff K S) := by
  have h : unitsOff K S = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) :
      Set (AdeleRing (𝓞 K) K)ˣ) := Set.ext fun t => upper_mem_unitsOff_iff K S t
  rw [h]
  exact NumberField.Idele.isOpen_unitIdelesOutside K _

private theorem upper_lintegral_unitsOff_inter_shell_pos (D : Set (AdelicGL2 (𝓞 K) K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : adelicMaximalCompact K)
    (hc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
      whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (ht₀ : t₀ ∈ unitsOff K S)
    (h0 : whittakerCoefficient K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t₀ * (k : AdelicGL2 (𝓞 K) K)) ≠ 0)
    (R : ℝ) (hR₁ : R < NumberField.TateGlobal.ideleNorm K t₀) (hR₂ : NumberField.TateGlobal.ideleNorm K t₀ < 4 * R) :
    0 < ∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc R (4 * R)},
        (‖whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(NumberField.Idele.idelicHaar K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  set c : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
    whittakerCoefficient K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) φ 1 g with hcdef
  set f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun t =>
    (‖c (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
    with hfdef

  set W : Set (AdeleRing (𝓞 K) K)ˣ := unitsOff K S ∩ NumberField.TateGlobal.ideleNorm K ⁻¹' Set.Ioo R (4 * R) ∩
    {t | c (diagOne t * (k : AdelicGL2 (𝓞 K) K)) ≠ 0} with hWdef
  have hck : Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => c (diagOne t * (k : AdelicGL2 (𝓞 K) K)) :=
    hc.comp ((cov_continuous_diagOne K).mul continuous_const)
  have hWopen : IsOpen W :=
    ((upper_isOpen_unitsOff K S).inter (isOpen_Ioo.preimage (NumberField.TateGlobal.continuous_ideleNorm K))).inter
      (isOpen_ne_fun hck continuous_const)
  have ht₀W : t₀ ∈ W := ⟨⟨ht₀, hR₁, hR₂⟩, h0⟩
  have hWpos : 0 < NumberField.Idele.idelicHaar K W := hWopen.measure_pos _ ⟨t₀, ht₀W⟩
  have hWsub : W ⊆ unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc R (4 * R)} :=
    fun t ht => ⟨ht.1.1, Set.Ioo_subset_Icc_self ht.1.2⟩
  have hWsupp : W ⊆ Function.support f := by
    intro t ht
    refine mul_ne_zero (pow_ne_zero 2 (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 ht.2))) ?_
    exact (ENNReal.ofReal_pos.2 (inv_pos.2 (NumberField.TateGlobal.ideleNorm_pos t))).ne'
  have hf : Measurable f :=
    ((ENNReal.continuous_coe.comp hck.nnnorm).measurable.pow_const 2).mul
      (ENNReal.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm K).measurable.inv)
  refine (lintegral_pos_iff_support hf).2 ?_
  calc 0 < NumberField.Idele.idelicHaar K W := hWpos
    _ = (NumberField.Idele.idelicHaar K).restrict
          (unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc R (4 * R)}) W := by
        rw [Measure.restrict_apply hWopen.measurableSet, Set.inter_eq_left.2 hWsub]
    _ ≤ (NumberField.Idele.idelicHaar K).restrict
          (unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc R (4 * R)}) (Function.support f) :=
        measure_mono hWsupp

private theorem upper_rpow_le_max_mul_rpow_of_block (σ Y n : ℝ) (hY : 0 < Y) (h₁ : Y < n) (h₂ : n ≤ 2 * Y) :
    n ^ σ ≤ max 1 ((2 : ℝ) ^ σ) * Y ^ σ := by
  have hn : 0 < n := hY.trans h₁
  rcases le_or_gt 0 σ with hσ | hσ
  · calc n ^ σ ≤ (2 * Y) ^ σ := Real.rpow_le_rpow hn.le h₂ hσ
      _ = (2 : ℝ) ^ σ * Y ^ σ := Real.mul_rpow (by norm_num) hY.le
      _ ≤ max 1 ((2 : ℝ) ^ σ) * Y ^ σ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hY.le σ)
  · calc n ^ σ ≤ Y ^ σ := Real.rpow_le_rpow_of_nonpos hY h₁.le hσ.le
      _ = 1 * Y ^ σ := (one_mul _).symm
      _ ≤ max 1 ((2 : ℝ) ^ σ) * Y ^ σ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hY.le σ)

private theorem upper_classBlock_le_of_forall_le_of_tsum_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ψ : HeckeEigensystem K ℂ) (σ : ℝ) (𝒞 : ClassGroup (𝓞 K)) (Y : ℝ) (hY : 0 < Y) (m₀ B : ℝ≥0∞) (hm₀ : m₀ ≠ 0)
    (hB : B ≠ ⊤) (I : GoodIdeal K S → ℝ≥0∞)
    (hI : ∀ 𝔫 : GoodIdeal K S, Y < (Ideal.absNorm 𝔫.1 : ℝ) → (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y → m₀ ≤ I 𝔫)
    (hsum : ∑' 𝔫 : GoodIdeal K S, (‖recValue K Ψ 𝔫.1‖₊ : ℝ≥0∞) ^ 2 * ((Ideal.absNorm 𝔫.1 : ℕ) : ℝ≥0∞) * I 𝔫 ≤
      B * ENNReal.ofReal (Y ^ (1 - σ))) :
    classBlock K S Ψ (1 + σ) 𝒞 Y ≤
      ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ)) * B / m₀ * ENNReal.ofReal Y := by

  set T : GoodIdeal K S → ℝ≥0∞ := fun 𝔫 =>
    (‖recValue K Ψ 𝔫.1‖₊ : ℝ≥0∞) ^ 2 * ((Ideal.absNorm 𝔫.1 : ℕ) : ℝ≥0∞) * I 𝔫 with hTdef

  have hterm : ∀ 𝔫 : {𝔫 : GoodIdeal K S //
      GoodIdeal.cls K 𝔫 = 𝒞 ∧ Y < (Ideal.absNorm 𝔫.1 : ℝ) ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y},
      m₀ * massSeq K Ψ (1 + σ) 𝔫.1.1 ≤ ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * T 𝔫.1 := by
    rintro ⟨𝔫, -, h₁, h₂⟩
    have hn : (0 : ℝ) < (Ideal.absNorm 𝔫.1 : ℝ) := hY.trans h₁
    have hpow : ENNReal.ofReal ((Ideal.absNorm 𝔫.1 : ℝ) ^ (1 + σ)) ≤
        ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * ((Ideal.absNorm 𝔫.1 : ℕ) : ℝ≥0∞) := by
      rw [Real.rpow_add hn, Real.rpow_one, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), mul_comm]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (upper_rpow_le_max_mul_rpow_of_block σ Y _ hY h₁ h₂) hn.le)
    calc m₀ * massSeq K Ψ (1 + σ) 𝔫.1 =
          m₀ * ((‖recValue K Ψ 𝔫.1‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((Ideal.absNorm 𝔫.1 : ℝ) ^ (1 + σ))) := rfl
      _ ≤ I 𝔫 * ((‖recValue K Ψ 𝔫.1‖₊ : ℝ≥0∞) ^ 2 *
            (ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * ((Ideal.absNorm 𝔫.1 : ℕ) : ℝ≥0∞))) :=
          mul_le_mul' (hI 𝔫 h₁ h₂) (mul_le_mul' le_rfl hpow)
      _ = ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * T 𝔫 := by simp only [hTdef]; ring

  have hblock : m₀ * classBlock K S Ψ (1 + σ) 𝒞 Y ≤ ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ)) * B * ENNReal.ofReal Y := by
    calc m₀ * classBlock K S Ψ (1 + σ) 𝒞 Y = ∑' 𝔫 : {𝔫 : GoodIdeal K S //
            GoodIdeal.cls K 𝔫 = 𝒞 ∧ Y < (Ideal.absNorm 𝔫.1 : ℝ) ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y},
            m₀ * massSeq K Ψ (1 + σ) 𝔫.1.1 := by
          unfold classBlock
          exact ENNReal.tsum_mul_left.symm
      _ ≤ ∑' 𝔫 : {𝔫 : GoodIdeal K S //
            GoodIdeal.cls K 𝔫 = 𝒞 ∧ Y < (Ideal.absNorm 𝔫.1 : ℝ) ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y},
            ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * T 𝔫.1 := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * ∑' 𝔫 : {𝔫 : GoodIdeal K S //
            GoodIdeal.cls K 𝔫 = 𝒞 ∧ Y < (Ideal.absNorm 𝔫.1 : ℝ) ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y}, T 𝔫.1 :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * ∑' 𝔫 : GoodIdeal K S, T 𝔫 :=
          mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective T)
      _ ≤ ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ) * Y ^ σ) * (B * ENNReal.ofReal (Y ^ (1 - σ))) :=
          mul_le_mul' le_rfl hsum
      _ = ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ)) * B * ENNReal.ofReal Y := by
          rw [ENNReal.ofReal_mul (by positivity), mul_mul_mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hY.le σ),
            ← Real.rpow_add hY, add_sub_cancel, Real.rpow_one]

  rw [← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hm₀)
    (Or.inr (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) ENNReal.ofReal_ne_top))]
  exact (mul_comm _ _).trans_le hblock

end ShellMassAndBlockBound

end UpperGrowthEstimates

section RecursionValueAndMultiplicity

private theorem upper_recValue_eq_finprod_emultiplicity (Ψ : HeckeEigensystem K ℂ) {𝔫 : Ideal (𝓞 K)}
    (h𝔫 : 𝔫 ≠ 0) :
    recValue K Ψ 𝔫 = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
        (Ψ.toRawCentral.b v) (emultiplicity v.asIdeal 𝔫).toNat := by
  classical
  unfold recValue
  refine finprod_congr fun v => ?_
  rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible h𝔫, normalize_eq,
    ENat.toNat_coe, ← Ideal.count_associates_factors_eq h𝔫 v.isPrime v.ne_bot]

end RecursionValueAndMultiplicity

private theorem exists_forall_classBlock_le_and_classSum_le (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
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

  obtain ⟨T, c, hc, u, hcovall⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) :=
    hcovall 1 2 two_pos one_le_two

  obtain ⟨g, hgV, hg0⟩ := hV
  have hgP : IsIsotypicCuspFormAt K (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ g :=
    AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓
        finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) ξ N S Ψ g hgV hg0
  have hcontg : Continuous g := hgP.continuous
  have hlevg : ∀ x : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, g (x * k) = g x :=
    fun x k hk => hgP.level_invariant x k hk
  obtain ⟨⟨hgauto, -⟩, -⟩ := hgP.smoothCusp
  have hgauto' := (lsXiMemberAt_iff _ _ _ _ _ _ _).mp hgauto
  have hleftg : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
      g (globalPoints (𝓞 K) K γ * x) = g x := hgauto'.1.left_invariant
  have hχg : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K),
      g (centralScalar (𝓞 K) K z * x) = (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) z * g x :=
    fun z x => hgauto'.1.central_transform ⟨z, Subgroup.mem_top z⟩ x
  obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hg0
  have hne₀ : ∃ x, g x ≠ 0 := ⟨x0, hx0⟩

  obtain ⟨f₁, f₂, hK₁, hK₂, hcont₁, hcont₀, hne, hleft, hright, hχ, hKf⟩ :=
    upper_exists_level_kernels_rightConv_rightConv K N hN g hcontg hne₀ hlevg hleftg
      (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hχg
  have hχ' : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K),
      (rightConv K (rightConv K g f₁) f₂) (centralScalar (𝓞 K) K z * x) =
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (rightConv K (rightConv K g f₁) f₂) x := hχ
  have hLK₁ : IsLevelKernel K N f₁ := And.intro hK₁.1 hK₁.2.2
  have hLK₂ : IsLevelKernel K N f₂ := And.intro hK₂.1 hK₂.2.2

  have hP : IsIsotypicCuspFormAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
      levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ (rightConv K g f₁) :=
    isIsotypicCuspFormAt_window_rightConv K c u 1 2 T α β Φ₀ ξ N S Ψ hc one_pos one_lt_two hcov hβ hαβ hΦ₀ hN
      g hgP f₁ hLK₁

  have hrec := whittakerCoefficient_recursion_of_rightConv_rightConv K c u 1 2 T α β Φ₀ ξ N S Ψ hc one_pos
    one_lt_two hcov hβ hαβ hΦ₀ hN hS hSψ g hgV f₁ f₂ hLK₁ hLK₂
  have hper : ∀ (b : K) (x : AdeleRing (𝓞 K) K) (y : AdelicGL2 (𝓞 K) K),
      (rightConv K (rightConv K g f₁) f₂) (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) b + x) * y) =
        (rightConv K (rightConv K g f₁) f₂) (unipotentGL2 x * y) := by
    intro b x y
    rw [unipotentGL2_add, ← iwasawa_globalPoints_unipotentGL2 K b, mul_assoc, hleft]
  have hvan := whittakerCoefficient_diagOne_mul_eq_zero_of_one_lt_valuation K
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) N S hS hSψ (rightConv K (rightConv K g f₁) f₂) hper hright
  have hrec₂ := norm_whittakerCoefficient_diagOne_idealIdele_mul_sq K
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) S Ψ (rightConv K (rightConv K g f₁) f₂) hrec

  have hψ : IsGlobalAddChar K (NumberField.StandardAddChar.stdAddChar K) :=
      NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K
  have hψ1 : ∀ x : AdeleRing (𝓞 K) K, ‖(NumberField.StandardAddChar.stdAddChar K) x‖ = 1 := fun x =>
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K hψ x

  obtain ⟨⟨-, hcusp₁⟩, -⟩ := hP.smoothCusp
  have hvan₁ : ∀ y : AdelicGL2 (𝓞 K) K, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) ''
      centreCutSiegelSet K c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K)
      K v) (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) (rightConv K g f₁) 0 y = 0 := fun y => by
    rw [whittakerCoefficient_zero_eq_constantTerm]
    exact hcusp₁ y
  obtain ⟨g₁, hg₁⟩ := hne
  obtain ⟨g₂, hg₂⟩ := upper_exists_whittakerCoefficient_one_rightConv_ne_zero K (⋃ x ∈ T, (· * x) ''
      centreCutSiegelSet K c u 1 2)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K) hψ (rightConv K g f₁) hP.continuous f₂
    hK₂.1 hleft hKf g₁ (upper_whittakerCoefficient_rightConv_eq_zero K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1
        2)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (NumberField.StandardAddChar.stdAddChar K) hψ.continuous
      (rightConv K g f₁) hP.continuous f₂ hK₂.1 0 hvan₁ g₁) hg₁

  obtain ⟨t₁, k, hk₁⟩ := upper_exists_whittakerCoefficient_one_diagOne_mul_ne_zero K (⋃ x ∈ T, (· * x) ''
      centreCutSiegelSet K c u 1 2)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂)
    hψ hψ1 hcont₀ hleft (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hχ ⟨g₂, hg₂⟩
  obtain ⟨t₂, ht₂, hk₂⟩ := upper_exists_mem_unitsOff_whittakerCoefficient_ne_zero K (⋃ x ∈ T, (· * x) ''
      centreCutSiegelSet K c u 1 2)
    S Ψ (rightConv K (rightConv K g f₁) f₂) hvan hrec₂ k t₁ hk₁

  have hWc : Continuous fun y : AdelicGL2 (𝓞 K) K => whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) ''
      centreCutSiegelSet K c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K)
      K v) (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 y :=
    AutomorphicForm.continuous_whittakerCoefficient K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
        levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K) hψ.continuous (rightConv K (rightConv K
          g f₁) f₂) hcont₀ 1
  have hρ : 0 < NumberField.TateGlobal.ideleNorm K t₂ := NumberField.TateGlobal.ideleNorm_pos t₂
  have hm₀ := upper_lintegral_unitsOff_inter_shell_pos K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) S
      (rightConv K (rightConv K g f₁) f₂) k hWc t₂
    ht₂ hk₂ (NumberField.TateGlobal.ideleNorm K t₂ / 2) (by linarith) (by linarith)

  obtain ⟨Cw, hCw⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre K c
        u 1 2
      T hc one_pos one_lt_two hcov ξ f₂ hK₂.1
  have hMw : ∀ w ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2), ‖(rightConv K (rightConv K g f₁) f₂) w‖ ≤ (Cw *
      (eLpNorm (rightConv K g f₁) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2))).toReal) :=
    fun w hw => hCw (rightConv K g f₁) hP.smoothCusp hP.continuous w hw
  obtain ⟨a₀, b₀, ha₀, hab₀, hdet⟩ :=
    upper_exists_ideleNorm_det_mem_of_mem_iUnion_centreCutSiegelSet K c u 1 2 one_pos T
  have hb₀ : 0 < b₀ := ha₀.trans_le hab₀
  have hfΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (q : AdelicGL2 (𝓞 K) K),
      ‖(rightConv K (rightConv K g f₁) f₂) (globalPoints (𝓞 K) K γ * q)‖ = ‖(rightConv K (rightConv K g f₁) f₂) q‖ :=
          fun γ q => by
    rw [hleft]
  have hdΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (q : AdelicGL2 (𝓞 K) K),
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * q)) =
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q) := fun γ q => by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  have hfZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (q : AdelicGL2 (𝓞 K) K),
      ‖(rightConv K (rightConv K g f₁) f₂) (q * centralScalar (𝓞 K) K z)‖ = NumberField.TateGlobal.ideleNorm K z ^ σ *
          ‖(rightConv K (rightConv K g f₁) f₂) q‖ :=
    fun z q => by rw [mul_centralScalar_comm, hχ', norm_mul, hξ]
  have hdZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (q : AdelicGL2 (𝓞 K) K),
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (q * centralScalar (𝓞 K) K z)) =
        NumberField.TateGlobal.ideleNorm K z ^ 2 * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det
            q) := fun z q => by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, upper_det_centralScalar_eq,
        NumberField.TateGlobal.ideleNorm_mul]
    ring
  have hcovU : ∀ q : AdelicGL2 (𝓞 K) K, ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (γ : Matrix.GeneralLinearGroup (Fin 2) K),
      globalPoints (𝓞 K) K γ * q * centralScalar (𝓞 K) K z ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) := fun
          q => by
    obtain ⟨γ, z, h⟩ := hcov q
    exact ⟨z, γ, h⟩
  have hband : ∀ q : AdelicGL2 (𝓞 K) K, ‖(rightConv K (rightConv K g f₁) f₂) q‖ ≤
      (Cw * (eLpNorm (rightConv K g f₁) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2))).toReal) *
        max ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q) / a₀) ^ (σ / 2))
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q) / b₀) ^ (σ / 2)) :=
    upper_le_mul_max_rpow (fun q => ‖(rightConv K (rightConv K g f₁) f₂) q‖)
      (fun q => NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q)) (fun q => norm_nonneg _)
      (fun q => NumberField.TateGlobal.ideleNorm_pos _) (fun z => NumberField.TateGlobal.ideleNorm K z)
      (fun z => NumberField.TateGlobal.ideleNorm_pos z) (fun z q => q * centralScalar (𝓞 K) K z)
      (fun γ q => globalPoints (𝓞 K) K γ * q) σ hfΓ hdΓ hfZ hdZ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2)
          hcovU
      (Cw * (eLpNorm (rightConv K g f₁) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2))).toReal) hMw a₀ b₀ ha₀ hdet

  haveI hHaar : (NumberField.Idele.idelicHaar K).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨D₀, hD₀m, hD₀F, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K
      (NumberField.Idele.idelicHaar K)
  obtain ⟨-, hVlt⟩ := NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top K D₀ hD₀m hD₀F
    (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂) (by linarith) (by linarith)
  have hnorm : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K, ∀ t : (AdeleRing (𝓞 K) K)ˣ, NumberField.TateGlobal.ideleNorm
      K (γ * t) = NumberField.TateGlobal.ideleNorm K t :=
    fun γ hγ t => upper_ideleNorm_mul_of_mem_principalIdeles K γ hγ t
  haveI hprob : IsProbabilityMeasure (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
      levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν := by
    rw [productionPinsOf_ν]
    exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite (adelicAddHaar_adelicBox_pos K).ne'
      (adelicAddHaar_adelicBox_lt_top K).ne
  have hν : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓
      finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν Set.univ ≠ ⊤ :=
    measure_ne_top _ _

  have hκ : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)) :=
    NumberField.TateGlobal.ideleNorm_pos _
  obtain ⟨G₂, hG₂0, hG₂⟩ := upper_exists_forall_sq_mul_le_mul_rpow
    (Cw * (eLpNorm (rightConv K g f₁) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2))).toReal) a₀ b₀
    (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)))
        (NumberField.TateGlobal.ideleNorm K t₂) σ ha₀ hb₀ hκ hρ
  have hBtop : (ENNReal.ofReal G₂ * (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
      levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν Set.univ *
            (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
                (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)})) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν) hVlt.ne
  refine ⟨(ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ)) * (ENNReal.ofReal G₂ * (productionPinsOf K (⋃ x ∈ T, (· * x) ''
      centreCutSiegelSet K c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K)
      K v) (adelicBox K)).ν Set.univ *
            (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
                (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)})) /
          (∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
              (NumberField.TateGlobal.ideleNorm K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
            ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
                levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
                AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(NumberField.Idele.idelicHaar K))), ?_, ?_⟩
  · exact ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop) hm₀.ne'
  intro 𝒞 Y₀ hY₀

  have hblock : ∀ Y : ℝ, 0 < Y → classBlock K S Ψ (1 + σ) 𝒞 Y ≤
      (ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ)) * (ENNReal.ofReal G₂ * (productionPinsOf K (⋃ x ∈ T, (· * x) ''
          centreCutSiegelSet K c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen
          (𝓞 K) K v) (adelicBox K)).ν Set.univ *
            (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
                (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)})) /
          (∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
              (NumberField.TateGlobal.ideleNorm K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
            ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
                levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
                AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(NumberField.Idele.idelicHaar K))) *
                  ENNReal.ofReal Y := by
    intro Y hY

    obtain ⟨s, -, hsY⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K Y⁻¹ (inv_pos.mpr hY)

    have hS3 := lintegral_nnnorm_whittakerCoefficient_diagOne_sq_mul_eq_tsum_goodIdeal K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) S Ψ (rightConv K (rightConv K g f₁) f₂) hrec hvan k
      (fun x => (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K
          t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y * NumberField.TateGlobal.ideleNorm K x))
    beta_reduce at hS3

    have hpt : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
            levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne (s * t) * (k :
            AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K (s * t))⁻¹) *
          (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator
              (1 : ℝ → ℝ≥0∞) (Y * NumberField.TateGlobal.ideleNorm K (s * t)) =
        ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
            levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (diagOne s *
            (k : AdelicGL2 (𝓞 K) K)))‖₊ : ℝ≥0∞)) ^ 2 *
            ENNReal.ofReal (Y * (NumberField.TateGlobal.ideleNorm K t)⁻¹) *
          (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator
              1 (NumberField.TateGlobal.ideleNorm K t) := by
      intro t
      have e1 : diagOne (s * t) * (k : AdelicGL2 (𝓞 K) K) = diagOne t * (diagOne s * (k : AdelicGL2 (𝓞 K) K)) := by
        rw [mul_comm s t, map_mul, mul_assoc]
      have e2 : (NumberField.TateGlobal.ideleNorm K (s * t))⁻¹ = Y * (NumberField.TateGlobal.ideleNorm K t)⁻¹ := by
        rw [NumberField.TateGlobal.ideleNorm_mul, hsY, mul_inv, inv_inv]
      have e3 : Y * NumberField.TateGlobal.ideleNorm K (s * t) = NumberField.TateGlobal.ideleNorm K t := by
        rw [NumberField.TateGlobal.ideleNorm_mul, hsY, ← mul_assoc, mul_inv_cancel₀ hY.ne', one_mul]
      rw [e1, e2, e3]

    have hGY : ∀ (v : AdeleRing (𝓞 K) K) (t : (AdeleRing (𝓞 K) K)ˣ), NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
        (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂) →
        ‖(rightConv K (rightConv K g f₁) f₂) (unipotentGL2 v * (diagOne t * (diagOne s * (k : AdelicGL2 (𝓞 K) K))))‖ ^
            2 ≤
          ((Cw * (eLpNorm (rightConv K g f₁) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2))).toReal) *
            max ((NumberField.TateGlobal.ideleNorm K t * (Y⁻¹ * NumberField.TateGlobal.ideleNorm K
                (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K))) / a₀) ^ (σ / 2))
              ((NumberField.TateGlobal.ideleNorm K t * (Y⁻¹ * NumberField.TateGlobal.ideleNorm K
                  (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K))) / b₀) ^ (σ / 2))) ^ 2 := by
      intro v t _
      have hd : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det
          (unipotentGL2 v * (diagOne t * (diagOne s * (k : AdelicGL2 (𝓞 K) K))))) =
          NumberField.TateGlobal.ideleNorm K t * (Y⁻¹ * NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K))) := by
        rw [map_mul, map_mul, map_mul, upper_det_unipotentGL2_eq, one_mul, cov_det_diagOne, cov_det_diagOne,
          NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, hsY]
      have h := hband (unipotentGL2 v * (diagOne t * (diagOne s * (k : AdelicGL2 (𝓞 K) K))))
      rw [hd] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    have hMY : ∀ r ∈ Set.Icc (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂),
        ENNReal.ofReal (((Cw * (eLpNorm (rightConv K g f₁) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2))).toReal) *
            max ((r * (Y⁻¹ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K)
                K))) / a₀) ^ (σ / 2))
              ((r * (Y⁻¹ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)))
                  / b₀) ^ (σ / 2))) ^ 2) *
          ENNReal.ofReal (Y * r⁻¹) ≤ ENNReal.ofReal (G₂ * Y ^ (1 - σ)) := fun r hr => by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hG₂ Y hY r hr)
    have hG1 := upper_lintegral_nnnorm_whittakerCoefficient_sq_mul_le K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u
        1 2)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (NumberField.StandardAddChar.stdAddChar K) hψ
      (rightConv K (rightConv K g f₁) f₂) hcont₀ hleft (diagOne s * (k : AdelicGL2 (𝓞 K) K)) D₀ hD₀m hD₀F hnorm
      (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂) (fun r => ENNReal.ofReal
          (Y * r⁻¹))
      (fun r => ((Cw * (eLpNorm (rightConv K g f₁) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2))).toReal) *
        max ((r * (Y⁻¹ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K))) /
            a₀) ^ (σ / 2))
          ((r * (Y⁻¹ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K))) /
              b₀) ^ (σ / 2))) ^ 2)
      hGY (ENNReal.ofReal (G₂ * Y ^ (1 - σ))) hMY
    beta_reduce at hG1
    have heq : ENNReal.ofReal (G₂ * Y ^ (1 - σ)) * (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1
        2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
        Set.univ *
          (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
              (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)}) =
        (ENNReal.ofReal G₂ * (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N => levelOne
            (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν Set.univ *
            (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
                (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)})) *
                ENNReal.ofReal (Y ^ (1 - σ)) := by
      rw [ENNReal.ofReal_mul hG₂0]
      ring
    have hsubst : ∫⁻ t, ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1
        2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k : AdelicGL2
        (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂
              / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y *
              NumberField.TateGlobal.ideleNorm K t) ∂(NumberField.Idele.idelicHaar K) =
        ∫⁻ t, ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N
            => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne (s * t) * (k :
            AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K (s * t))⁻¹) * (Set.Icc (NumberField.TateGlobal.ideleNorm
              K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y *
              NumberField.TateGlobal.ideleNorm K (s * t)) ∂(NumberField.Idele.idelicHaar K) :=
      (lintegral_mul_left_eq_self (μ := (NumberField.Idele.idelicHaar K))
        (fun t => ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
            AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂
              / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y *
              NumberField.TateGlobal.ideleNorm K t)) s).symm
    have hchain : ∫⁻ t, ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1
        2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k : AdelicGL2
        (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂
              / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y *
              NumberField.TateGlobal.ideleNorm K t) ∂(NumberField.Idele.idelicHaar K) ≤
        (ENNReal.ofReal G₂ * (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N => levelOne
            (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν Set.univ *
            (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
                (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)})) *
                ENNReal.ofReal (Y ^ (1 - σ)) :=
      ((hsubst.trans (lintegral_congr hpt)).trans_le hG1).trans_eq heq
    have hsum := hS3.symm.trans_le hchain

    have hAm : MeasurableSet (unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
        (NumberField.TateGlobal.ideleNorm K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))}) :=
      (upper_isOpen_unitsOff K S).measurableSet.inter
        ((isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm K)).measurableSet)
    have hI : ∀ 𝔫 : GoodIdeal K S, Y < (Ideal.absNorm 𝔫.1 : ℝ) → (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y →
        (∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc (NumberField.TateGlobal.ideleNorm
            K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
            ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
                levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
                AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(NumberField.Idele.idelicHaar K)) ≤
        ∫⁻ t in unitsOff K S, ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K
            c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t
            * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * (Set.Icc (NumberField.TateGlobal.ideleNorm K
                t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y *
                NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫.1 * t)) ∂(NumberField.Idele.idelicHaar K) := by
      intro 𝔫 h1 h2
      have hN0 : (0 : ℝ) < (Ideal.absNorm 𝔫.1 : ℝ) := hY.trans h1
      have hω : ∀ t ∈ unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
          (NumberField.TateGlobal.ideleNorm K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
          (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator
              (1 : ℝ → ℝ≥0∞) (Y * NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫.1 * t)) = 1 := by
        intro t ht
        obtain ⟨hlo, hhi⟩ := ht.2
        have htpos : 0 < NumberField.TateGlobal.ideleNorm K t := NumberField.TateGlobal.ideleNorm_pos t
        rw [idelePartition_ideleNorm_idealIdele_mul K 𝔫.2.1, Set.indicator_of_mem, Pi.one_apply]
        rw [Set.mem_Icc, mul_div_assoc', le_div_iff₀ hN0, div_le_iff₀ hN0]
        constructor
        · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hY.le, mul_nonneg (sub_nonneg.mpr h2) hρ.le]
        · nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) htpos.le, mul_nonneg (sub_nonneg.mpr hhi) hN0.le]
      have hmid : (∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
          (NumberField.TateGlobal.ideleNorm K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
            ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
                levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
                AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(NumberField.Idele.idelicHaar K)) =
          ∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc (NumberField.TateGlobal.ideleNorm
              K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
            ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
                levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
                AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * (Set.Icc (NumberField.TateGlobal.ideleNorm K
                  t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y *
                  NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫.1 * t)) ∂(NumberField.Idele.idelicHaar K) :=
        setLIntegral_congr_fun hAm (fun t ht => by rw [hω t ht, mul_one])
      exact hmid.trans_le (lintegral_mono_set Set.inter_subset_left)
    exact upper_classBlock_le_of_forall_le_of_tsum_le K S Ψ σ 𝒞 Y hY
      (∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc (NumberField.TateGlobal.ideleNorm K
          t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
            ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
                levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
                AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(NumberField.Idele.idelicHaar K))
      (ENNReal.ofReal G₂ * (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N => levelOne
          (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν Set.univ *
            (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
                (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)})) hm₀.ne'
                hBtop
      (fun 𝔫 => ∫⁻ t in unitsOff K S, ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) ''
          centreCutSiegelSet K c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen
          (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) * (Set.Icc (NumberField.TateGlobal.ideleNorm K t₂ /
            4) (2 * NumberField.TateGlobal.ideleNorm K t₂)).indicator (1 : ℝ → ℝ≥0∞) (Y *
            NumberField.TateGlobal.ideleNorm K (idealIdele K 𝔫.1 * t)) ∂(NumberField.Idele.idelicHaar K))
      hI hsum

  refine ⟨hblock Y₀ hY₀, ?_⟩
  have hn : ∀ 𝔫 : GoodIdeal K S, (0 : ℝ) < (Ideal.absNorm 𝔫.1 : ℝ) := fun 𝔫 =>
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h => 𝔫.2.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hpart := upper_tsum_le_of_forall_block_le (fun 𝔫 : GoodIdeal K S => GoodIdeal.cls K 𝔫 = 𝒞)
    (fun 𝔫 => (Ideal.absNorm 𝔫.1 : ℝ)) hn (fun 𝔫 => massSeq K Ψ (1 + σ) 𝔫.1)
    (ENNReal.ofReal (max 1 ((2 : ℝ) ^ σ)) * (ENNReal.ofReal G₂ * (productionPinsOf K (⋃ x ∈ T, (· * x) ''
        centreCutSiegelSet K c u 1 2) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞
        K) K v) (adelicBox K)).ν Set.univ *
            (NumberField.Idele.idelicHaar K) (D₀ ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
                (NumberField.TateGlobal.ideleNorm K t₂ / 4) (2 * NumberField.TateGlobal.ideleNorm K t₂)})) /
          (∫⁻ t in unitsOff K S ∩ {t | NumberField.TateGlobal.ideleNorm K t ∈ Set.Icc
              (NumberField.TateGlobal.ideleNorm K t₂ / 2) (4 * (NumberField.TateGlobal.ideleNorm K t₂ / 2))},
            ((‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2) (fun N =>
                levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
                (NumberField.StandardAddChar.stdAddChar K) (rightConv K (rightConv K g f₁) f₂) 1 (diagOne t * (k :
                AdelicGL2 (𝓞 K) K))‖₊ : ℝ≥0∞)) ^ 2 *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(NumberField.Idele.idelicHaar K)))
    (fun Y hY => by simpa only [classBlock] using hblock Y hY) Y₀ hY₀
  simpa only [classSum] using hpart

end WindowMultiplicity
p2m_reactivate "P2MW.S_AutomorphicForm_ClassSumGrowth_exists_forall_classBlock_le_and_classSum_le.WindowMultiplicity"

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm NumberField.AdelicHaar NumberField.AdelicBox
open NumberField.AdelicLevel
open scoped ENNReal
open WindowMultiplicity in
attribute [local instance] NumberField.AdelicHaar.glBorel in

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
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
      (∑' 𝔫 : {𝔫 : {𝔫 : Ideal (𝓞 K) // 𝔫 ≠ 0 ∧ ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔫} //
            ClassGroup.mk0 ⟨𝔫.1, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔫.2.1⟩ = 𝒞 ∧
              Y < (Ideal.absNorm 𝔫.1 : ℝ) ∧ (Ideal.absNorm 𝔫.1 : ℝ) ≤ 2 * Y},
          (‖∏ᶠ v : HeightOneSpectrum (𝓞 K),
              UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
                (Ψ.toRawCentral.b v) (emultiplicity v.asIdeal 𝔫.1.1).toNat‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((Ideal.absNorm 𝔫.1.1 : ℝ) ^ (1 + σ)))
        ≤ C * ENNReal.ofReal Y ∧
      (∑' 𝔫 : {𝔫 : {𝔫 : Ideal (𝓞 K) // 𝔫 ≠ 0 ∧ ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔫} //
            ClassGroup.mk0 ⟨𝔫.1, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔫.2.1⟩ = 𝒞 ∧
              (Ideal.absNorm 𝔫.1 : ℝ) ≤ Y},
          (‖∏ᶠ v : HeightOneSpectrum (𝓞 K),
              UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
                (Ψ.toRawCentral.b v) (emultiplicity v.asIdeal 𝔫.1.1).toNat‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((Ideal.absNorm 𝔫.1.1 : ℝ) ^ (1 + σ)))
        ≤ 2 * C * ENNReal.ofReal Y := by
  obtain ⟨C, hC, h⟩ :=
    exists_forall_classBlock_le_and_classSum_le K α β hβ hαβ Φ₀ hΦ₀ ξ σ hξ N hN S hS hSψ Ψ hV
  refine ⟨C, hC, fun 𝒞 Y hY => ?_⟩
  obtain ⟨h₁, h₂⟩ := h 𝒞 Y hY
  have hterm : ∀ 𝔫 : {𝔫 : Ideal (𝓞 K) // 𝔫 ≠ 0 ∧ ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔫},
      (‖∏ᶠ v : HeightOneSpectrum (𝓞 K),
            UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
              (Ψ.toRawCentral.b v) (emultiplicity v.asIdeal 𝔫.1).toNat‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((Ideal.absNorm 𝔫.1 : ℝ) ^ (1 + σ)) =
        massSeq K Ψ (1 + σ) 𝔫.1 := fun 𝔫 => by
    rw [massSeq, upper_recValue_eq_finprod_emultiplicity K Ψ 𝔫.2.1]
  dsimp only [classBlock, classSum, GoodIdeal, GoodIdeal.cls] at h₁ h₂
  simp only [← hterm] at h₁ h₂
  exact ⟨h₁, h₂⟩

end
end S_AutomorphicForm_ClassSumGrowth_exists_forall_classBlock_le_and_classSum_le
end P2MW
export P2MW.S_AutomorphicForm_ClassSumGrowth_exists_forall_classBlock_le_and_classSum_le (solution)
