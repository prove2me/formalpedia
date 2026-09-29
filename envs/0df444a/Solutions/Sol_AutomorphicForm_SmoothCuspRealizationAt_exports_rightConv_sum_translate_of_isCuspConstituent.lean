-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.exports_rightConv_sum_translate_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a564076f-f7b5-563c-b8f4-5393d026e814

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_AutomorphicForm_summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate
import Theorems.Thm_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
import Theorems.Thm_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exports_rightConv_sum_translate_of_isCuspConstituent
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply"
p2m_attr_erase "simp" "Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace RS37S1

open MeasureTheory

theorem rightConv_sum_left_translate (K : Type) [Field K] [NumberField K]
    (φ f : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (hf : Continuous f) (hfs : HasCompactSupport f)
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ (fun z => ∑ i, cs i * f ((h i)⁻¹ * z)) g = ∑ i, cs i * rightConv K φ f (g * h i) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hterm : ∀ i, Integrable (fun z => φ (g * z) * (cs i * f ((h i)⁻¹ * z))) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro i
    have hc2 : Continuous fun z : AdelicGL2 (𝓞 K) K => cs i * f ((h i)⁻¹ * z) :=
      continuous_const.mul (hf.comp (continuous_mul_left _))
    have hcs : HasCompactSupport fun z : AdelicGL2 (𝓞 K) K => cs i * f ((h i)⁻¹ * z) := by
      refine HasCompactSupport.mul_left ?_
      exact hfs.comp_homeomorph (Homeomorph.mulLeft (h i)⁻¹)
    exact ((hφ.comp (continuous_mul_left g)).mul hc2).integrable_of_hasCompactSupport hcs.mul_left
  simp only [rightConv]
  rw [show (fun z => φ (g * z) * ∑ i, cs i * f ((h i)⁻¹ * z)) =
      fun z => ∑ i, φ (g * z) * (cs i * f ((h i)⁻¹ * z)) from funext fun z => Finset.mul_sum _ _ _]
  rw [integral_finset_sum _ fun i _ => hterm i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  have key := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun z => cs i * (φ (g * z) * f ((h i)⁻¹ * z))) (h i)
  simp only [inv_mul_cancel_left] at key
  calc ∫ a, φ (g * a) * (cs i * f ((h i)⁻¹ * a)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ a, cs i * (φ (g * a) * f ((h i)⁻¹ * a)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1; funext a; ring
    _ = ∫ a, cs i * (φ (g * (h i * a)) * f a) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := key.symm
    _ = ∫ a, cs i * (φ (g * h i * a) * f a) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1; funext a; rw [mul_assoc g]

theorem isFactorizableTestFn_sum_left_translate (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfT : IsFactorizableTestFn K f)
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (hharch : ∀ i, glArch (𝓞 K) K (h i) = 1) (cs : Fin n → ℂ) :
    IsFactorizableTestFn K (fun z => ∑ i, cs i * f ((h i)⁻¹ * z)) := by
  obtain ⟨fa, ff, hfa, ⟨hffl, hffc⟩, hfeq⟩ := hfT
  refine ⟨fa, fun y => ∑ i, cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y), hfa, ⟨?_, ?_⟩, ?_⟩
  · have hterm : ∀ i, IsLocallyConstant fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := fun i =>
      (IsLocallyConstant.const (cs i)).mul (hffl.comp_continuous (continuous_mul_left _))
    have : (fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => ∑ i, cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y)) =
        ∑ i, fun y => cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := by
      funext y; simp only [Finset.sum_apply]
    rw [this]
    exact Finset.sum_induction _ IsLocallyConstant (fun a b ha hb => ha.add hb)
      (IsLocallyConstant.const 0) (fun i _ => hterm i)
  · have hterm : ∀ i, HasCompactSupport fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := fun i =>
      (hffc.comp_homeomorph (Homeomorph.mulLeft (glFin (𝓞 K) K (h i))⁻¹)).mul_left
    have : (fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => ∑ i, cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y)) =
        ∑ i, fun y => cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := by
      funext y; simp only [Finset.sum_apply]
    rw [this]
    exact Finset.sum_induction _ HasCompactSupport (fun a b ha hb => ha.add hb)
      HasCompactSupport.zero (fun i _ => hterm i)
  · intro g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfeq ((h i)⁻¹ * g), map_mul, map_mul, map_inv, map_inv, hharch i, inv_one, one_mul]
    ring

theorem unipotentGL2_algebraMap_eq_globalPoints (K : Type) [Field K] [NumberField K] (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp

end RS37S1

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (_hc : 0 < c) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (_hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (_hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (_hRlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      R.toFun (g * k) = R.toFun g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hfT : IsFactorizableTestFn K f)
    (S Sf Sψ : Finset (HeightOneSpectrum (𝓞 K))) (_hSf : Sf ⊆ S) (_hSψ : Sψ ⊆ S)
    (_hfsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (_hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet)
    (_hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (_hV : IsCuspConstituent K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
    (_hx₀V : rightConv K R.toFun f ∈ V)
    (w : ℝ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (_h𝓕m : MeasurableSet 𝓕)
    (_h𝓕s : 𝓕 ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc 1 2})
    (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc 1 2}))
    (d₁' d₂' : ℝ) (_hd₁' : 0 < d₁')
    (r : ℕ) (h : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (_hharch : ∀ i, glArch (𝓞 K) K (h i) = 1)
    (_hhcomm : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h i)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum : ∀ g, x g = ∑ i, cs i * rightConv K R.toFun f (g * h i)) :
    x ∈ V ∧
    IsFactorizableTestFn K (fun z => ∑ i, cs i * f ((h i)⁻¹ * z)) ∧
    Continuous x ∧
    IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar x ∧
    (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) ∧
    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 0 g = 0) ∧
    (∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g) ∧
    (∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh)) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, Summable (fun b : K => ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x b g‖)) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        x (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g) ∧
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v)) ∧
    (∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g) ∧
    (∀ (t : AdelicGL2 (𝓞 K) K) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
      (∀ m : ℕ,
        whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g)) =
          UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ.toRawCentral.a v) (Θ.toRawCentral.b v) m *
            UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
              ((starRingEnd ℂ) (Θ.toRawCentral.a v)) ((starRingEnd ℂ) (Θ.toRawCentral.b v)) m *
            (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g))) ∧
      (∀ m : ℕ, 0 < m → whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0)) := by

  have hRc : Continuous R.toFun := _hR
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f _hfT
  set f' : AdelicGL2 (𝓞 K) K → ℂ := fun z => ∑ i, cs i * f ((h i)⁻¹ * z) with hf'def
  have hxf' : ∀ g, x g = rightConv K R.toFun f' g := fun g => by
    rw [_hxsum g, RS37S1.rightConv_sum_left_translate K R.toFun f hRc hfc hfcs h cs g]
  have hxfun : x = rightConv K R.toFun f' := funext hxf'

  have hxV : x ∈ V := by
    have hfun : x = ∑ i, cs i • rightTranslate K (h i) (rightConv K R.toFun f) := by
      funext g
      rw [_hxsum g, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [rightTranslate_apply, smul_eq_mul]
    rw [hfun]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact _hV.1.rightTranslate_fin_mem (h i) ((mem_finiteAdelicGL2Subgroup_iff K (h i)).mpr (_hharch i)) _ _hx₀V
  have hf'T : IsFactorizableTestFn K f' := RS37S1.isFactorizableTestFn_sum_left_translate K f _hfT h _hharch cs

  have hdecay : ∀ (t : AdelicGL2 (𝓞 K) K) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro t N
    have key := AutomorphicForm.integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet K
      c u d₁ d₂ T _hd _hcov R.centralChar R.toFun R.smoothCusp.1 _hR f' hf'T w 1 2 one_pos one_lt_two 𝓕 _h𝓕m _h𝓕s _h𝓕 c u d₁' d₂' _hc _hd₁' t N
    have hfun : (fun g => ‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) =
        (fun g => ‖rightConv K R.toFun f' g‖ ^ 2 * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) := by
      funext g; simp only [hxfun, sq]
    rw [hfun]; exact key

  obtain ⟨hxc, hxsmooth⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) R.centralChar x (_hV.1.le hxV)
  have hx1 : IsSmoothCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar x := by
    have h1 := hxsmooth 1
    have : rightTranslate K (1 : AdelicGL2 (𝓞 K) K) x = x := funext fun y => by simp [rightTranslate_apply]
    rwa [this] at h1
  have hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g := by
    letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).mS
    letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).μ⟩
    exact hx1.1.1.left_invariant
  have hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g := by
    letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).mS
    letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).μ⟩
    intro z g
    exact hx1.1.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hx0 : ∀ g, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 0 g = 0 := by
    intro g
    rw [whittakerCoefficient_zero_eq_constantTerm]
    exact hx1.1.2 g
  have hxleftN : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = x g := by
    intro β g
    rw [RS37S1.unipotentGL2_algebraMap_eq_globalPoints]
    exact hxG _ g
  have hxsmoothArch := (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K R.toFun _hR f' hf'T).2
  have hxint : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g := by
    have h1' := hx1.2
    have hN' := hxleftN
    rw [hxfun] at h1' hN' ⊢
    exact (AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) _ hN' h1'
      hxsmoothArch).1
  have hxper : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh) := by
    intro β uu hh
    rw [unipotentGL2_add, mul_assoc, RS37S1.unipotentGL2_algebraMap_eq_globalPoints, hxG]
  have hxW : ∀ g, Summable (fun b : K => ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x b g‖) := by
    have h1' := hx1.2
    have hN' := hxleftN
    rw [hxfun] at h1' hN' ⊢
    exact AutomorphicForm.summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) _ hN' h1' hxsmoothArch

  have PKG := AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate
      K c u d₁ d₂ T Θ R _hR (fun g k hk => _hRlev g k hk) f _hfT S Sf Sψ _hSf _hSψ _hfsupp _hS _hSψ0
  have PKGx := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) =>
    PKG r h cs _hharch _hhcomm x _hxsum hxint hxper hxZ v hv
  have hconv := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) => (PKGx v hv).1
  have hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g :=
    AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway K S x hx1.2
      (fun v hv => (hconv v hv).1)

  have hUWx : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
      (∀ m : ℕ,
        whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g)) =
          UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ.toRawCentral.a v) (Θ.toRawCentral.b v) m *
            UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
              ((starRingEnd ℂ) (Θ.toRawCentral.a v)) ((starRingEnd ℂ) (Θ.toRawCentral.b v)) m *
            (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g))) ∧
      (∀ m : ℕ, 0 < m → whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) := by
    intro v hv g hg
    obtain ⟨ψv, ϖ, hπ, b, hgen, -, hψ0, hψ1, hNw, hKw, hTw, hZw⟩ := (PKGx v hv).2
    haveI : Nonempty (Fin (Ideal.absNorm v.asIdeal)) := by
      refine ⟨⟨0, ?_⟩⟩
      rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have hI : Fintype.card (Fin (Ideal.absNorm v.asIdeal)) = Ideal.absNorm v.asIdeal := Fintype.card_fin _
    exact UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero K v ψv ϖ hπ hgen b hI hψ0 hψ1
      _ _ (Θ.toRawCentral.a v) (Θ.toRawCentral.b v) (Θ.toRawCentral.a v) (Θ.toRawCentral.b v)
      hNw hNw hKw hKw hTw hTw hZw hZw g hg
  exact ⟨hxV, hf'T, hxc, hx1, hxG, hxZ, hx0, hxint, hxper, hxW, hconv, hxKS, hdecay, hUWx⟩

end S_AutomorphicForm_SmoothCuspRealizationAt_exports_rightConv_sum_translate_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exports_rightConv_sum_translate_of_isCuspConstituent (solution)
