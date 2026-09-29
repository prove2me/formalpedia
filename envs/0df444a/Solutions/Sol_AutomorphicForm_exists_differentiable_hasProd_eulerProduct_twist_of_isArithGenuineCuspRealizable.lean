-- Prove2me | solution 1 for AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ceec6a97-a6ec-55ff-941e-5c94fb82af9f

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Mathlib
import Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_toFun_eq_rightConv_of_isArithGenuineCuspRealizable
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_finset_badSet_rightConv_section
import Theorems.Thm_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentAverage_unramified_package
import Theorems.Thm_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow
import Theorems.Thm_UnramifiedWhittaker_exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq
import Theorems.Thm_AutomorphicForm_exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
import Theorems.Thm_AutomorphicForm_exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
import Theorems.Thm_Complex_exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_forall_norm_a_le_rpow_and_norm_b_le_rpow_of_moderateGrowth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000

section Assembly
open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open IsDedekindDomain NumberField.TateGlobal Polynomial UnramifiedWhittaker NumberField.StandardAddChar AdelicDock
open NumberField.AdeleRing

theorem globalPoints_unipotentGL2 (F : Type) [Field F] [NumberField F] (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [globalPoints, unipotentGL2]

theorem localRepSome_eq_repSome {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F)
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (b : v.adicCompletionIntegers F) :
    LocalGL2.localRepSome ϖ hπ b =
      repSome (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) b) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [LocalGL2.coe_localRepSome]
  fin_cases i <;> fin_cases j <;> simp [repSome]

theorem localRepInf_eq_repInf {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F)
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0) :
    LocalGL2.localRepInf ϖ hπ =
      repInf (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [LocalGL2.coe_localRepInf]
  fin_cases i <;> fin_cases j <;> simp [repInf]

theorem mem_levelOne_of_mem_levelOne_top (F : Type) [Field F] [NumberField F] {N : Ideal (𝓞 F)} (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, ¬ v.asIdeal ∣ N)
    (k : GL (Fin 2) (AdeleRing (𝓞 F) F)) (hk : k ∈ levelOne (𝓞 F) F ⊤)
    (hkS : ∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) :
    k ∈ levelOne (𝓞 F) F N := by

  have h1 : ∀ v ∈ S, finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = 1 := by
    intro v hv
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [finComponent_apply, glFin_apply, hkS v hv i j]
    fin_cases i <;> fin_cases j <;> rfl
  have hmS : ∀ v ∈ S, ∀ i j : Fin 2,
      (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v =
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j := by
    intro v hv i j
    have := congrArg (fun g : GL (Fin 2) (v.adicCompletion F) =>
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) (h1 v hv)
    simp only [finComponent_apply] at this
    exact this
  have hmS' : ∀ v ∈ S, ∀ i j : Fin 2,
      (((glFin (𝓞 F) F k)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v =
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j := by
    intro v hv i j
    have h2 : finComponent (𝓞 F) F v ((glFin (𝓞 F) F k)⁻¹) = 1 := by rw [map_inv, h1 v hv, inv_one]
    have := congrArg (fun g : GL (Fin 2) (v.adicCompletion F) =>
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) h2
    simp only [finComponent_apply] at this
    exact this
  have hball : ∀ (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)),
      (∀ i j, m i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 F) F) →
      (∀ v ∈ S, ∀ i j : Fin 2, m i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) →
      m 1 0 ∈ idealBall (𝓞 F) F N ∧ m 1 1 - 1 ∈ idealBall (𝓞 F) F N := by
    intro m hm hmv
    constructor
    · intro v
      by_cases hv : v ∈ S
      · rw [hmv v hv 1 0]
        simp
      · rw [idealBound_eq_one_of_not_dvd hN (hS v hv)]
        exact valued_apply_le_one (hm 1 0) v
    · intro v
      by_cases hv : v ∈ S
      · rw [coe_sub_apply, hmv v hv 1 1, coe_one_apply]
        simp
      · rw [idealBound_eq_one_of_not_dvd hN (hS v hv)]
        exact valued_apply_le_one (sub_mem_integralFiniteAdeles (hm 1 1) one_mem_integralFiniteAdeles) v
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk ⊢
  obtain ⟨⟨⟨hint, -⟩, -⟩, ⟨⟨hint', -⟩, -⟩⟩ := hk
  exact ⟨⟨⟨hint, (hball _ hint hmS).1⟩, (hball _ hint hmS).2⟩,
    ⟨⟨hint', (hball _ hint' hmS').1⟩, (hball _ hint' hmS').2⟩⟩

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S ∧ ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      Differentiable ℂ Λ ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * Φ.a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * Φ.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by
  classical

  obtain ⟨R, ξ, φf, f, hφ, hcontφ, hf, hR, hcontR⟩ :=
    AutomorphicForm.exists_smoothCuspRealizationAt_toFun_eq_rightConv_of_isArithGenuineCuspRealizable
      F c u d₁ d₂ T hd hcov Φ hΦ

  have hψ : IsGlobalAddChar F (stdAddChar F) := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F

  obtain ⟨S, hS₀, hSE, hSlev, hSχ, hχU, hnormU, hnorm, hKS, ϖ, hπ, ψv, sec, hsec, hsysP, hgen, hψ0, hψ1, hNc⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_finset_badSet_rightConv_section
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Φ R φf f hR (stdAddChar F) hψ χ hχc S₀
  have hSE' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v ∉ R.exceptionalSet := fun v hv h => hv (hSE h)

  have hϖval : ∀ v ∉ S,
      Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) =
        WithZero.exp (-1 : ℤ) := by
    intro v hv
    have h00 := congrArg (fun g : AdelicGL2 (𝓞 F) F =>
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 v) (hgen v hv)
    have e1 : ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (LocalGL2.diagPi (ϖ v) (hπ v))) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 v =
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) := by
      rw [← glFin_apply, glFin_finEmbed, ← finComponent_apply, finComponent_localEmbed_self, LocalGL2.coe_diagPi]
      simp
    have e2 : ((heckeGen (𝓞 F) F v : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 v =
        (uniformizerUnit F v : v.adicCompletion F) := by
      rw [heckeGen, heckeGenAt_snd_apply_self]
      simp
    rw [e1, e2] at h00
    rw [h00]
    exact valued_uniformizerUnit F v

  have hleftR : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      R.toFun (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = R.toFun g := by
    intro β g
    rw [← globalPoints_unipotentGL2]
    exact R.left_invariant _ g

  have harch : ∀ g : AdelicGL2 (𝓞 F) F,
      ContDiff ℝ (Module.finrank ℚ F + 1) (fun z : mixedEmbedding.mixedSpace F =>
        R.toFun (unipotentGL2 (R := AdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0) * g)) := by
    rw [hR]
    exact (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φf hcontφ f hf).2
  obtain ⟨hint, hsum⟩ :=
    AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
      (stdAddChar F) hψ R.toFun hleftR R.isKfSmooth harch

  haveI : ∀ v : HeightOneSpectrum (𝓞 F), Fintype (𝓞 F ⧸ v.asIdeal) := fun v => Fintype.ofFinite _
  have hI : ∀ v ∉ S, Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    intro v _
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

  have hsys : ∀ v ∉ S,
      HeckeIntegralSeam.IsHeckeCosetSystem
        (levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
        (fun i : Option (𝓞 F ⧸ v.asIdeal) => i.elim
          (placeEmbed F v (repInf
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)))
          (fun j => placeEmbed F v (repSome
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)
              (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v j)))))) := by
    intro v hv
    have hfun : (fun i : Option (𝓞 F ⧸ v.asIdeal) => i.elim
          (placeEmbed F v (repInf
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)))
          (fun j => placeEmbed F v (repSome
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)
              (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v j)))))) =
        (fun i : Option (𝓞 F ⧸ v.asIdeal) =>
          finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
            (i.elim (LocalGL2.localRepInf (ϖ v) (hπ v))
              (fun c => LocalGL2.localRepSome (ϖ v) (hπ v)
                (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v c)))))) := by
      funext i
      cases i with
      | none => simp only [Option.elim, placeEmbed, MonoidHom.comp_apply, localRepInf_eq_repInf]
      | some j => simp only [Option.elim, placeEmbed, MonoidHom.comp_apply, localRepSome_eq_repSome]
    rw [hfun]
    exact hsysP v hv

  have hN0 : ∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) R.toFun 1 (placeEmbed F v (unipotent x) * g) =
        ψv v x * whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) R.toFun 1 g :=
    fun v hv x g => hNc v hv x g R.toFun hleftR
  have hT0 := fun v (hv : v ∉ S) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) =>
    AutomorphicForm.SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Φ.toRawCentral R (stdAddChar F) hint v (hSE' v hv) (ϖ v) (hπ v)
      (fun c : 𝓞 F ⧸ v.asIdeal => algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v c)) (hI v hv)
      (hsysP v hv) 1 g
  have hZ0 := fun v (hv : v ∉ S) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) =>
    AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Φ.toRawCentral R (stdAddChar F) v (hSE' v hv) (ϖ v) (hπ v) (hgen v hv) 1 g
  have hK0 : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
        whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) R.toFun 1 (g * k) =
          whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) R.toFun 1 g := by
    intro k hk hkS g
    have hkU : k ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F :=
      ⟨mem_levelOne_of_mem_levelOne_top F Φ.level_ne_bot S hSlev k hk.1 hkS, hk.2⟩
    simp only [whittakerCoefficient]
    congr 1
    funext x
    rw [← mul_assoc, R.level_invariant _ k hkU]
  have hW0 : ∃ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) R.toFun 1 g ≠ 0 := by
    obtain ⟨g₁, hg₁⟩ := R.exists_ne_zero
    refine AutomorphicForm.exists_whittakerCoefficient_one_ne_zero F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
      (stdAddChar F) hψ R.toFun R.left_invariant g₁ ?_ ?_ (hsum g₁) hg₁
    · rw [whittakerCoefficient_zero_eq_constantTerm]
      exact R.smoothCusp.1.2 g₁
    · exact hcontR.comp (AutomorphicForm.continuous_unipotentGL2.mul continuous_const)
  obtain ⟨g₀, a₀, hg₀, ha₀, hWpt⟩ :=
    UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero F S
      (fun g => whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) R.toFun 1 g) ψv ϖ hπ hϖval
      (I := fun v => 𝓞 F ⧸ v.asIdeal)
      (fun v c => algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v c))
      Φ.toRawCentral.a Φ.toRawCentral.b hψ0 hψ1 hN0 hT0 hZ0 hK0 hW0
  have hW : whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) (rightConv F φf f) 1 (diagOne a₀ * g₀) ≠ 0 := by
    rw [← hR]; exact hWpt

  have hlev : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F,
      rightConv F φf f (g * k) = rightConv F φf f g := by
    intro g k hk
    rw [← hR]
    exact R.level_invariant g k hk
  have hHecke : ∀ v ∉ S,
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v (rightConv F φf f) (Φ.a v) := by
    intro v hv
    rw [← hR]
    exact R.hecke_eigen v (hSE' v hv)
  have hcentral : ∀ v ∉ S, ∀ g : AdelicGL2 (𝓞 F) F,
      rightConv F φf f (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) * g)
        = Φ.toRawCentral.b v * rightConv F φf f g := by
    intro v hv g
    rw [← hR]
    exact R.central_eigen v (hSE' v hv) g

  letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.ideleBorel F
  haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.borelSpace_ideleBorel F
  haveI : (NumberField.Idele.idelicHaar F).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar F

  have hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖R.toFun g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M := by
    obtain ⟨C₀, M, h⟩ := AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
      F c u d₁ d₂ T hd hcov ξ φf hφ hcontφ f hf
    exact ⟨C₀, M, fun g => by rw [hR]; exact h g⟩
  obtain ⟨κ, hκ0, hκE⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_forall_norm_a_le_rpow_and_norm_b_le_rpow_of_moderateGrowth
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Φ R hMG
  have hκ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ‖Φ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖Φ.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ :=
    fun v hv => hκE v (hSE' v hv)

  obtain ⟨σχ, hσχ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F χ hχ hχc
  have hτ : ∀ v ∉ S,
      ‖((χ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σχ) := by
    intro v _
    rw [hσχ, hnorm v, Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]

  obtain ⟨hL, hLdiff⟩ :=
    NumberField.TateGlobal.differentiableOn_tprod_eulerFactor_of_norm_le_rpow F S χ Φ.a Φ.b (-σχ) hτ κ hκ0 hκ
      (κ + -σχ + 4) le_rfl

  have hf' : IsFactorizableTestFn F (fun y => f (g₀⁻¹ * y)) :=
    AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn F f hf g₀

  have key : ∀ s₁ : ℂ, ∃ (Z E : ℂ → ℂ) (cc : ℂ) (σ : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ E ∧ cc ≠ 0 ∧
      E s₁ ≠ 0 ∧ ∀ s : ℂ, σ < s.re → Z s = cc * E s *
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * Φ.a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * Φ.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) := by
    intro s₁
    obtain ⟨B, ΦB, hB, hBstd, hΦB, hint6, hEdiff, hEne⟩ :=
      AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
        F c u d₁ d₂ T hd hcov ξ φf hφ hcontφ f hf (stdAddChar F) hψ χ hχ hχc S hKS
        g₀ hg₀ a₀ ha₀ hW s₁
    obtain ⟨σ₁, Z, hZ, hZint⟩ :=
      AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
        F c u d₁ d₂ T hd hcov ξ φf hφ hcontφ (fun y => f (g₀⁻¹ * y)) hf' B hB ΦB hΦB (stdAddChar F) hψ χ hχ hχc
        (NumberField.Idele.idelicHaar F)
    obtain ⟨hN', hK', hT', hZ', hU'⟩ :=
      AutomorphicForm.whittakerCoefficient_unipotentAverage_unramified_package
        F c u d₁ d₂ T hd hcov Φ ξ φf hφ hcontφ f hf (stdAddChar F) hψ S hlev hKS ψv hNc ϖ hπ
        (I := fun v => 𝓞 F ⧸ v.asIdeal)
        (fun v c => algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v c)) hI hsys hHecke hcentral hnormU
        g₀ hg₀ B hB hBstd ΦB hΦB
    obtain ⟨L', hL'⟩ :=
      UnramifiedWhittaker.exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq
        F (NumberField.Idele.idelicHaar F) Φ S χ
        (fun g => whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) ΦB 1 g) ψv ϖ hπ
        (I := fun v => 𝓞 F ⧸ v.asIdeal)
        (fun v c => algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v c)) hI hgen hψ0 hψ1
        hN' hK' hT' hZ' hU' hχU hnormU hnorm (-σχ) hτ κ hκ0 hκ (κ + -σχ + 4) le_rfl
        (NumberField.Idele.productMeasureData F S) (fun s _ => hint6 s)
    refine ⟨Z, fun s => ∫ a, zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (stdAddChar F) ΦB 1 g) χ s a
        ∂(NumberField.Idele.sPartMeasure F S),
      ((NumberField.Idele.productMeasureData F S).c : ℂ), max (κ + -σχ + 4) σ₁, hZ, hEdiff, ?_, hEne, ?_⟩
    · exact_mod_cast (NumberField.Idele.productMeasureData F S).c_pos.ne'
    · intro s hs
      have hs₀ : κ + -σχ + 4 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      obtain ⟨-, hZs⟩ := hZint s (lt_of_le_of_lt (le_max_right _ _) hs)
      obtain ⟨hP', -, hid⟩ := hL' s hs₀
      have hLL := hP'.unique (hL s hs₀)
      rw [← hZs, hid, hLL]
      rfl

  obtain ⟨Λ, hΛ, σ, hΛL⟩ :=
    Complex.exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq _ (κ + -σχ + 4)
      hLdiff.continuousOn key
  refine ⟨S, hS₀, max (κ + -σχ + 4) σ, Λ, hΛ, fun s hs => ?_⟩
  rw [hΛL s (lt_of_le_of_lt (le_max_right _ _) hs)]
  exact hL s (lt_of_le_of_lt (le_max_left _ _) hs)

end Assembly

end S_AutomorphicForm_exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_AutomorphicForm_exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable (solution)
