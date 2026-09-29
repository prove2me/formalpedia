-- Prove2me | solution 1 for AutomorphicForm.exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/dd4a486d-9cb3-5226-844d-4bb48ccaea63

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_cutProjector_of_isCompact
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval"
p2m_attr_erase "simp" "TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one"

set_option autoImplicit false

noncomputable section

section Standardness

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel

namespace StdL

variable (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

private def piScalar (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    GL (Fin 2) (v.adicCompletion L) :=
  ⟨Matrix.diagonal fun _ => algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ,
    Matrix.diagonal fun _ => (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [mul_inv_cancel₀ hϖ0, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal]; simp only [inv_mul_cancel₀ hϖ0, Matrix.diagonal_one]⟩

private def piUnit (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (v.adicCompletion L)ˣ :=
  Units.mk0 _ hϖ0

private theorem weyl_diagPi_weyl_diagPi (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (weylR : GL (Fin 2) (v.adicCompletion L)) * diagPi ϖ hϖ0 * weylR * diagPi ϖ hϖ0
      = piScalar L v ϖ hϖ0 := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagPi]
  show !![(0 : v.adicCompletion L), 1; 1, 0]
        * !![algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ, 0; 0, 1]
        * !![(0 : v.adicCompletion L), 1; 1, 0]
        * !![algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ, 0; 0, 1]
      = Matrix.diagonal fun _ => algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem diagPi_inv_eq (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (diagPi ϖ hϖ0)⁻¹
      = (piScalar L v ϖ hϖ0)⁻¹ * (weylR : GL (Fin 2) (v.adicCompletion L)) * diagPi ϖ hϖ0
          * weylR := by
  rw [← weyl_diagPi_weyl_diagPi L v ϖ hϖ0]
  group

private theorem finEmbed_localEmbed_piScalar (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v (piScalar L v ϖ hϖ0))
      = centralScalar (𝓞 L) L
          (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0))) := by
  apply Units.ext
  rw [coe_finEmbed, coe_localEmbed]
  show finMat (𝓞 L) L (localMat (𝓞 L) L v (piScalar L v ϖ hϖ0 : Matrix (Fin 2) (Fin 2) _))
      = Matrix.scalar (Fin 2)
          (((Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0)) :
              (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L))
  rw [Matrix.scalar_apply, Units.coe_map]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 L) L ?_ ?_
  · rw [mapMatrix_arch_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
    simp only [adeleArch_apply, finIncl_apply_fst, Matrix.diagonal_one]
  · rw [mapMatrix_fin_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
    simp only [adeleFin_apply, finIncl_apply_snd]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
      show Matrix.diagonal (fun _ => algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) ϖ)
          = Matrix.diagonal fun _ => finAdeleEval (𝓞 L) L w
              ((localUnit (𝓞 L) L w (piUnit L w ϖ hϖ0) : (FiniteAdeleRing (𝓞 L) L)ˣ) :
                FiniteAdeleRing (𝓞 L) L)
      rw [finAdeleEval_apply, localUnit_apply_self]
      rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 L) L v _ hw, RingHom.mapMatrix_apply,
        Matrix.diagonal_map (map_zero _)]
      simp only [finAdeleEval_apply, localUnit_apply_of_ne (𝓞 L) L v _ hw, Matrix.diagonal_one]

private theorem heckeGen_inv_eq_of_weyl_mem (U : Subgroup (AdelicGL2 (𝓞 L) L))
    (hU : finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR) ∈ U) :
    ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L), u₁ ∈ U ∧ u₂ ∈ U ∧
      (heckeGen (𝓞 L) L v)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L v * u₂ := by
  obtain ⟨ϖ, hϖ0, -, hgen, -⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen L v
  refine ⟨(Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0)))⁻¹,
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR), finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR),
    hU, hU, ?_⟩
  rw [← hgen, ← map_inv (finEmbed (𝓞 L) L), ← map_inv (localEmbed (𝓞 L) L v),
    diagPi_inv_eq L v ϖ hϖ0]
  simp only [map_mul, map_inv, finEmbed_localEmbed_piScalar]

private theorem finEmbed_localEmbed_weylR_mem (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (hv : ¬ v.asIdeal ∣ N) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR)
      ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    have hb : idealBound (𝓞 L) N v = 1 := idealBound_eq_one_of_not_dvd (R := 𝓞 L) hN hv
    have hW : IsLocalLevelOne (𝓞 L) L v N
        ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) := by
      refine ⟨fun i j => ?_, ?_, ?_⟩
      · show (!![(0 : v.adicCompletion L), 1; 1, 0] : Matrix (Fin 2) (Fin 2) _) i j
            ∈ v.adicCompletionIntegers L
        fin_cases i <;> fin_cases j <;> simp
      · show Valued.v ((!![(0 : v.adicCompletion L), 1; 1, 0] : Matrix (Fin 2) (Fin 2) _) 1 0)
            ≤ idealBound (𝓞 L) N v
        rw [hb]; simp
      · show Valued.v ((!![(0 : v.adicCompletion L), 1; 1, 0] : Matrix (Fin 2) (Fin 2) _) 1 1 - 1)
            ≤ idealBound (𝓞 L) N v
        rw [hb]; simp
    have hWinv : (((weylR : GL (Fin 2) (v.adicCompletion L))⁻¹ : GL (Fin 2) (v.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion L))
        = ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) :=
      rfl
    refine ⟨hW, ?_⟩
    rw [hWinv]
    exact hW
  · rw [mem_finiteAdelicGL2Subgroup_iff, glArch_finEmbed]

private theorem hstd_levelOne_heckeGen (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L),
        u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        (heckeGen (𝓞 L) L w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L w * u₂ :=
  fun w hw =>
    heckeGen_inv_eq_of_weyl_mem L w _
      (finEmbed_localEmbed_weylR_mem L w N hN fun hdvd => hw (hNS w hdvd))

end StdL

end Standardness

section SlabConstruction

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Venue

variable {K : Type} [Field K] [NumberField K]

open HeckeIntegralSeam

private theorem cosetSum_eq_of_isHeckeCosetSystem {U : Subgroup (AdelicGL2 (𝓞 K) K)} {gv : AdelicGL2 (𝓞 K) K}
    {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] {reps₀ : ι₀ → AdelicGL2 (𝓞 K) K} {reps₁ : ι₁ → AdelicGL2 (𝓞 K) K}
    (h₀ : IsHeckeCosetSystem U gv reps₀) (h₁ : IsHeckeCosetSystem U gv reps₁) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) (g : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (g * reps₀ i) = ∑ j, φ (g * reps₁ j) := by

  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (reps₀ i) : AdelicGL2 (𝓞 K) K ⧸ U) = QuotientGroup.mk (reps₁ j) :=
    fun i => h₁.covers (reps₀ i) (h₀.mem_doubleCoset i)
  choose f hf using hcov
  have hinj : Function.Injective f := by
    intro i i' hii'
    apply h₀.mk_injective
    simp only
    rw [hf i, hf i', hii']
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := h₀.covers (reps₁ j) (h₁.mem_doubleCoset j)
    refine ⟨i, h₁.mk_injective ?_⟩
    simp only
    rw [← hf i, hi]
  refine Fintype.sum_bijective f ⟨hinj, hsurj⟩ _ _ fun i => ?_

  have hu : (reps₀ i)⁻¹ * reps₁ (f i) ∈ U := QuotientGroup.eq.1 (hf i)
  have e : reps₁ (f i) = reps₀ i * ((reps₀ i)⁻¹ * reps₁ (f i)) := by group
  rw [e, ← mul_assoc, hφU _ _ hu]

end Venue

namespace SlabOrthogonality

variable (K : Type) [Field K] [NumberField K]

private abbrev slabPins (Φ : Set (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

private def slabPairing (Φ : Set (AdelicGL2 (𝓞 K) K)) (a b : AdelicGL2 (𝓞 K) K → ℂ) : ℂ :=
  ∫ g in Φ, a g * conj (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K

variable {K}

section Members

variable {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
variable (W : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
  (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))

private theorem invariant_and_eigen_of_mem {Φ : HeckeEigensystem K ℂ} (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    {reps₀ : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K}
    (hsys₀ : HeckeIntegralSeam.IsHeckeCosetSystem (U N) (gen v) reps₀) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ) :
    (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U N, φ (g * u) = φ g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K, ∑ i, φ (g * reps₀ i) = Φ.a v * φ g := by
  have hφ' : φ ∈
      Submodule.span ℂ {ψ | IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ ψ} := hφ
  clear hφ
  induction hφ' using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ x := hx
    have hxU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U N, x (g * u) = x g := fun g u hu => hx'.level_invariant g u hu
    refine ⟨hxU, fun g => ?_⟩
    obtain ⟨reps, hsys, heig⟩ := hx'.hecke_eigen v hv
    rw [Venue.cosetSum_eq_of_isHeckeCosetSystem hsys₀ hsys x hxU g]
    exact heig g
  | zero => exact ⟨fun _ _ _ => rfl, fun g => by simp⟩
  | add x y _ _ hx hy =>
    refine ⟨fun g u hu => ?_, fun g => ?_⟩
    · simp only [Pi.add_apply, hx.1 g u hu, hy.1 g u hu]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hx.2 g, hy.2 g, mul_add]
  | smul c x _ hx =>
    refine ⟨fun g u hu => ?_, fun g => ?_⟩
    · simp only [Pi.smul_apply, hx.1 g u hu]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx.2 g]
      ring

end Members

open AutomorphicForm.CuspidalConstituent

variable {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 K) K)}

private theorem isSlabFundamentalDomain_of_binders (hα : 0 < α) (hαβ : α < β)
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    IsSlabFundamentalDomain K α β Φ := by
  exact ⟨hα, hαβ, hΦs, hΦ⟩

private theorem pairing_zero_eq_slabPairing (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    pairing K Φ 0 a b = slabPairing K Φ a b := by
  simp only [pairing, slabPairing, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]

private theorem slabPairing_smul_left (c : ℂ) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    slabPairing K Φ (c • a) b = c * slabPairing K Φ a b := by
  unfold slabPairing
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

private theorem slabPairing_smul_right (c : ℂ) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    slabPairing K Φ a (c • b) = conj c * slabPairing K Φ a b := by
  unfold slabPairing
  simp_rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (conj c)]
  exact integral_const_mul _ _

private theorem memLp_two_of_mem {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {a : AdelicGL2 (𝓞 K) K → ℂ}
    (ha : a ∈ contMemberSubmodule K Φ ξ) : MemLp a 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
  ((mem_memberSubmodule_iff' K Φ ξ a).1 ha.1).2

private theorem integrable_mul_conj_of_mem {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {a b : AdelicGL2 (𝓞 K) K → ℂ} (ha : a ∈ contMemberSubmodule K Φ ξ) (hb : b ∈ contMemberSubmodule K Φ ξ) :
    Integrable (fun g => a g * conj (b g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
  (memLp_two_of_mem ha).integrable_mul (memLp_two_of_mem hb).star

private theorem slabPairing_sum_left (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) {n : ℕ}
    (a : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (ha : ∀ i, a i ∈ contMemberSubmodule K Φ ξ) (b : AdelicGL2 (𝓞 K) K → ℂ)
    (hb : b ∈ contMemberSubmodule K Φ ξ) :
    slabPairing K Φ (fun g => ∑ i, a i g) b = ∑ i, slabPairing K Φ (a i) b := by
  unfold slabPairing
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_conj_of_mem (ha i) hb

private theorem slabPairing_sum_right (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (a : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ contMemberSubmodule K Φ ξ) {n : ℕ} (b : Fin n → AdelicGL2 (𝓞 K) K → ℂ)
    (hb : ∀ i, b i ∈ contMemberSubmodule K Φ ξ) :
    slabPairing K Φ a (fun g => ∑ i, b i g) = ∑ i, slabPairing K Φ a (b i) := by
  unfold slabPairing
  simp_rw [map_sum, Finset.mul_sum]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_conj_of_mem ha (hb i)

private theorem weightedMeasure_zero_eq : weightedMeasure K Φ 0 = (adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ := by
  rw [weightedMeasure_def]
  have hone : (fun x => ENNReal.ofReal (weight K 0 x)) = (1 : AdelicGL2 (𝓞 K) K → ENNReal) := by
    funext x
    simp [weight_def]
  rw [hone, withDensity_one]

private theorem eq_zero_of_slabPairing_self_eq_zero (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (a : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ contMemberSubmodule K Φ ξ) (h : slabPairing K Φ a a = 0) : a = 0 := by
  have hsq : slabPairing K Φ a a = ((∫ g in Φ, ‖a g‖ ^ 2 ∂adelicGLHaar (Fin 2) (𝓞 K) K : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    unfold slabPairing
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Complex.mul_conj', Complex.ofReal_pow]
  have hint : Integrable (fun g => ‖a g‖ ^ 2) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    (memLp_two_of_mem ha).norm.integrable_sq
  have hzero : (fun g => ‖a g‖ ^ 2) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0 :=
    (integral_eq_zero_iff_of_nonneg (f := fun g => ‖a g‖ ^ 2) (fun g => sq_nonneg ‖a g‖) hint).1
      (Complex.ofReal_eq_zero.1 (hsq.symm.trans h))
  have hae : a =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0 := hzero.mono fun g hg => by simpa using hg
  refine eq_zero_of_toCarrier_eq_zero K hΦ₀ 0 ξ a ha ?_
  show (memLp_weightedMeasure_of_mem K hΦ₀ 0 ha.1).toLp a = 0
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine (MemLp.coeFn_toLp _).trans ?_
  rw [weightedMeasure_zero_eq]
  exact hae

private theorem exists_forall_slabPairing_rightTranslate_eq (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (r : AdelicGL2 (𝓞 K) K) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a b : AdelicGL2 (𝓞 K) K → ℂ, a ∈ contMemberSubmodule K Φ ξ → b ∈ contMemberSubmodule K Φ ξ →
        rightTranslate K r a ∈ contMemberSubmodule K Φ ξ ∧
        rightTranslate K r⁻¹ b ∈ contMemberSubmodule K Φ ξ ∧
        slabPairing K Φ (rightTranslate K r a) b = (κ : ℂ) * slabPairing K Φ a (rightTranslate K r⁻¹ b) := by
  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det r) :=
    NumberField.TateGlobal.ideleNorm_pos _

  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K
    (Real.sqrt (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det r))⁻¹)
    (Real.sqrt_pos.2 (inv_pos.2 hd))
  have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
    rw [show centralScalar (𝓞 K) K z = Matrix.GeneralLinearGroup.scalar (Fin 2) z from rfl,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, sq]
  obtain ⟨y, hy_def⟩ : ∃ y : AdelicGL2 (𝓞 K) K, y = centralScalar (𝓞 K) K z * r := ⟨_, rfl⟩
  have hy : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) = 1 := by
    rw [hy_def, map_mul, hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, hz,
      Real.mul_self_sqrt (inv_nonneg.2 hd.le), inv_mul_cancel₀ hd.ne']
  obtain ⟨c, hc_def⟩ : ∃ c : ℂ, c = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc_def]
    exact (ξ ⟨z, Subgroup.mem_top z⟩).ne_zero
  refine ⟨‖c⁻¹‖ ^ 2, pow_pos (norm_pos_iff.2 (inv_ne_zero hc0)) 2, fun a b ha hb => ?_⟩
  obtain ⟨hya', hyb', hpair⟩ :=
    rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one K hΦ₀ 0 ξ a b ha hb y hy
  have hcen_a := ((mem_memberSubmodule_iff' K Φ ξ a).1 ha.1).1.central_transform
  have hcen_b := ((mem_memberSubmodule_iff' K Φ ξ b).1 hb.1).1.central_transform

  have hya : ∀ g : AdelicGL2 (𝓞 K) K, a (g * y) = c * a (g * r) := by
    intro g
    rw [hy_def, ← mul_assoc, AutomorphicForm.SiegelCovering.mul_centralScalar_comm, mul_assoc, hc_def]
    exact hcen_a ⟨z, Subgroup.mem_top z⟩ (g * r)
  have hyb : ∀ g : AdelicGL2 (𝓞 K) K, b (g * y⁻¹) = c⁻¹ * b (g * r⁻¹) := by
    intro g
    rw [hy_def, mul_inv_rev, ← map_inv (centralScalar (𝓞 K) K) z, ← mul_assoc,
      AutomorphicForm.SiegelCovering.mul_centralScalar_comm]
    have h := hcen_b (⟨z, Subgroup.mem_top z⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))⁻¹ (g * r⁻¹)
    rw [map_inv ξ, Units.val_inv_eq_inv_val, ← hc_def] at h
    exact h
  have hra : rightTranslate K r a = c⁻¹ • rightTranslate K y a := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    rw [hya g, inv_mul_cancel_left₀ hc0]
  have hrb : rightTranslate K y⁻¹ b = c⁻¹ • rightTranslate K r⁻¹ b := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    exact hyb g
  have hrb' : rightTranslate K r⁻¹ b = c • rightTranslate K y⁻¹ b := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    rw [hyb g, mul_inv_cancel_left₀ hc0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hra]
    exact (contMemberSubmodule K Φ ξ).smul_mem _ hya'
  · rw [hrb']
    exact (contMemberSubmodule K Φ ξ).smul_mem _ hyb'
  · calc slabPairing K Φ (rightTranslate K r a) b
        _ = c⁻¹ * pairing K Φ 0 (rightTranslate K y a) b := by
          rw [hra, slabPairing_smul_left, pairing_zero_eq_slabPairing]
        _ = c⁻¹ * slabPairing K Φ a (rightTranslate K y⁻¹ b) := by rw [hpair, pairing_zero_eq_slabPairing]
        _ = ((‖c⁻¹‖ ^ 2 : ℝ) : ℂ) * slabPairing K Φ a (rightTranslate K r⁻¹ b) := by
          rw [hrb, slabPairing_smul_right, Complex.ofReal_pow, ← Complex.mul_conj', mul_assoc]

private theorem exists_forall_mul_slabPairing_eq (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (U : Subgroup (AdelicGL2 (𝓞 K) K)) (gv : AdelicGL2 (𝓞 K) K)
    (hstd : ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 K) K), u₁ ∈ U ∧ u₂ ∈ U ∧
      gv⁻¹ = centralScalar (𝓞 K) K z * u₁ * gv * u₂)
    {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps) :
    ∃ c : ℂ, ∀ (a b : AdelicGL2 (𝓞 K) K → ℂ) (A B : ℂ),
      a ∈ contMemberSubmodule K Φ ξ → b ∈ contMemberSubmodule K Φ ξ →
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, a (g * u) = a g) → (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, b (g * u) = b g) →
      (∀ g : AdelicGL2 (𝓞 K) K, ∑ i, a (g * reps i) = A * a g) →
      (∀ g : AdelicGL2 (𝓞 K) K, ∑ i, b (g * reps i) = B * b g) →
      A * slabPairing K Φ a b = c * conj B * slabPairing K Φ a b := by
  obtain ⟨z, u₁, u₂, hu₁, hu₂, hgv⟩ := hstd
  choose κ _ hκ using fun x : AdelicGL2 (𝓞 K) K => exists_forall_slabPairing_rightTranslate_eq hΦ₀ ξ x
  obtain ⟨i₀, -⟩ := hsys.covers gv (HeckePair.self_mem_doubleCoset (U := U) gv)
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 i₀.pos.ne'
  obtain ⟨w, hw_def⟩ : ∃ w : ℂ, w = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hcomm : ∀ X Y : AdelicGL2 (𝓞 K) K,
      X * (centralScalar (𝓞 K) K z * Y) = centralScalar (𝓞 K) K z * (X * Y) := fun X Y => by
    rw [← mul_assoc, AutomorphicForm.SiegelCovering.mul_centralScalar_comm, mul_assoc]
  refine ⟨(∑ i, (κ (reps i) : ℂ)) * conj w * (n : ℂ)⁻¹, fun a b A B ha hb haU hbU haE hbE => ?_⟩
  by_cases h0 : slabPairing K Φ a b = 0
  · simp only [h0, mul_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h0 (by simp [slabPairing])
  have haa : slabPairing K Φ a a ≠ 0 := fun h => ha0 (eq_zero_of_slabPairing_self_eq_zero hΦ₀ ξ a ha h)
  have hfix : ∀ u ∈ U, rightTranslate K u a = a := fun u hu => funext fun g => by
    rw [rightTranslate_apply]
    exact haU g u hu

  have hcost : ∀ u ∈ U, (κ u : ℂ) = 1 := by
    intro u hu
    have h1 := (hκ u a a ha ha).2.2
    rw [hfix u hu, hfix u⁻¹ (inv_mem hu)] at h1
    exact mul_right_cancel₀ haa (h1.symm.trans (one_mul _).symm)

  have hfree : ∀ u ∈ U, ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ, ψ ∈ contMemberSubmodule K Φ ξ →
      slabPairing K Φ a (rightTranslate K u ψ) = slabPairing K Φ a ψ := by
    intro u hu ψ hψ
    have h1 := (hκ u⁻¹ a ψ ha hψ).2.2
    rw [inv_inv, hcost u⁻¹ (inv_mem hu), one_mul, hfix u⁻¹ (inv_mem hu)] at h1
    exact h1.symm
  have hcen_b := ((mem_memberSubmodule_iff' K Φ ξ b).1 hb.1).1.central_transform
  have hgvb : rightTranslate K gv b ∈ contMemberSubmodule K Φ ξ := (hκ gv b b hb hb).1

  have hL : A * slabPairing K Φ a b =
      (∑ i, (κ (reps i) : ℂ)) * (conj w * slabPairing K Φ a (rightTranslate K gv b)) := by
    have hsum := slabPairing_sum_left ξ (fun i => rightTranslate K (reps i) a)
      (fun i => (hκ (reps i) a b ha hb).1) b hb
    have hfun : (fun g => ∑ i, rightTranslate K (reps i) a g) = A • a := by
      funext g
      simp only [rightTranslate_apply, Pi.smul_apply, smul_eq_mul]
      exact haE g
    rw [hfun, slabPairing_smul_left] at hsum
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨u, hu, u', hu', hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hsys.mem_doubleCoset i)
    have hinv : rightTranslate K (reps i)⁻¹ b = w • rightTranslate K (u'⁻¹ * u₁) (rightTranslate K gv b) := by
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
      have hg : g * (reps i)⁻¹ = centralScalar (𝓞 K) K z * (g * (u'⁻¹ * u₁) * gv) * (u₂ * u⁻¹) := by
        rw [← hrep, mul_inv_rev, mul_inv_rev, hgv]
        simp only [mul_assoc]
        rw [hcomm, hcomm]
      rw [hg, hbU _ _ (mul_mem hu₂ (inv_mem hu)), hw_def]
      exact hcen_b ⟨z, Subgroup.mem_top z⟩ _
    rw [(hκ (reps i) a b ha hb).2.2, hinv, slabPairing_smul_right, hfree _ (mul_mem (inv_mem hu') hu₁) _ hgvb]

  have hR : conj B * slabPairing K Φ a b = (n : ℂ) * slabPairing K Φ a (rightTranslate K gv b) := by
    have hsum := slabPairing_sum_right ξ a ha (fun i => rightTranslate K (reps i) b)
      (fun i => (hκ (reps i) b b hb hb).1)
    have hfun : (fun g => ∑ i, rightTranslate K (reps i) b g) = B • b := by
      funext g
      simp only [rightTranslate_apply, Pi.smul_apply, smul_eq_mul]
      exact hbE g
    rw [hfun, slabPairing_smul_right] at hsum
    rw [hsum]
    have hterm : ∀ i, slabPairing K Φ a (rightTranslate K (reps i) b) =
        slabPairing K Φ a (rightTranslate K gv b) := by
      intro i
      obtain ⟨u, hu, u', hu', hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hsys.mem_doubleCoset i)
      have hrt : rightTranslate K (reps i) b = rightTranslate K u (rightTranslate K gv b) := by
        funext g
        simp only [rightTranslate_apply]
        rw [← hrep, ← mul_assoc, ← mul_assoc, hbU _ _ hu']
      rw [hrt, hfree u hu _ hgvb]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc A * slabPairing K Φ a b
    _ = (∑ i, (κ (reps i) : ℂ)) * conj w * slabPairing K Φ a (rightTranslate K gv b) := by rw [hL]; ring
    _ = (∑ i, (κ (reps i) : ℂ)) * conj w * (n : ℂ)⁻¹ *
          ((n : ℂ) * slabPairing K Φ a (rightTranslate K gv b)) := by
        rw [mul_assoc _ (n : ℂ)⁻¹, inv_mul_cancel_left₀ hn]
    _ = (∑ i, (κ (reps i) : ℂ)) * conj w * (n : ℂ)⁻¹ * conj B * slabPairing K Φ a b := by rw [← hR]; ring

private theorem mem_contMemberSubmodule_of_isIsotypicCuspFormAt
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {π : HeckeEigensystem K ℂ} {a : AdelicGL2 (𝓞 K) K → ℂ} (ha : IsIsotypicCuspFormAt K (slabPins K Φ) ξ N S π a) :
    a ∈ contMemberSubmodule K Φ ξ := by
  exact ⟨(mem_memberSubmodule_iff K Φ ξ a).2 ha.smoothCusp.1.1, ha.continuous⟩

private theorem isotypicCuspSubmodule_le_contMemberSubmodule
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (π : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ≤ contMemberSubmodule K Φ ξ := by
  exact Submodule.span_le.2 fun a ha => mem_contMemberSubmodule_of_isIsotypicCuspFormAt ξ N S ha

private theorem toRawCentral_b_eq_of_mem_cuspClasses (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) {π : HeckeEigensystem K ℂ}
    (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    π.toRawCentral.b v =
      ((ξ ⟨Matrix.GeneralLinearGroup.det ((slabPins K Φ).gen v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
  obtain ⟨χ, hχ, hne⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hne
  have h₁ := hχ.central_eigen v hv g
  have h₂ := ((isAutomorphicFnAt_fdPins_iff K Φ ξ χ).1 hχ.smoothCusp.1.1).1.central_transform
    ⟨Matrix.GeneralLinearGroup.det ((slabPins K Φ).gen v), Subgroup.mem_top _⟩ g
  exact mul_right_cancel₀ hg (h₁.symm.trans h₂)

private theorem b_eq_b_of_mem_cuspClasses (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) {π π' : HeckeEigensystem K ℂ}
    (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S) (hπ' : π' ∈ cuspClasses K (slabPins K Φ) ξ N S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) : π.b v = π'.b v := by
  have h := (toRawCentral_b_eq_of_mem_cuspClasses ξ N S hπ v hv).trans
    (toRawCentral_b_eq_of_mem_cuspClasses ξ N S hπ' v hv).symm
  rw [HeckeEigensystem.toRawCentral_b, HeckeEigensystem.toRawCentral_b] at h
  exact mul_left_cancel₀ (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero v)) h

private theorem exists_a_ne_of_ne_of_mem_cuspClasses (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) {π π' : HeckeEigensystem K ℂ}
    (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S) (hπ' : π' ∈ cuspClasses K (slabPins K Φ) ξ N S)
    (hne : π ≠ π') : ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ π.a v ≠ π'.a v := by
  by_contra h
  exact hne (eq_of_mem_cuspClasses hπ hπ' fun v hv =>
    ⟨Classical.byContradiction fun hav => h ⟨v, hv, hav⟩, b_eq_b_of_mem_cuspClasses ξ N S hπ hπ' v hv⟩)

private theorem exists_finite_orthonormal_spanning_family (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (tys : ArchTypeFamily K) (π : HeckeEigensystem K ℂ)
    [FiniteDimensional ℂ ↥(isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys)] :
    ∃ (m : ℕ) (b : Fin m → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ k, b k ∈ isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys) ∧
      (∀ k l, slabPairing K Φ (b k) (b l) = if l = k then 1 else 0) ∧
      Submodule.span ℂ (Set.range b) = isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys := by
  set P := isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys with hP
  have hcont : ∀ x : ↥P, (x : AdelicGL2 (𝓞 K) K → ℂ) ∈ contMemberSubmodule K Φ ξ := fun x =>
    isotypicCuspSubmodule_le_contMemberSubmodule ξ N S π x.2.1
  have hle : P ≤ memberSubmodule K Φ ξ := fun _ hx => (isotypicCuspSubmodule_le_contMemberSubmodule ξ N S π hx.1).1
  obtain ⟨T, hT⟩ : ∃ T : ↥P →ₗ[ℂ] Carrier K Φ 0, T = (toCarrier K hΦ₀ 0 ξ).comp (Submodule.inclusion hle) :=
    ⟨_, rfl⟩

  have hTcoe : ∀ x : ↥P, ⇑(T x) =ᵐ[weightedMeasure K Φ 0] (x : AdelicGL2 (𝓞 K) K → ℂ) := by
    intro x
    rw [hT]
    exact MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem K hΦ₀ 0 (hle x.2))
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun x hx => Subtype.ext ?_
    rw [hT] at hx
    exact eq_zero_of_toCarrier_eq_zero K hΦ₀ 0 ξ (x : AdelicGL2 (𝓞 K) K → ℂ) (hcont x) hx

  have hpair : ∀ x y : ↥P,
      slabPairing K Φ (x : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K → ℂ) = inner ℂ (T y) (T x) := by
    intro x y
    rw [L2.inner_def]
    simp_rw [RCLike.inner_apply]
    unfold slabPairing
    rw [← weightedMeasure_zero_eq]
    refine integral_congr_ae ?_
    filter_upwards [hTcoe x, hTcoe y] with g hx hy
    rw [hx, hy]

  obtain ⟨φ, hφ⟩ : ∃ φ : ↥P ≃ₗ[ℂ] ↥(LinearMap.range T),
      ∀ x, ((φ x : ↥(LinearMap.range T)) : Carrier K Φ 0) = T x :=
    ⟨LinearEquiv.ofInjective T hinj, fun _ => rfl⟩
  obtain ⟨m, ⟨e⟩⟩ : ∃ m : ℕ, Nonempty (OrthonormalBasis (Fin m) ℂ ↥(LinearMap.range T)) :=
    ⟨_, ⟨stdOrthonormalBasis ℂ ↥(LinearMap.range T)⟩⟩
  obtain ⟨bas, hbas⟩ : ∃ bas : Module.Basis (Fin m) ℂ ↥P, ∀ k, bas k = φ.symm (e k) :=
    ⟨e.toBasis.map φ.symm, fun k => by rw [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]⟩
  have hTbas : ∀ k, T (bas k) = ((e k : ↥(LinearMap.range T)) : Carrier K Φ 0) := by
    intro k
    rw [hbas, ← hφ, LinearEquiv.apply_symm_apply]
  refine ⟨m, fun k => (bas k : AdelicGL2 (𝓞 K) K → ℂ), fun k => (bas k).2, fun k l => ?_, ?_⟩
  · rw [hpair, hTbas, hTbas]
    exact orthonormal_iff_ite.1 e.orthonormal l k
  · refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun k => (bas k).2)) fun x hx => ?_
    have h := Submodule.mem_map_of_mem (f := P.subtype) (bas.mem_span ⟨x, hx⟩)
    rw [← Submodule.span_image, ← Set.range_comp'] at h
    exact h

private theorem fibre_finite {C : Set (HeckeEigensystem K ℂ)} (m : HeckeEigensystem K ℂ → ℕ)
    {π : HeckeEigensystem K ℂ} (hπ : π ∈ C) : {i : Σ p : ↥C, Fin (m p.1) | i.1.1 = π}.Finite := by
  refine (Set.finite_range fun k : Fin (m π) => (⟨⟨π, hπ⟩, k⟩ : Σ p : ↥C, Fin (m p.1))).subset ?_
  rintro ⟨⟨π', hπ'⟩, k⟩ (rfl : π' = π)
  exact ⟨k, rfl⟩

private theorem image_fibre_eq {C : Set (HeckeEigensystem K ℂ)} (m : HeckeEigensystem K ℂ → ℕ)
    (c : ∀ p : HeckeEigensystem K ℂ, Fin (m p) → AdelicGL2 (𝓞 K) K → ℂ) {π : HeckeEigensystem K ℂ} (hπ : π ∈ C) :
    (fun i : Σ p : ↥C, Fin (m p.1) => c i.1.1 i.2) '' {i | i.1.1 = π} = Set.range (c π) := by
  ext f
  constructor
  · rintro ⟨⟨⟨π', hπ'⟩, k⟩, (rfl : π' = π), rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨⟨π, hπ⟩, k⟩, rfl, rfl⟩

private theorem integral_mul_conj_eq_zero_of_ne_of_mem_cuspClasses (hα : 0 < α) (hαβ : α < β)
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    {π π' : HeckeEigensystem K ℂ} (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S)
    (hπ' : π' ∈ cuspClasses K (slabPins K Φ) ξ N S) (hne : π ≠ π') {a b : AdelicGL2 (𝓞 K) K → ℂ}
    (ha : a ∈ isotypicCuspSubmodule K (slabPins K Φ) ξ N S π)
    (hb : b ∈ isotypicCuspSubmodule K (slabPins K Φ) ξ N S π') :
    ∫ g in Φ, a g * starRingEnd ℂ (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0 := by
  have hΦ₀ : IsSlabFundamentalDomain K α β Φ := isSlabFundamentalDomain_of_binders hα hαβ hΦs hΦ
  have ha' : a ∈ contMemberSubmodule K Φ ξ := isotypicCuspSubmodule_le_contMemberSubmodule ξ N S π ha
  have hb' : b ∈ contMemberSubmodule K Φ ξ := isotypicCuspSubmodule_le_contMemberSubmodule ξ N S π' hb
  show slabPairing K Φ a b = 0
  by_cases hb0 : b = 0
  · rw [hb0]
    simp [slabPairing]

  obtain ⟨v, hv, hav⟩ := exists_a_ne_of_ne_of_mem_cuspClasses ξ N S hπ hπ' hne
  obtain ⟨χ, hχ, -⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ
  obtain ⟨reps, hsys, -⟩ := hχ.hecke_eigen v hv
  obtain ⟨haU, haE⟩ := invariant_and_eigen_of_mem Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) N S v hv hsys ha
  obtain ⟨hbU, hbE⟩ := invariant_and_eigen_of_mem Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) N S v hv hsys hb

  obtain ⟨c, hc⟩ := exists_forall_mul_slabPairing_eq hΦ₀ ξ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (heckeGen (𝓞 K) K v) (StdL.hstd_levelOne_heckeGen K N hN S hNS v hv) reps hsys
  have hab := hc a b (π.a v) (π'.a v) ha' hb' haU hbU haE hbE
  have hbb := hc b b (π'.a v) (π'.a v) hb' hb' hbU hbU hbE hbE
  have hbb0 : slabPairing K Φ b b ≠ 0 := fun h => hb0 (eq_zero_of_slabPairing_self_eq_zero hΦ₀ ξ b hb' h)
  rw [← mul_right_cancel₀ hbb0 hbb] at hab
  exact (mul_eq_mul_right_iff.1 hab).resolve_left hav

end SlabOrthogonality

end SlabConstruction

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalSpectrum SlabOrthogonality

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace SlabOrthogonality

private theorem eq_zero_of_mem_topologicalClosure_of_mem_orthogonal {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Submodule ℂ E) {x : E} (hx : x ∈ S.topologicalClosure) (hx' : x ∈ Sᗮ) : x = 0 := by
  have hle : S.topologicalClosure ≤ Sᗮᗮ :=
    S.topologicalClosure_minimal S.le_orthogonal_orthogonal Sᗮ.isClosed_orthogonal
  have h : x ∈ Sᗮ ⊓ Sᗮᗮ := ⟨hx', hle hx⟩
  rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h

private theorem rpow_mul_toReal_eLpNorm_le {X : Type} [MeasurableSpace X] {ν ρ : Measure X} {c : ℝ} (hc : 0 < c)
    (h : ENNReal.ofReal c • ν ≤ ρ) {f : X → ℂ} (hf : MemLp f 2 ρ) :
    c ^ (1 / 2 : ℝ) * (eLpNorm f 2 ν).toReal ≤ (eLpNorm f 2 ρ).toReal := by
  have h1 : eLpNorm f 2 (ENNReal.ofReal c • ν) ≤ eLpNorm f 2 ρ := eLpNorm_mono_measure f h
  rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top f, smul_eq_mul] at h1
  have h2 : ((1 : ENNReal) / 2).toReal = (1 / 2 : ℝ) := by simp
  rw [h2] at h1
  have h3 := ENNReal.toReal_mono hf.eLpNorm_ne_top h1
  rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hc.le] at h3

private theorem mem_topologicalClosure_map_of_forall_mul_norm_le {M E₀ E₁ : Type} [AddCommGroup M] [Module ℂ M]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    (T₀ : M →ₗ[ℂ] E₀) (T₁ : M →ₗ[ℂ] E₁) {k : ℝ} (hk : 0 < k) (hT : ∀ z, k * ‖T₀ z‖ ≤ ‖T₁ z‖)
    (W : Submodule ℂ M) {x : M} (hx : T₁ x ∈ (W.map T₁).topologicalClosure) :
    T₀ x ∈ (W.map T₀).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hx ⊢
  intro ε hε
  obtain ⟨z, hz, hdist⟩ := hx (k * ε) (mul_pos hk hε)
  obtain ⟨y, hyW, rfl⟩ := Submodule.mem_map.1 hz
  refine ⟨T₀ y, Submodule.mem_map_of_mem hyW, ?_⟩
  rw [dist_eq_norm, ← map_sub] at hdist ⊢
  exact lt_of_mul_lt_mul_left ((hT (x - y)).trans_lt hdist) hk.le

private theorem smul_restrict_le_weightedMeasure (K : Type) [Field K] [NumberField K] {α β : ℝ}
    {Φ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : IsSlabFundamentalDomain K α β Φ) (σ : ℝ) :
    ENNReal.ofReal (min (α ^ (-σ)) (β ^ (-σ))) • (adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ ≤
      weightedMeasure K Φ σ := by
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K
  have hres : μ.restrict Φ = (μ.restrict (detNormSlab K α β)).restrict Φ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  have hae : ∀ᵐ x ∂(μ.restrict Φ), x ∈ Φ := by
    rw [hres]
    exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet
  have hbound : ∀ x ∈ Φ, min (α ^ (-σ)) (β ^ (-σ)) ≤ weight K σ x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hΦ₀.subset hx
    rw [weight_def]
    rcases le_or_gt 0 (-σ) with hs | hs
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow hΦ₀.pos.le h1 hs)
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hΦ₀.pos.trans_le h1) h2 hs.le)
  rw [weightedMeasure_def, ← withDensity_const]
  exact withDensity_mono (hae.mono fun x hx => ENNReal.ofReal_le_ofReal (hbound x hx))

private theorem rpow_mul_norm_toCarrier_zero_le (K : Type) [Field K] [NumberField K] {α β : ℝ}
    {Φ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : IsSlabFundamentalDomain K α β Φ) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (ψ : ↥(memberSubmodule K Φ ξ)) :
    (min (α ^ (-σ)) (β ^ (-σ))) ^ (1 / 2 : ℝ) * ‖toCarrier K hΦ₀ 0 ξ ψ‖ ≤ ‖toCarrier K hΦ₀ σ ξ ψ‖ := by
  have hc : 0 < min (α ^ (-σ)) (β ^ (-σ)) :=
    lt_min (Real.rpow_pos_of_pos hΦ₀.pos _) (Real.rpow_pos_of_pos hΦ₀.pos_right _)
  have h0 : ‖toCarrier K hΦ₀ 0 ξ ψ‖ =
      (eLpNorm (ψ : AdelicGL2 (𝓞 K) K → ℂ) 2 (weightedMeasure K Φ 0)).toReal :=
    Lp.norm_toLp _ (memLp_weightedMeasure_of_mem K hΦ₀ 0 ψ.2)
  have hs : ‖toCarrier K hΦ₀ σ ξ ψ‖ =
      (eLpNorm (ψ : AdelicGL2 (𝓞 K) K → ℂ) 2 (weightedMeasure K Φ σ)).toReal :=
    Lp.norm_toLp _ (memLp_weightedMeasure_of_mem K hΦ₀ σ ψ.2)
  rw [h0, hs, weightedMeasure_zero_eq]
  exact rpow_mul_toReal_eLpNorm_le hc (smul_restrict_le_weightedMeasure K hΦ₀ σ)
    (memLp_weightedMeasure_of_mem K hΦ₀ σ ψ.2)

private theorem slabPairing_eq_inner_toCarrier_zero (K : Type) [Field K] [NumberField K] {α β : ℝ}
    {Φ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (x y : ↥(memberSubmodule K Φ ξ)) :
    slabPairing K Φ (x : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K → ℂ) =
      inner ℂ (toCarrier K hΦ₀ 0 ξ y) (toCarrier K hΦ₀ 0 ξ x) := by
  have hx : ⇑(toCarrier K hΦ₀ 0 ξ x) =ᵐ[weightedMeasure K Φ 0] (x : AdelicGL2 (𝓞 K) K → ℂ) :=
    MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem K hΦ₀ 0 x.2)
  have hy : ⇑(toCarrier K hΦ₀ 0 ξ y) =ᵐ[weightedMeasure K Φ 0] (y : AdelicGL2 (𝓞 K) K → ℂ) :=
    MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem K hΦ₀ 0 y.2)
  rw [L2.inner_def]
  simp_rw [RCLike.inner_apply]
  unfold slabPairing
  rw [← weightedMeasure_zero_eq]
  refine integral_congr_ae ?_
  filter_upwards [hx, hy] with g hxg hyg
  rw [hxg, hyg]

private theorem span_range_le_contMemberSubmodule {K : Type} [Field K] [NumberField K] {Φ : Set (AdelicGL2 (𝓞 K) K)}
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (tys : ArchTypeFamily K) {ι : Type} (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (h₁ : ∀ i, cls i ∈ cuspClasses K (slabPins K Φ) ξ N S ∧
      b i ∈ isotypicCuspSubmodule K (slabPins K Φ) ξ N S (cls i) ⊓ archCutSubmodule K tys) :
    Submodule.span ℂ (Set.range b) ≤ contMemberSubmodule K Φ ξ := by
  refine Submodule.span_le.2 fun a ha => ?_
  obtain ⟨i, rfl⟩ := ha
  exact isotypicCuspSubmodule_le_contMemberSubmodule ξ N S (cls i) (h₁ i).2.1

private theorem slabPairing_eq_zero_of_mem_span_range {K : Type} [Field K] [NumberField K]
    {Φ : Set (AdelicGL2 (𝓞 K) K)}
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : φ ∈ contMemberSubmodule K Φ ξ)
    {ι : Type} {b : ι → AdelicGL2 (𝓞 K) K → ℂ} (hb : Submodule.span ℂ (Set.range b) ≤ contMemberSubmodule K Φ ξ)
    (hperp : ∀ i, slabPairing K Φ φ (b i) = 0) {w : AdelicGL2 (𝓞 K) K → ℂ} (hw : w ∈ Submodule.span ℂ (Set.range b)) :
    slabPairing K Φ φ w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hperp i
  | zero => simp [slabPairing]
  | add x y hx hy ihx ihy =>
    have hadd : slabPairing K Φ φ (x + y) = slabPairing K Φ φ x + slabPairing K Φ φ y := by
      unfold slabPairing
      simp_rw [Pi.add_apply, map_add, mul_add]
      exact integral_add (integrable_mul_conj_of_mem hφ (hb hx)) (integrable_mul_conj_of_mem hφ (hb hy))
    rw [hadd, ihx, ihy, add_zero]
  | smul c x _ ih => rw [slabPairing_smul_right, ih, mul_zero]

private theorem apply_mem_topologicalClosure_map {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (P : E →L[ℂ] F) (J : Submodule ℂ E) {x : E}
    (hx : x ∈ J.topologicalClosure) :
    P x ∈ (J.map (P : E →ₗ[ℂ] F)).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx ⊢
  refine map_mem_closure P.continuous hx fun y hy => ?_
  exact Submodule.mem_map_of_mem hy

private theorem topologicalClosure_le_topologicalClosure {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {J A : Submodule ℂ E} (h : J ≤ A.topologicalClosure) : J.topologicalClosure ≤ A.topologicalClosure :=
  J.topologicalClosure_minimal h A.isClosed_topologicalClosure

private theorem apply_eq_zero_of_mem_orthogonal_of_forall_eigenspace_le {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (Tc : E →L[ℂ] E) (hcpt : IsCompactOperator Tc)
    (hsymm : (Tc : E →ₗ[ℂ] E).IsSymmetric) (I : Submodule ℂ E) (hI : ∀ x ∈ I, Tc x ∈ I)
    (heig : ∀ μ : ℂ, μ ≠ 0 → Module.End.eigenspace (Tc : Module.End ℂ E) μ ≤ I) {z : E} (hz : z ∈ Iᗮ) : Tc z = 0 := by
  have hsup : (⨆ μ : ℂ, Module.End.eigenspace (Tc : Module.End ℂ E) μ) ≤ LinearMap.ker (Tc : E →ₗ[ℂ] E) ⊔ I := by
    refine iSup_le fun μ => ?_
    by_cases hμ : μ = 0
    · subst hμ
      rw [Module.End.eigenspace_zero]
      exact le_sup_left
    · exact (heig μ hμ).trans le_sup_right
  have hbot : (LinearMap.ker (Tc : E →ₗ[ℂ] E) ⊔ I)ᗮ = ⊥ :=
    le_bot_iff.1 ((Submodule.orthogonal_le hsup).trans
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcpt hsymm).le)
  have htop : (LinearMap.ker (Tc : E →ₗ[ℂ] E) ⊔ I).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2 hbot
  have hz' : z ∈ (LinearMap.ker (Tc : E →ₗ[ℂ] E) ⊔ I).topologicalClosure := by
    rw [htop]
    exact Submodule.mem_top
  have hTz : Tc z ∈ I.topologicalClosure := by
    refine topologicalClosure_le_topologicalClosure ?_ (apply_mem_topologicalClosure_map Tc _ hz')
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
    have hk' : Tc k = 0 := LinearMap.mem_ker.1 hk
    simp only [ContinuousLinearMap.coe_coe, map_add, hk', zero_add]
    exact I.le_topologicalClosure (hI i hi)
  have hperp : Tc z ∈ Iᗮ := by
    rw [Submodule.mem_orthogonal]
    intro i hi
    have h := hsymm i z
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h]
    exact Submodule.inner_right_of_mem_orthogonal (hI i hi) hz
  exact eq_zero_of_mem_topologicalClosure_of_mem_orthogonal I hTz hperp

private theorem heckeGen_mem_finiteAdelicGL2Subgroup (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : heckeGen (𝓞 K) K v ∈ finiteAdelicGL2Subgroup K := by
  show glArch (𝓞 K) K (heckeGen (𝓞 K) K v) = 1
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  rw [glArch_apply]
  exact heckeGenAt_fst _ i j

private theorem adelicGL2_eq_of_glArch_eq_of_glFin_eq (K : Type) [Field K] [NumberField K] {x y : AdelicGL2 (𝓞 K) K}
    (h₁ : NumberField.AdelicLevel.glArch (𝓞 K) K x = NumberField.AdelicLevel.glArch (𝓞 K) K y)
    (h₂ : NumberField.AdelicLevel.glFin (𝓞 K) K x = NumberField.AdelicLevel.glFin (𝓞 K) K y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j) h₂
  exact Prod.ext h₁' h₂'

private theorem commute_rowIsometryInclAt₀_of_glArch_eq_one (K : Type) [Field K] [NumberField K]
    {g : AdelicGL2 (𝓞 K) K} (hg : NumberField.AdelicLevel.glArch (𝓞 K) K g = 1) (w : InfinitePlace K)
    (k : rowIsometrySubgroup₀ w.Completion) : Commute g (rowIsometryInclAt₀ K w k) := by
  refine (commute_iff_eq _ _).mpr (adelicGL2_eq_of_glArch_eq_of_glFin_eq K ?_ ?_)
  · rw [map_mul, map_mul, hg, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀ K w k, mul_one, one_mul]

private theorem rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ finiteAdelicGL2Subgroup K) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ archCutSubmodule K tys) : CuspidalConstituent.rightTranslate K g φ ∈ archCutSubmodule K tys := by
  have hg₁ : NumberField.AdelicLevel.glArch (𝓞 K) K g = 1 := (mem_finiteAdelicGL2Subgroup_iff K g).mp hg
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have key : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt K w (tys.rep w i)).map (CuspidalConstituent.rightRegular K g)
        ≤ archTypeSubmoduleAt K w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    exact comp_mul_mem_typeSubmodule_of_commute hf₀ g (commute_rowIsometryInclAt₀_of_glArch_eq_one K hg₁ w)
  have hmap : (⨆ i, archTypeSubmoduleAt K w (tys.rep w i)).map (CuspidalConstituent.rightRegular K g)
      ≤ ⨆ i, archTypeSubmoduleAt K w (tys.rep w i) := by
    rw [Submodule.map_iSup]; exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem (hφ w))

private theorem isHeckeCosetSystem_mul_left {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι : Type*} {reps : ι → G} (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) {k : G}
    (hk : k ∈ U) : HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => k * reps i) := by
  constructor
  · intro i
    exact HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hk
  · intro x hx
    obtain ⟨i, hi⟩ := hsys.covers (k⁻¹ * x) (HeckePair.mul_mem_doubleCoset hx (U.inv_mem hk))
    have h : x⁻¹ * (k * reps i) ∈ U := by
      rw [show x⁻¹ * (k * reps i) = (k⁻¹ * x)⁻¹ * reps i by group]
      exact QuotientGroup.eq.mp hi
    exact ⟨i, QuotientGroup.eq.mpr h⟩
  · intro i j hij
    have h : (QuotientGroup.mk (k * reps i) : G ⧸ U) = QuotientGroup.mk (k * reps j) := hij
    have h' : (reps i)⁻¹ * reps j ∈ U := by
      rw [show (reps i)⁻¹ * reps j = (k * reps i)⁻¹ * (k * reps j) by group]
      exact QuotientGroup.eq.mp h
    exact hsys.mk_injective (QuotientGroup.eq.mpr h')

private def archTypeFamilySum {K : Type} [Field K] [NumberField K] (t₁ t₂ : ArchTypeFamily K) : ArchTypeFamily K where
  card := fun w => t₁.card w + t₂.card w
  rep := fun w => Fin.addCases (motive := fun _ => ArchRepAt K w) (t₁.rep w) (t₂.rep w)

private theorem isContainedIn_archTypeFamilySum_left {K : Type} [Field K] [NumberField K] (t₁ t₂ : ArchTypeFamily K) :
    t₁.IsContainedIn K (archTypeFamilySum t₁ t₂) := fun w i =>
  ⟨Fin.castAdd (t₂.card w) i, by simp only [archTypeFamilySum]; exact Fin.addCases_left i⟩

private theorem isContainedIn_archTypeFamilySum_right {K : Type} [Field K] [NumberField K] (t₁ t₂ : ArchTypeFamily K) :
    t₂.IsContainedIn K (archTypeFamilySum t₁ t₂) := fun w i =>
  ⟨Fin.natAdd (t₁.card w) i, by simp only [archTypeFamilySum]; exact Fin.addCases_right i⟩

private theorem exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule {K : Type} [Field K] [NumberField K]
    (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : ψ ∈ CuspidalConstituent.cuspKFiniteSubmodule K pins ξ) :
    ∃ t : ArchTypeFamily K, ψ ∈ archCutSubmodule K t := by
  unfold CuspidalConstituent.cuspKFiniteSubmodule at hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    have hx' : (∀ g : AdelicGL2 (𝓞 K) K,
        IsSmoothCuspAutomorphicFnAt K pins ξ (CuspidalConstituent.rightTranslate K g x)) ∧
        Continuous x ∧ ∃ t : ArchTypeFamily K, x ∈ archCutSubmodule K t := hx
    exact hx'.2.2
  | zero => exact ⟨⟨fun _ => 0, fun _ i => i.elim0⟩, Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨t₁, h₁⟩ := ihx
    obtain ⟨t₂, h₂⟩ := ihy
    exact ⟨archTypeFamilySum t₁ t₂, Submodule.add_mem _
      (archCutSubmodule_mono K (isContainedIn_archTypeFamilySum_left t₁ t₂) h₁)
      (archCutSubmodule_mono K (isContainedIn_archTypeFamilySum_right t₁ t₂) h₂)⟩
  | smul a x _ ih =>
    obtain ⟨t, h⟩ := ih
    exact ⟨t, Submodule.smul_mem _ a h⟩

private theorem isCuspSubrep_fdPins_of_forall_isAutomorphicFnAt {K : Type} [Field K] [NumberField K]
    {Φ : Set (AdelicGL2 (𝓞 K) K)} (D : Set (AdelicGL2 (𝓞 K) K)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (htr : ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ ψ → IsAutomorphicFnAt K (fdPins K Φ) ξ ψ)
    {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hV : CuspidalConstituent.IsCuspSubrep K (productionPinsOf K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ V) :
    CuspidalConstituent.IsCuspSubrep K (fdPins K Φ) ξ V := by
  refine ⟨hV.le.trans ?_, hV.rightTranslate_fin_mem, hV.rightTranslate_arch_mem, hV.rightConv_mem⟩
  unfold CuspidalConstituent.cuspKFiniteSubmodule
  refine Submodule.span_le.2 fun ψ hψ => Submodule.subset_span ?_
  simp only [Set.mem_setOf_eq] at hψ ⊢
  exact ⟨fun g => ⟨⟨htr _ (hψ.1 g).1.1, (hψ.1 g).1.2⟩, (hψ.1 g).2⟩, hψ.2.1, hψ.2.2⟩

private theorem heckeCosetSum_eq_sum_rightTranslate {K : Type} [Field K] [NumberField K] {n : ℕ}
    (reps : Fin n → AdelicGL2 (𝓞 K) K) (x : AdelicGL2 (𝓞 K) K → ℂ) :
    SmoothCusp.heckeCosetSum K reps x = ∑ i, CuspidalConstituent.rightTranslate K (reps i) x := by
  funext g
  show (∑ i, x (g * reps i)) = (∑ i, CuspidalConstituent.rightTranslate K (reps i) x) g
  rw [Finset.sum_apply]
  rfl

open HeckeIntegralSeam in

private theorem toCarrier_mem_topologicalClosure_map_span_range (K : Type) [Field K] [NumberField K] {α β : ℝ}
    {Φ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus K ξ σ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (tys : ArchTypeFamily K)
    (hspan : ∀ (tys' : ArchTypeFamily K) {X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)},
      FiniteDimensional ℂ X →
      (∀ x ∈ X, IsSmoothCuspAutomorphicFnAt K (slabPins K Φ) ξ x ∧ Continuous x ∧
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ (slabPins K Φ).U N, x (g * u) = x g) ∧ x ∈ archCutSubmodule K tys') →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        HeckeIntegralSeam.IsHeckeCosetSystem ((slabPins K Φ).U N) ((slabPins K Φ).gen v) reps →
        ∀ x ∈ X, SmoothCusp.heckeCosetSum K reps x ∈ X) →
      X ≤ ⨆ (π : HeckeEigensystem K ℂ) (_ : π ∈ cuspClasses K (slabPins K Φ) ξ N S),
        isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys')
    {ι : Type} (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (h₄ : ∀ π ∈ cuspClasses K (slabPins K Φ) ξ N S, {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) =
        isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsSmoothCuspAutomorphicFnAt K (slabPins K Φ) ξ φ) (hc : Continuous φ)
    (hU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ (slabPins K Φ).U N, φ (g * u) = φ g) (hT : φ ∈ archCutSubmodule K tys)
    (hφm : φ ∈ memberSubmodule K Φ ξ) :
    toCarrier K hΦ₀ σ ξ ⟨φ, hφm⟩ ∈
      (((Submodule.span ℂ (Set.range b)).comap (memberSubmodule K Φ ξ).subtype).map
        (toCarrier K hΦ₀ σ ξ)).topologicalClosure := by
  haveI : CompleteSpace ↥(cuspSubcarrier K hΦ₀ σ ξ) :=
    Submodule.topologicalClosure.completeSpace (Submodule.map (toCarrier K hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule K Φ ξ).subtype (cuspMemberSubmodule K Φ ξ)))

  obtain ⟨T, c, hc0, u, hcovAll⟩ := SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov := hcovAll 1 2 two_pos one_le_two
  have hφc : φ ∈ cuspMemberSubmodule K Φ ξ :=
    (⟨hφ, hc⟩ : IsSmoothCuspAutomorphicFnAt K (fdPins K Φ) ξ φ ∧ Continuous φ)

  obtain ⟨P, -, -, hPfix, hPcut, -⟩ := exists_idempotent_cutProjector_of_isCompact K hΦ₀ σ ξ hσ
    (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (isCompact_levelOne_inf_finiteAdelicGL2Subgroup K N)
    (levelOne (𝓞 K) K N)
    (isOpen_levelOne (𝓞 K) K hN) rfl tys
  have hPv : P (toCuspSubcarrier K hΦ₀ σ ξ ⟨φ, hφc⟩) = toCuspSubcarrier K hΦ₀ σ ξ ⟨φ, hφc⟩ := hPfix φ hφc hU hT

  set AH : Submodule ℂ ↥(cuspSubcarrier K hΦ₀ σ ξ) :=
    ((Submodule.span ℂ (Set.range b)).comap (cuspMemberSubmodule K Φ ξ).subtype).map (toCuspSubcarrier K hΦ₀ σ ξ)

  have hW₀ : ∀ π ∈ cuspClasses K (slabPins K Φ) ξ N S,
      isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys ≤ Submodule.span ℂ (Set.range b) := by
    intro π hπ
    rw [← (h₄ π hπ).2]
    exact Submodule.span_mono (Set.image_subset_range _ _)

  have hM : ∀ M : Submodule ℂ ↥(cuspSubcarrier K hΦ₀ σ ξ), IsIrreducibleCuspSubrep K hΦ₀ σ ξ M →
      M.map (P : ↥(cuspSubcarrier K hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier K hΦ₀ σ ξ)) ≤ AH.topologicalClosure := by
    intro M hMirr
    obtain ⟨V, hVc, hVmem⟩ := exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep K
      c u 1 2 T hc0 one_pos one_lt_two hcov ξ σ hσ hΦ₀ M hMirr
    have hVslab : CuspidalConstituent.IsCuspSubrep K (fdPins K Φ) ξ V :=
      isCuspSubrep_fdPins_of_forall_isAutomorphicFnAt _ ξ (fun ψ hψ =>
        isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre K c u 1 2 T one_lt_two hcov
          α β hΦ₀.pos Φ hΦ₀.subset hΦ₀.isFundamentalDomain ξ ψ hψ) hVc.1

    have hC := isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep K hΦ₀ σ ξ V hVslab
    have hCle : (Submodule.map (toCuspSubcarrier K hΦ₀ σ ξ)
        (Submodule.comap (cuspMemberSubmodule K Φ ξ).subtype V)).topologicalClosure ≤ M := by
      refine Submodule.topologicalClosure_minimal _ ?_ hMirr.1.isClosed
      rintro _ ⟨ψ, hψV, rfl⟩
      obtain ⟨-, h, hmem⟩ := (hVmem ψ).1 hψV
      exact hmem
    have hCne : (Submodule.map (toCuspSubcarrier K hΦ₀ σ ξ)
        (Submodule.comap (cuspMemberSubmodule K Φ ξ).subtype V)).topologicalClosure ≠ ⊥ := by
      obtain ⟨ψ, hψ0, hψK, hψm, hψM⟩ :=
        exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot K c u 1 2 T hc0
          one_pos one_lt_two hcov ξ σ hσ hΦ₀ M hMirr.1 hMirr.2.1
      intro hbot
      have hin : toCuspSubcarrier K hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ (Submodule.map (toCuspSubcarrier K hΦ₀ σ ξ)
          (Submodule.comap (cuspMemberSubmodule K Φ ξ).subtype V)).topologicalClosure :=
        Submodule.le_topologicalClosure _
          (Submodule.mem_map_of_mem (f := toCuspSubcarrier K hΦ₀ σ ξ)
            (show (⟨ψ, hψm⟩ : ↥(cuspMemberSubmodule K Φ ξ)) ∈
                Submodule.comap (cuspMemberSubmodule K Φ ξ).subtype V from
              (hVmem ψ).2 ⟨hψK, hψm, hψM⟩))
      rw [hbot, Submodule.mem_bot] at hin
      exact hψ0 (eq_zero_of_toCarrier_eq_zero K hΦ₀ σ ξ ψ ⟨hψm.1.1.1, hψm.2⟩ (congrArg Subtype.val hin))
    have hCeq : (Submodule.map (toCuspSubcarrier K hΦ₀ σ ξ)
        (Submodule.comap (cuspMemberSubmodule K Φ ξ).subtype V)).topologicalClosure = M := by
      rcases hMirr.2.2 _ hC hCle with h | h
      · exact absurd h hCne
      · exact h

    have hfinX := finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent K c u 1 2 T
      one_lt_two hcov ξ N hN tys V hVc
    have hKle := cuspKFiniteSubmodule_le_cuspMemberSubmodule K c u 1 2 T hc0 one_pos one_lt_two hcov ξ hΦ₀
    have hXle := hspan tys hfinX (fun x hx => by
        obtain ⟨hxVU, hxT⟩ := Submodule.mem_inf.1 hx
        obtain ⟨hxV, hxU⟩ := Submodule.mem_inf.1 hxVU
        have hxm : x ∈ cuspMemberSubmodule K Φ ξ := hKle (hVc.1.le hxV)
        exact ⟨hxm.1, hxm.2, hxU, hxT⟩)
      (fun v hv reps hreps x hx => by
        obtain ⟨hxVU, hxT⟩ := Submodule.mem_inf.1 hx
        obtain ⟨hxV, hxU⟩ := Submodule.mem_inf.1 hxVU
        refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
        · rw [heckeCosetSum_eq_sum_rightTranslate]
          refine Submodule.sum_mem _ fun i _ => hVc.1.rightTranslate_fin_mem _ ?_ x hxV
          obtain ⟨u₁, hu₁, u₂, hu₂, hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hreps.mem_doubleCoset i)
          rw [← hrep]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.1 hu₁).2
            (heckeGen_mem_finiteAdelicGL2Subgroup K v)) (Subgroup.mem_inf.1 hu₂).2
        · have hxU' : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
              x (g * u) = x g := hxU
          show ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
            SmoothCusp.heckeCosetSum K reps x (g * k) = SmoothCusp.heckeCosetSum K reps x g
          intro g k hk
          show ∑ i, x (g * k * reps i) = ∑ i, x (g * reps i)
          simp_rw [mul_assoc]
          exact Venue.cosetSum_eq_of_isHeckeCosetSystem (isHeckeCosetSystem_mul_left hreps hk) hreps x hxU' g
        · rw [heckeCosetSum_eq_sum_rightTranslate]
          refine Submodule.sum_mem _ fun i _ => rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic K tys ?_ hxT
          obtain ⟨u₁, hu₁, u₂, hu₂, hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hreps.mem_doubleCoset i)
          rw [← hrep]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.1 hu₁).2
            (heckeGen_mem_finiteAdelicGL2Subgroup K v)) (Subgroup.mem_inf.1 hu₂).2)

    rintro _ ⟨m, hm, rfl⟩
    rw [← hCeq] at hm
    refine topologicalClosure_le_topologicalClosure ?_ (apply_mem_topologicalClosure_map P _ hm)
    rintro _ ⟨_, ⟨ψ, hψV, rfl⟩, rfl⟩
    obtain ⟨t, ht⟩ := exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule _ _ ((hVmem ψ).1 hψV).1
    obtain ⟨ψ', hψ'm, hψ'U, hψ'T, hψ'V, hPψ⟩ := hPcut ψ ψ.2 ⟨t, ht⟩
    have hψ'V' : ψ' ∈ V := hψ'V V hVc.1.rightTranslate_fin_mem hVc.1.rightTranslate_arch_mem hψV
    have hψ'W : ψ' ∈ Submodule.span ℂ (Set.range b) :=
      (iSup₂_le fun π hπ => hW₀ π hπ) (hXle (Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hψ'V', hψ'U⟩, hψ'T⟩))
    have hPψ' : P (toCuspSubcarrier K hΦ₀ σ ξ ψ) = toCuspSubcarrier K hΦ₀ σ ξ ⟨ψ', hψ'm⟩ := hPψ
    simp only [ContinuousLinearMap.coe_coe]
    rw [hPψ']
    exact AH.le_topologicalClosure (Submodule.mem_map_of_mem (f := toCuspSubcarrier K hΦ₀ σ ξ)
      (show (⟨ψ', hψ'm⟩ : ↥(cuspMemberSubmodule K Φ ξ)) ∈
        (Submodule.span ℂ (Set.range b)).comap (cuspMemberSubmodule K Φ ξ).subtype from hψ'W))

  set I : Submodule ℂ ↥(cuspSubcarrier K hΦ₀ σ ξ) :=
    ⨆ (M : Submodule ℂ ↥(cuspSubcarrier K hΦ₀ σ ξ)) (_ : IsIrreducibleCuspSubrep K hΦ₀ σ ξ M), M
  have hIperp : Iᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    by_contra hz0
    obtain ⟨tys', f, hf, hft, -, Tc, hcpt, hsymm, hTc, hTz⟩ :=
      exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero K hΦ₀ σ ξ hσ z hz0
    refine hTz (apply_eq_zero_of_mem_orthogonal_of_forall_eigenspace_le Tc hcpt hsymm I ?_ ?_ hz)
    · intro x hx
      refine (iSup₂_le fun M hMirr => ?_ :
        I ≤ I.comap (Tc : ↥(cuspSubcarrier K hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier K hΦ₀ σ ξ))) hx
      intro m hm
      exact le_iSup₂ (f := fun (M : Submodule ℂ ↥(cuspSubcarrier K hΦ₀ σ ξ))
          (_ : IsIrreducibleCuspSubrep K hΦ₀ σ ξ M) => M) M hMirr
        (hMirr.1.map_le_of_rightConv f tys' hf hft Tc hTc (Submodule.mem_map_of_mem hm))
    · intro μ hμ w hw
      rw [Module.End.mem_eigenspace_iff] at hw
      obtain ⟨n, Ms, vs, hMs, -, hvs, hwsum⟩ :=
        exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul K hΦ₀ σ ξ hσ f hf tys' hft Tc hTc hcpt μ hμ
          w hw
      rw [hwsum]
      exact Submodule.sum_mem _ fun i _ =>
        le_iSup₂ (f := fun (M : Submodule ℂ ↥(cuspSubcarrier K hΦ₀ σ ξ))
          (_ : IsIrreducibleCuspSubrep K hΦ₀ σ ξ M) => M) (Ms i) (hMs i) (hvs i).1
  have hvI : toCuspSubcarrier K hΦ₀ σ ξ ⟨φ, hφc⟩ ∈ I.topologicalClosure := by
    rw [Submodule.topologicalClosure_eq_top_iff.2 hIperp]
    exact Submodule.mem_top
  have hPI : I.map (P : ↥(cuspSubcarrier K hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier K hΦ₀ σ ξ)) ≤ AH.topologicalClosure :=
    Submodule.map_le_iff_le_comap.2 (iSup₂_le fun M hMirr => Submodule.map_le_iff_le_comap.1 (hM M hMirr))
  have hfin : P (toCuspSubcarrier K hΦ₀ σ ξ ⟨φ, hφc⟩) ∈ AH.topologicalClosure :=
    topologicalClosure_le_topologicalClosure hPI (apply_mem_topologicalClosure_map P I hvI)
  rw [hPv] at hfin

  have hcoe := apply_mem_topologicalClosure_map (cuspSubcarrier K hΦ₀ σ ξ).subtypeL AH hfin
  have hsub : AH.map ((cuspSubcarrier K hΦ₀ σ ξ).subtypeL : ↥(cuspSubcarrier K hΦ₀ σ ξ) →ₗ[ℂ] Carrier K Φ σ) ≤
      (((Submodule.span ℂ (Set.range b)).comap (memberSubmodule K Φ ξ).subtype).map
        (toCarrier K hΦ₀ σ ξ)).topologicalClosure := by
    rintro _ ⟨_, ⟨ψ, hψW, rfl⟩, rfl⟩
    refine Submodule.le_topologicalClosure _ ?_
    simp only [ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, toCuspSubcarrier_apply_coe]
    exact Submodule.mem_map_of_mem (f := toCarrier K hΦ₀ σ ξ)
      (show (⟨(ψ : AdelicGL2 (𝓞 K) K → ℂ), ψ.2.1.1.1⟩ : ↥(memberSubmodule K Φ ξ)) ∈
        (Submodule.span ℂ (Set.range b)).comap (memberSubmodule K Φ ξ).subtype from hψW)
  exact topologicalClosure_le_topologicalClosure hsub hcoe

private theorem ae_eq_zero_of_forall_integral_mul_conj_eq_zero_of_span_isotypicCuspSubmodule_levelOne
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (h₁ :
      (∀ i, cls i ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S ∧
        b i ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys))
    (h₄ :
      (∀ π ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S,
        {i | cls i = π}.Finite ∧
        Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys)) :
      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
        IsSmoothCuspAutomorphicFnAt K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ φ →
        Continuous φ →
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
          (productionPinsOf K Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tys →
        (∀ i, ∫ g in Φ, φ g * starRingEnd ℂ (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0) := by
  intro φ hφ hc hU hT hperp
  by_cases h0 : φ = 0
  · subst h0
    exact Filter.EventuallyEq.rfl
  have hΦ₀ : IsSlabFundamentalDomain K α β Φ := isSlabFundamentalDomain_of_binders hα hαβ hΦs hΦ
  obtain ⟨σ, hσ⟩ := exists_hasModulus_of_isAutomorphicFnAt_of_continuous K Φ ξ φ hφ.1.1 hc h0
  have hφc : φ ∈ contMemberSubmodule K Φ ξ := ⟨(mem_memberSubmodule_iff K Φ ξ φ).2 hφ.1.1, hc⟩
  have hW : Submodule.span ℂ (Set.range b) ≤ contMemberSubmodule K Φ ξ :=
    span_range_le_contMemberSubmodule ξ N S tys b cls h₁
  have hperp' : ∀ i, slabPairing K Φ φ (b i) = 0 := hperp
  have hk : 0 < (min (α ^ (-σ)) (β ^ (-σ))) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans hαβ) _)) _
  have hC := toCarrier_mem_topologicalClosure_map_span_range K hΦ₀ ξ σ hσ N hN S tys
    (fun tys' {X} hfin hX hstab =>
      le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
        K α β hΦ₀.pos hΦ₀.lt Φ hΦ₀.subset hΦ₀.isFundamentalDomain ξ N hN S hNS tys' X hX hfin hstab)
    b cls h₄ φ hφ hc hU hT hφc.1
  have hC₀ := mem_topologicalClosure_map_of_forall_mul_norm_le (toCarrier K hΦ₀ 0 ξ) (toCarrier K hΦ₀ σ ξ) hk
    (rpow_mul_norm_toCarrier_zero_le K hΦ₀ σ ξ) _ hC
  have hzero : toCarrier K hΦ₀ 0 ξ ⟨φ, hφc.1⟩ = 0 := by
    refine eq_zero_of_mem_topologicalClosure_of_mem_orthogonal _ hC₀ ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨y, hyW, rfl⟩ := Submodule.mem_map.1 hu
    have hy : (y : AdelicGL2 (𝓞 K) K → ℂ) ∈ Submodule.span ℂ (Set.range b) := hyW
    rw [← slabPairing_eq_inner_toCarrier_zero K hΦ₀ ξ ⟨φ, hφc.1⟩ y]
    exact slabPairing_eq_zero_of_mem_span_range hφc hW hperp' hy
  have h2 : (memLp_weightedMeasure_of_mem K hΦ₀ 0 hφc.1).toLp φ = 0 := hzero
  rw [Lp.eq_zero_iff_ae_eq_zero] at h2
  have hae : φ =ᵐ[weightedMeasure K Φ 0] 0 := (MemLp.coeFn_toLp _).symm.trans h2
  rwa [weightedMeasure_zero_eq] at hae

end SlabOrthogonality

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K) :
    ∃ (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ),
      (∀ i, cls i ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S ∧
        b i ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys) ∧
      (∀ i, ∫ g in Φ, b i g * starRingEnd ℂ (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) ∧
      (∀ i j, i ≠ j → ∫ g in Φ, b i g * starRingEnd ℂ (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) ∧
      (∀ π ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S,
        {i | cls i = π}.Finite ∧
        Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys) ∧
      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
        IsSmoothCuspAutomorphicFnAt K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ φ →
        Continuous φ →
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
          (productionPinsOf K Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tys →
        (∀ i, ∫ g in Φ, φ g * starRingEnd ℂ (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0) := by
  have hΦ₀ : IsSlabFundamentalDomain K α β Φ := isSlabFundamentalDomain_of_binders hα hαβ hΦs hΦ

  have hpiece : ∀ π : HeckeEigensystem K ℂ, ∃ (m : ℕ) (c : Fin m → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ k, c k ∈ isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys) ∧
      (∀ k l, slabPairing K Φ (c k) (c l) = if l = k then 1 else 0) ∧
      Submodule.span ℂ (Set.range c) =
        isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys := by
    intro π
    haveI : FiniteDimensional ℂ ↥(isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys) :=
      finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain K α β hα hαβ Φ hΦs hΦ ξ N
        hN S tys π
    exact exists_finite_orthonormal_spanning_family hΦ₀ ξ N S tys π
  choose m c hmem horth hspan using hpiece

  refine ⟨(Σ p : ↥(cuspClasses K (slabPins K Φ) ξ N S), Fin (m p.1)), fun i => c i.1.1 i.2, fun i => i.1.1,
    fun i => ⟨i.1.2, hmem i.1.1 i.2⟩, fun i => ?_, fun i j hij => ?_, fun π hπ => ⟨fibre_finite m hπ, ?_⟩, ?_⟩
  · have h := horth i.1.1 i.2 i.2
    rw [if_pos rfl] at h
    exact h
  · obtain ⟨p, k⟩ := i
    obtain ⟨q, l⟩ := j
    by_cases hpq : p = q
    · subst q
      have hlk : l ≠ k := by
        rintro rfl
        exact hij rfl
      have h := horth p.1 k l
      rw [if_neg hlk] at h
      exact h
    · exact integral_mul_conj_eq_zero_of_ne_of_mem_cuspClasses hα hαβ hΦs hΦ ξ N hN S hNS p.2 q.2
        (fun h => hpq (Subtype.ext h)) (hmem p.1 k).1 (hmem q.1 l).1
  · have h := hspan π
    rw [← image_fibre_eq m c hπ] at h
    exact h

  · refine ae_eq_zero_of_forall_integral_mul_conj_eq_zero_of_span_isotypicCuspSubmodule_levelOne K α β hα hαβ Φ hΦs hΦ
      ξ N hN S hNS tys (Σ p : ↥(cuspClasses K (slabPins K Φ) ξ N S), Fin (m p.1)) (fun i => c i.1.1 i.2)
      (fun i => i.1.1) (fun i => ⟨i.1.2, hmem i.1.1 i.2⟩) fun π hπ => ⟨fibre_finite m hπ, ?_⟩
    have h := hspan π
    rw [← image_fibre_eq m c hπ] at h
    exact h

end

end S_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab (solution)
