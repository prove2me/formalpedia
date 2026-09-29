-- Prove2me | solution 1 for AutomorphicForm.eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/62d016f7-feb0-55f5-bd2a-1d2cae2649a6

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk"
p2m_attr_erase "simp" "FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft"
p2m_attr_erase "simp" "LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (g g' : GL (Fin 2) (v.adicCompletion K)) (hg : AutomorphicForm.IsRegularSemisimple g)
    (hg₀₁ : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (hg₁₀ : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (ε : v.adicCompletion K) (hε : Valued.v ε = 1)
    (hg' : (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ε • (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (τ : @Measure (AutomorphicForm.localCentralizer K v g) (AutomorphicForm.localCentralizerBorel K v g))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v g) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (τ' : @Measure (AutomorphicForm.localCentralizer K v g') (AutomorphicForm.localCentralizerBorel K v g'))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v g') τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hcen : ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), f (c * y) = f y)
    (I I' : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v g τ f I)
    (hI' : AutomorphicForm.IsOrbitalIntegral K v g' τ' f I') :
    I' = I := by
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, map_zero] at hε; exact zero_ne_one hε
  have hg'e : ∀ i j, (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      ε * (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := fun i j => by
    rw [hg', Matrix.smul_apply, smul_eq_mul]
  have hg'₀₁ : (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by
    rw [hg'e, hg₀₁, mul_zero]
  have hg'₁₀ : (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
    rw [hg'e, hg₁₀, mul_zero]
  have hg'r : AutomorphicForm.IsRegularSemisimple g' := by
    unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
    have h : Matrix.trace (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        ε ^ 2 * (Matrix.trace (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
          4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
      rw [hg', Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]
      ring
    rw [h]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hε0)).mul hg
  letI mK : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  have h1 := AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
    K v g hg hg₀₁ hg₁₀ τ hτ (Measure.addHaar) f hf I hI
  have h2 := AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
    K v g' hg'r hg'₀₁ hg'₁₀ τ' hτ' (Measure.addHaar) f hf I' hI'
  have hτe : τ {t : AutomorphicForm.localCentralizer K v g |
      (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 := hτ1
  have hτ'e : τ' {t : AutomorphicForm.localCentralizer K v g' |
      (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 := hτ'1
  have hratio : (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
      (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 := by
    rw [hg'e, hg'e, mul_div_mul_left _ _ hε0]
  have hint : ∀ (k : GL (Fin 2) (v.adicCompletion K)) (u : v.adicCompletion K),
      f (k⁻¹ * (g' * AutomorphicForm.unipotentGL2 u) * k) =
        f (k⁻¹ * (g * AutomorphicForm.unipotentGL2 u) * k) := by
    intro k u
    set y : GL (Fin 2) (v.adicCompletion K) := k⁻¹ * (g * AutomorphicForm.unipotentGL2 u) * k with hy
    have hmat : ((k⁻¹ * (g' * AutomorphicForm.unipotentGL2 u) * k : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      rw [hy, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hg',
        Matrix.smul_mul ε, Matrix.mul_smul _ ε, Matrix.smul_mul ε]
    have key : k⁻¹ * (g' * AutomorphicForm.unipotentGL2 u) * k =
        (k⁻¹ * (g' * AutomorphicForm.unipotentGL2 u) * k * y⁻¹) * y := by
      rw [inv_mul_cancel_right]
    rw [key]
    refine hcen _ ⟨ε, hε, ?_⟩ y
    rw [Units.val_mul, hmat, smul_mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [h2, h1, hτe, hτ'e, hratio]
  simp_rw [hint]

end S_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul
end P2MW
export P2MW.S_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul (solution)
