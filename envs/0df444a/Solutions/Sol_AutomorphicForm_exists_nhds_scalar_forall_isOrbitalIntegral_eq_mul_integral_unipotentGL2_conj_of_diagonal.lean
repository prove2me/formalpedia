-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f9cd8944-f54a-53f0-b06c-35b6b45721f6

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
import Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk"
p2m_attr_erase "simp" "FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft"
p2m_attr_erase "simp" "LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter
open scoped Topology

noncomputable section

namespace P2mSplitGermScalar

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

theorem scalar_mul_comm {F : Type*} [Field F] (c : Fˣ) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (c : F) (fun r' => Commute.all _ _) _).eq

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.localCentralizerBorel

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

theorem main (c : (v.adicCompletion K)ˣ)
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : IsLocalTestFn K v f) :
    ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ W, (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
        (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 → IsRegularSemisimple γ →
        ∀ (τ : Measure (localCentralizer K v γ)), τ.IsHaarMeasure →
          ∀ I : ℂ, IsOrbitalIntegral K v γ τ f I →
            I = (((τ {t : localCentralizer K v γ |
                      (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v}).toReal⁻¹ *
                  (ν (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal⁻¹ *
                  ‖1 - (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
                      (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖⁻¹ : ℝ) : ℂ) *
              ∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
                 (∫ u, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                   (k⁻¹ * unipotentGL2 u * k)) ∂ν) ∂(localHaar K v) := by

  generalize hz : Matrix.GeneralLinearGroup.scalar (Fin 2) c = z
  have hzc : ∀ g : GL (Fin 2) (v.adicCompletion K), z * g = g * z := fun g => by
    rw [← hz]; exact scalar_mul_comm c g

  obtain ⟨V, hV1, hV⟩ := hf.1.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hf.2

  have hD : ∀ᶠ d in 𝓝 (1 : GL (Fin 2) (v.adicCompletion K)), ∀ k ∈ localIntegralSet K v, k⁻¹ * d * k ∈ V := by
    refine (isCompact_localIntegralSet K v).eventually_forall_of_forall_eventually fun k _ => ?_
    have hcont : Continuous fun p : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) =>
        p.2⁻¹ * p.1 * p.2 := (continuous_snd.inv.mul continuous_fst).mul continuous_snd
    have hV' : V ∈ 𝓝 ((fun p : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) =>
        p.2⁻¹ * p.1 * p.2) (1, k)) := by
      simpa using hV1
    exact (hcont.tendsto (1, k)).eventually_mem hV'
  obtain ⟨D, hD1, hDV⟩ : ∃ D ∈ 𝓝 (1 : GL (Fin 2) (v.adicCompletion K)),
      ∀ d ∈ D, ∀ k ∈ localIntegralSet K v, k⁻¹ * d * k ∈ V :=
    ⟨_, hD, fun d hd => hd⟩

  refine ⟨(fun g => z⁻¹ * g) ⁻¹' D, ?_, ?_⟩
  · have hcont : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => z⁻¹ * g := continuous_const.mul continuous_id
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using hD1
  intro γ hγW hγ₀₁ hγ₁₀ hreg τ hτ I hI

  have hdesc :=
    AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
      K v γ hreg hγ₀₁ hγ₁₀ τ hτ ν f hf I hI
  rw [hdesc]
  congr 1

  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  dsimp only
  by_cases hk : k ∈ localIntegralSet K v
  · congr 1
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    have hd : z⁻¹ * γ ∈ D := hγW
    have hkd : k⁻¹ * (z⁻¹ * γ) * k ∈ V := hDV _ hd k hk
    have e1 : k⁻¹ * (γ * unipotentGL2 u) * k = (k⁻¹ * (z⁻¹ * γ) * k) * (z * (k⁻¹ * unipotentGL2 u * k)) * 1 := by
      calc k⁻¹ * (γ * unipotentGL2 u) * k
          = k⁻¹ * z⁻¹ * (z * γ) * unipotentGL2 u * k := by group
        _ = k⁻¹ * z⁻¹ * (γ * z) * unipotentGL2 u * k := by rw [hzc γ]
        _ = k⁻¹ * (z⁻¹ * γ) * (z * k) * k⁻¹ * unipotentGL2 u * k := by group
        _ = k⁻¹ * (z⁻¹ * γ) * (k * z) * k⁻¹ * unipotentGL2 u * k := by rw [hzc k]
        _ = (k⁻¹ * (z⁻¹ * γ) * k) * (z * (k⁻¹ * unipotentGL2 u * k)) * 1 := by group
    change f (k⁻¹ * (γ * unipotentGL2 u) * k) = f (z * (k⁻¹ * unipotentGL2 u * k))
    rw [e1]
    exact hV _ hkd 1 (mem_of_mem_nhds hV1) _
  · rw [Set.indicator_of_notMem hk, zero_mul, zero_mul]

end P2mSplitGermScalar

end

open MeasureTheory NumberField
open IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f) :
    ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ W, (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
        (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 → AutomorphicForm.IsRegularSemisimple γ →
        ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
          @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
            I = (((τ {t : AutomorphicForm.localCentralizer K v γ |
                      (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal⁻¹ *
                  (ν (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal⁻¹ *
                  ‖1 - (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
                      (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖⁻¹ : ℝ) : ℂ) *
              (letI := AutomorphicForm.localGLBorel K v
               ∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
                 (∫ u, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                   (k⁻¹ * AutomorphicForm.unipotentGL2 u * k)) ∂ν) ∂(AutomorphicForm.localHaar K v)) :=
  P2mSplitGermScalar.main K v c ν f hf

end S_AutomorphicForm_exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal (solution)
