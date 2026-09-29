-- Prove2me | solution 1 for AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d381ca62-cfa6-54dc-9730-1464a8411e92

import Theorems.Thm_AutomorphicForm_exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
import Theorems.Thm_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions"
p2m_attr_erase "instance" "instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk"
p2m_attr_erase "simp" "Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

noncomputable section

namespace R3G3Red

open MeasureTheory NumberField NumberField.AdelicHaar Filter Function Set
open scoped ENNReal NNReal Topology Pointwise

section Instances

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_mulOpposite {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

theorem secondCountableTopology_units {M : Type*} [TopologicalSpace M] [Monoid M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := secondCountableTopology_mulOpposite
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  exact secondCountableTopology_units

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

end Instances

section Modulus

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem ideleNorm_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) =
      NumberField.TateGlobal.ideleNorm L z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph
  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne
  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* _) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b
  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl
  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s
    exact θ.apply_symm_apply _
  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1
  have hcancel : distribHaarChar (AdeleRing (𝓞 L) L) w = distribHaarChar (AdeleRing (𝓞 L) L) z := by
    have := congrArg (fun t => t / μ s) h1
    beta_reduce at this
    rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this
  unfold NumberField.TateGlobal.ideleNorm
  rw [hw] at hcancel
  exact_mod_cast congrArg (fun t : ℝ≥0 => (t : ℝ)) hcancel

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

abbrev actU : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem det_sigmaAdelicAct (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.sigmaAdelicAct K L D σ y) =
      actU K L D σ (Matrix.GeneralLinearGroup.det y) :=
  Matrix.GeneralLinearGroup.map_det _ y

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z ^ 2 := by
  have h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      z ^ Fintype.card (Fin 2) := Matrix.GeneralLinearGroup.det_scalar z
  rw [Fintype.card_fin] at h
  exact h

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm L 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := L) 1).ne' (h.symm.trans (mul_one _).symm)

theorem ideleNorm_inv (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := L) u u⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem ideleNorm_pow_two (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (u ^ 2) = NumberField.TateGlobal.ideleNorm L u ^ 2 := by
  rw [pow_two, pow_two, NumberField.TateGlobal.ideleNorm_mul]

theorem ideleNorm_det_kernelArg (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) =
      NumberField.TateGlobal.ideleNorm L z ^ 2 := by
  rw [map_mul, map_mul, map_inv, det_sigmaAdelicAct, map_mul, det_centralScalar, map_mul, map_pow,
    NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, AutomorphicForm.ideleNorm_det_globalPoints,
    ideleNorm_pow_two, ideleNorm_unitsMap_act, ideleNorm_unitsMap_act, mul_one]
  have hx : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) ≠ 0 :=
    (NumberField.TateGlobal.ideleNorm_pos (F := L) _).ne'
  field_simp

end Modulus

section Lift

variable (L : Type) [Field L] [NumberField L]

theorem mem_Icc_sqrt_of_sq_mem_Icc {t m₀ M₀ : ℝ} (ht : 0 ≤ t) (h : t ^ 2 ∈ Set.Icc m₀ M₀) :
    t ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
  ⟨by rw [← Real.sqrt_sq ht]; exact Real.sqrt_le_sqrt h.1,
    (Real.le_sqrt ht (le_trans (sq_nonneg t) h.2)).mpr h.2⟩

theorem exists_isCompact_forall_mem_exists_princ_mul {m₁ M₁ : ℝ} (hm₁ : 0 < m₁) :
    ∃ C : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact C ∧
      ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc m₁ M₁ →
        ∃ (a : Lˣ) (c : (AdeleRing (𝓞 L) L)ˣ), c ∈ C ∧
          z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a * c := by
  obtain ⟨C₁, hC₁c, -, hC₁⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
  obtain ⟨s, hs_cont, hs_norm, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L
  set S₁ : Set ℝ≥0ˣ := {r | ((r : ℝ≥0) : ℝ) ∈ Set.Icc m₁ M₁} with hS₁
  have hS₁c : IsCompact S₁ := by
    set a₀ : ℝ≥0 := ⟨m₁, hm₁.le⟩ with ha₀
    set b₀ : ℝ≥0 := Real.toNNReal M₁ with hb₀
    have ha₀pos : 0 < a₀ := hm₁
    have hpre : IsCompact (Units.embedProduct ℝ≥0 ⁻¹'
        (Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹))) :=
      Units.isClosedEmbedding_embedProduct.isCompact_preimage
        (isCompact_Icc.prod (isCompact_Icc.image MulOpposite.continuous_op))
    refine hpre.of_isClosed_subset (isClosed_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val)) ?_
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrpos : 0 < (r : ℝ≥0) := lt_of_lt_of_le ha₀pos hr1
    have h1 : a₀ ≤ (r : ℝ≥0) := hr1
    have h2 : (r : ℝ≥0) ≤ b₀ := (Real.le_toNNReal_iff_coe_le (le_trans (le_trans hm₁.le hr1) hr2)).mpr hr2
    show ((r : ℝ≥0), MulOpposite.op ((r⁻¹ : ℝ≥0ˣ) : ℝ≥0)) ∈
      Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹)
    refine Set.mk_mem_prod ⟨h1, h2⟩ ⟨(r : ℝ≥0)⁻¹, ⟨inv_anti₀ hrpos h2, inv_anti₀ ha₀pos h1⟩, ?_⟩
    rw [Units.val_inv_eq_inv_val]
  refine ⟨C₁ * s '' S₁, hC₁c.mul (hS₁c.image hs_cont), fun z hz => ?_⟩
  have hzpos : 0 < NumberField.TateGlobal.ideleNorm L z := NumberField.TateGlobal.ideleNorm_pos (F := L) z
  set r : ℝ≥0ˣ := Units.mk0 (⟨NumberField.TateGlobal.ideleNorm L z, hzpos.le⟩ : ℝ≥0)
    (fun h => hzpos.ne' (congrArg Subtype.val h)) with hr
  have hrS : r ∈ S₁ := hz
  have hsr : NumberField.TateGlobal.ideleNorm L (s r) = NumberField.TateGlobal.ideleNorm L z := hs_norm r
  have hz₁ : z * (s r)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, hsr,
      mul_inv_cancel₀ hzpos.ne']
  obtain ⟨η, κ, hκ, hzκ⟩ := hC₁ _ hz₁
  refine ⟨η, κ * s r, Set.mul_mem_mul hκ ⟨r, hrS, rfl⟩, ?_⟩
  rw [← mul_assoc]
  exact mul_inv_eq_iff_eq_mul.mp hzκ

end Lift

section Measures

variable (L : Type) [Field L] [NumberField L]

theorem measure_inter_le_of_isFundamentalDomain
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Ω νZ)
    (C S : Set (AdeleRing (𝓞 L) L)ˣ)
    (hS : ∀ z ∈ S, ∃ (a : Lˣ) (c : (AdeleRing (𝓞 L) L)ˣ), c ∈ C ∧
      z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a * c) :
    νZ (Ω ∩ S) ≤ νZ C := by
  set P : Subgroup (AdeleRing (𝓞 L) L)ˣ :=
    (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range with hP
  haveI : Countable Lˣ := countable_units L
  haveI : Countable P := by
    have hsurj : Function.Surjective
        ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).rangeRestrict) :=
      MonoidHom.rangeRestrict_surjective _
    exact hsurj.countable
  have h := hΩ.measure_eq_tsum C
  calc νZ (Ω ∩ S) ≤ νZ (⋃ g : P, (g • C ∩ Ω)) := by
        refine measure_mono ?_
        rintro z ⟨hzΩ, hzS⟩
        obtain ⟨a, c, hc, rfl⟩ := hS z hzS
        refine Set.mem_iUnion.mpr ⟨⟨_, ⟨a, rfl⟩⟩, ?_, hzΩ⟩
        exact Set.mem_smul_set.mpr ⟨c, hc, rfl⟩
    _ ≤ ∑' g : P, νZ (g • C ∩ Ω) := measure_iUnion_le _
    _ = νZ C := h.symm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_adelicGL2

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L :
      (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; simpa [Matrix.scalar_apply] using continuous_id'
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

theorem measure_setOf_ideleNorm_det_eq_eq_zero {α : ℝ} (hα : 0 < α) :
    adelicGLHaar (Fin 2) (𝓞 L) L
      {g : AutomorphicForm.AdelicGL2 (𝓞 L) L |
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) = α} = 0 := by
  haveI : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := inferInstance
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set Nd : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ := fun g =>
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) with hNd
  have hNdc : Continuous Nd := NumberField.TateGlobal.continuous_ideleNorm_det L
  set As : ℝ → Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := fun t => {g | Nd g = Real.exp t * α} with hAs
  have hmeas : ∀ t, MeasurableSet (As t) := fun t =>
    (isClosed_eq hNdc continuous_const).measurableSet
  have hdisj : Pairwise (Disjoint on As) := by
    intro t t' htt'
    refine Set.disjoint_left.mpr fun g hg hg' => htt' ?_
    have h1 : Nd g = Real.exp t * α := hg
    have h2 : Nd g = Real.exp t' * α := hg'
    have h3 : Real.exp t = Real.exp t' := mul_right_cancel₀ hα.ne' (h1.symm.trans h2)
    exact Real.exp_injective h3
  obtain ⟨s, -, hs_norm, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L

  have hall : ∀ t, μ (As t) = μ (As 0) := by
    intro t
    have hexp : 0 < Real.exp (t / 2) := Real.exp_pos _
    set r : ℝ≥0ˣ := Units.mk0 (⟨Real.exp (t / 2), hexp.le⟩ : ℝ≥0)
      (fun h => hexp.ne' (congrArg Subtype.val h)) with hr
    set c := AutomorphicForm.centralScalar (𝓞 L) L (s r) with hc
    have hsr : NumberField.TateGlobal.ideleNorm L (s r) = Real.exp (t / 2) := hs_norm r
    have hpre : (fun g => c * g) ⁻¹' (As t) = As 0 := by
      ext g
      simp only [Set.mem_preimage, hAs, Set.mem_setOf_eq, hNd, hc, map_mul, det_centralScalar,
        NumberField.TateGlobal.ideleNorm_mul, ideleNorm_pow_two, hsr, Real.exp_zero, one_mul]
      have hexp2 : Real.exp (t / 2) ^ 2 = Real.exp t := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [hexp2]
      constructor
      · intro h
        exact mul_left_cancel₀ (Real.exp_pos t).ne' (by rw [h])
      · intro h; rw [h]
    rw [← hpre]
    exact (measure_preimage_mul μ c (As t)).symm

  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hmeas hdisj
  have hzero : μ (As 0) = 0 := by
    by_contra hne
    have hpos : 0 < μ (As 0) := pos_iff_ne_zero.mpr hne
    have huniv : {t : ℝ | 0 < μ (As t)} = Set.univ := Set.eq_univ_of_forall fun t => by
      show 0 < μ (As t); rw [hall t]; exact hpos
    rw [huniv] at hcount
    exact Set.not_countable_univ hcount
  have hset : {g : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) = α} = As 0 := by
    ext g; simp [hAs, hNd]
  rw [hset]; exact hzero

theorem measure_lt_top_of_isFundamentalDomain (α β : ℝ) (hα : 0 < α)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    adelicGLHaar (Fin 2) (𝓞 L) L Φ < ⊤ := by
  rcases lt_trichotomy α β with hlt | heq | hgt
  · have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      L α β hα hlt Φ hΦ
    rwa [Set.inter_eq_self_of_subset_left hΦs] at h
  · subst heq
    refine lt_of_le_of_lt (measure_mono (hΦs.trans ?_)) ((measure_setOf_ideleNorm_det_eq_eq_zero L hα).le.trans_lt
      ENNReal.zero_lt_top)
    intro g hg
    exact le_antisymm hg.2 hg.1
  · have hempty : Φ = ∅ := Set.eq_empty_of_subset_empty fun g hg => by
      have h := hΦs hg
      exact absurd (h.1.trans h.2) (not_le.mpr hgt)
    rw [hempty, measure_empty]
    exact ENNReal.zero_lt_top

end Measures

section Counting

theorem tsum_le_of_encard_le {ι : Type*} (f : ι → ℝ≥0∞) (S : Set ι) (hS : ∀ i, f i ≠ 0 → i ∈ S)
    (N : ℕ) (hN : S.encard ≤ N) (c : ℝ≥0∞) (hc : ∀ i, f i ≤ c) : ∑' i, f i ≤ N * c := by
  have hfin : S.Finite := Set.finite_of_encard_le_coe hN
  have hsupp : Function.support f ⊆ hfin.toFinset := fun i hi => by
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hS i hi
  rw [tsum_eq_sum' hsupp]
  have hcard : (hfin.toFinset.card : ℝ≥0∞) ≤ N := by
    have h := hN
    rw [hfin.encard_eq_coe_toFinset_card] at h
    exact_mod_cast (show hfin.toFinset.card ≤ N by exact_mod_cast h)
  calc ∑ i ∈ hfin.toFinset, f i ≤ ∑ i ∈ hfin.toFinset, c := Finset.sum_le_sum fun i _ => hc i
    _ = hfin.toFinset.card * c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * c := mul_le_mul_left hcard c

end Counting

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adelicGL2

abbrev karg (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.AdelicGL2 (𝓞 L) L :=
  x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
theorem continuous_karg (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) L) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => karg K L D σ p.1 δ p.2 :=
  ((continuous_fst.inv).mul continuous_const).mul
    ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst))

theorem main
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (α β : ℝ) (hα : 0 < α) (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫⁻ x in Φ, ∫⁻ z in Ω,
        ∑' δ : {δ : GL (Fin 2) L // ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
              ConjClasses.mk γ},
          ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (karg K L D σ x δ z)‖ₑ
          ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ⊤ := by
  classical

  haveI : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_ideles L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := inferInstance
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := inferInstance
  haveI : SigmaFinite νZ := inferInstance
  haveI : Countable (GL (Fin 2) L) := countable_GL2 L

  set Haar := adelicGLHaar (Fin 2) (𝓞 L) L with hHaar
  set P : GL (Fin 2) L → Prop := fun δ => ∃ γ : GL (Fin 2) K,
      (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ with hP
  set Fam : GL (Fin 2) L → Prop := fun δ => ∃ (h : GL (Fin 2) L) (u : Lˣ),
      δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) with hFam
  set ξv : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξv
  set kφ : GL (Fin 2) L → AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ → ℂ :=
    fun δ p => φ (karg K L D σ p.1 δ p.2) with hkφ
  set f : GL (Fin 2) L → AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ :=
    fun δ p => ‖ξv p.2 * kφ δ p‖ₑ with hf

  have hSc : IsCompact (tsupport φ) := hφc
  obtain ⟨m₀, hm₀, hlo⟩ : ∃ m₀ > 0, ∀ g ∈ tsupport φ,
      m₀ ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
    by_cases hne : (tsupport φ).Nonempty
    · obtain ⟨g₀, -, hmin⟩ :=
        hSc.exists_isMinOn hne (NumberField.TateGlobal.continuous_ideleNorm_det L).continuousOn
      exact ⟨_, NumberField.TateGlobal.ideleNorm_pos (F := L) _, fun g hg => hmin hg⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, one_pos, fun g hg => by rw [hne] at hg; exact absurd hg (Set.notMem_empty g)⟩
  obtain ⟨M₀, hhi⟩ : ∃ M₀, ∀ g ∈ tsupport φ,
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ≤ M₀ := by
    obtain ⟨M, hM⟩ := (hSc.image (NumberField.TateGlobal.continuous_ideleNorm_det L)).bddAbove
    exact ⟨M, fun g hg => hM ⟨g, hg, rfl⟩⟩
  have hm₁pos : 0 < Real.sqrt m₀ := Real.sqrt_pos.mpr hm₀
  set band : Set (AdeleRing (𝓞 L) L)ˣ :=
    {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀)} with hband_def
  have hband_meas : MeasurableSet band :=
    (isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm L)).measurableSet
  have hband : ∀ (δ : GL (Fin 2) L) (p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ),
      kφ δ p ≠ 0 → p.2 ∈ band := by
    intro δ p hne
    have hmem : karg K L D σ p.1 δ p.2 ∈ tsupport φ := subset_tsupport φ hne
    have hz2 : NumberField.TateGlobal.ideleNorm L p.2 ^ 2 ∈ Set.Icc m₀ M₀ := by
      rw [← ideleNorm_det_kernelArg K L D σ p.1 δ p.2]
      exact ⟨hlo _ hmem, hhi _ hmem⟩
    exact mem_Icc_sqrt_of_sq_mem_Icc (NumberField.TateGlobal.ideleNorm_pos (F := L) p.2).le hz2

  obtain ⟨C₁, hC₁c, hlift⟩ := exists_isCompact_forall_mem_exists_princ_mul L (M₁ := Real.sqrt M₀) hm₁pos
  obtain ⟨Mξ, hMξ⟩ := hC₁c.exists_bound_of_continuousOn hξc.continuousOn
  have hξband : ∀ z ∈ band, ‖ξv z‖ ≤ max Mξ 0 := by
    intro z hz
    obtain ⟨a, c, hc, rfl⟩ := hlift z hz
    have hval : ξv (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a * c) = ξv c := by
      simp only [hξv]
      have hmul : (⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a * c,
          Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
          ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a, Subgroup.mem_top _⟩ *
            ⟨c, Subgroup.mem_top _⟩ := rfl
      rw [hmul, map_mul, hξt _ ⟨a, rfl⟩, one_mul]
    rw [hval]
    exact (hMξ c hc).trans (le_max_left _ _)

  obtain ⟨Cφ, hCφ⟩ := hφ.bounded_above_of_compact_support hφc
  set cξ : ℝ≥0∞ := ENNReal.ofReal (max Mξ 0) with hcξ
  set cφ : ℝ≥0∞ := ENNReal.ofReal Cφ with hcφ

  have hf_le_k : ∀ δ p, f δ p ≤ cξ * ‖kφ δ p‖ₑ := by
    intro δ p
    by_cases hk : kφ δ p = 0
    · simp only [hf, hk, mul_zero, enorm_zero]
      exact bot_le
    · have hz := hband δ p hk
      simp only [hf]
      rw [enorm_mul]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hξband _ hz)
  have hk_le : ∀ δ p, ‖kφ δ p‖ₑ ≤ cφ := by
    intro δ p
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hCφ _)
  have hf_le_c : ∀ δ p, f δ p ≤ cξ * cφ := fun δ p =>
    (hf_le_k δ p).trans (mul_le_mul_right (hk_le δ p) _)
  have hf_zero : ∀ (δ : GL (Fin 2) L) (p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ),
      p.2 ∉ band → f δ p = 0 := by
    intro δ p hz
    have hk : kφ δ p = 0 := by
      by_contra hk
      exact hz (hband δ p hk)
    simp only [hf, hk, mul_zero, enorm_zero]

  obtain ⟨N, hN⟩ :=
    AutomorphicForm.exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
      K L hgen D φ hφc
  have hB : ∀ p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ,
      ∑' δ : {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}, f δ p ≤
        band.indicator (fun _ => (N : ℝ≥0∞) * (cξ * cφ)) p.2 := by
    intro p
    by_cases hz : p.2 ∈ band
    · rw [Set.indicator_of_mem hz]
      set S' : Set (GL (Fin 2) L) := {δ | P δ ∧ ¬ Fam δ ∧ φ (karg K L D σ p.1 δ p.2) ≠ 0} with hS'
      have hS'N : S'.encard ≤ N := hN p.1 p.2
      refine tsum_le_of_encard_le _ (Subtype.val ⁻¹' S') (fun i hi => ?_) N ?_ (cξ * cφ)
        (fun i => hf_le_c i p)
      · have hk : kφ i p ≠ 0 := by
          intro hk
          apply hi
          simp only [hf, hk, mul_zero, enorm_zero]
        exact ⟨i.2.1, i.2.2, hk⟩
      · calc (Subtype.val ⁻¹' S' : Set {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}).encard
            = (Subtype.val '' (Subtype.val ⁻¹' S' : Set {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ})).encard :=
              (Subtype.val_injective.injOn.encard_image).symm
          _ ≤ S'.encard := Set.encard_mono (Set.image_preimage_subset _ _)
          _ ≤ N := hS'N
    · rw [Set.indicator_of_notMem hz]
      have h0 : ∀ δ : {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}, f δ p = 0 := fun δ => hf_zero δ p hz
      simp only [h0, tsum_zero, le_refl]

  have hcontk : ∀ δ, Continuous (kφ δ) := fun δ => hφ.comp (continuous_karg K L D σ δ)
  have hmeasf : ∀ δ, Measurable (f δ) := fun δ =>
    ((hξc.comp continuous_snd).mul (hcontk δ)).measurable.enorm
  have hAm : Measurable fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ p :=
    Measurable.tsum fun δ => hmeasf δ

  have hsplit : ∀ p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ,
      ∑' δ : {δ : GL (Fin 2) L // P δ}, f δ p =
        (∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ p) +
          ∑' δ : {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}, f δ p := by
    intro p
    have e1 : ∑' δ : {δ : GL (Fin 2) L // P δ}, f δ p = ∑' δ, {δ | P δ}.indicator (fun δ => f δ p) δ :=
      tsum_subtype {δ | P δ} (fun δ => f δ p)
    have e2 : ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ p =
        ∑' δ, {δ | P δ ∧ Fam δ}.indicator (fun δ => f δ p) δ :=
      tsum_subtype {δ | P δ ∧ Fam δ} (fun δ => f δ p)
    have e3 : ∑' δ : {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}, f δ p =
        ∑' δ, {δ | P δ ∧ ¬ Fam δ}.indicator (fun δ => f δ p) δ :=
      tsum_subtype {δ | P δ ∧ ¬ Fam δ} (fun δ => f δ p)
    rw [e1, e2, e3, ← ENNReal.tsum_add]
    refine tsum_congr fun δ => ?_
    by_cases h1 : P δ
    · by_cases h2 : Fam δ
      · simp [Set.indicator, h1, h2]
      · simp [Set.indicator, h1, h2]
    · simp [Set.indicator, h1]

  have hI1 : ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ (x, z) ∂νZ ∂Haar < ⊤ := by
    have hC0 := AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top
      K L σ D α β hα Φ hΦs hΦ νZ Ω hΩ φ hφ hφc
    have hpt : ∀ p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ,
        ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ p ≤
          cξ * ∑' δ : {δ : GL (Fin 2) L // Fam δ}, ‖kφ δ p‖ₑ := by
      intro p
      calc ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ p
          ≤ ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, cξ * ‖kφ δ p‖ₑ := ENNReal.tsum_le_tsum fun δ => hf_le_k δ p
        _ = cξ * ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, ‖kφ δ p‖ₑ := ENNReal.tsum_mul_left
        _ ≤ cξ * ∑' δ : {δ : GL (Fin 2) L // Fam δ}, ‖kφ δ p‖ₑ := by
              refine mul_le_mul_right ?_ _
              exact ENNReal.tsum_comp_le_tsum_of_injective
                (f := fun δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ} => (⟨δ.1, δ.2.2⟩ : {δ : GL (Fin 2) L // Fam δ}))
                (fun a b hab => Subtype.ext (by simpa using hab))
                (fun δ : {δ : GL (Fin 2) L // Fam δ} => ‖kφ δ p‖ₑ)
    have hcξtop : cξ ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ (x, z) ∂νZ ∂Haar
        ≤ ∫⁻ x in Φ, ∫⁻ z in Ω, cξ * ∑' δ : {δ : GL (Fin 2) L // Fam δ}, ‖kφ δ (x, z)‖ₑ ∂νZ ∂Haar :=
          lintegral_mono fun x => lintegral_mono fun z => hpt (x, z)
      _ = cξ * ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // Fam δ}, ‖kφ δ (x, z)‖ₑ ∂νZ ∂Haar := by
          rw [← lintegral_const_mul' _ _ hcξtop]
          congr 1; funext x
          rw [← lintegral_const_mul' _ _ hcξtop]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC0

  have hΦfin : Haar Φ < ⊤ := measure_lt_top_of_isFundamentalDomain L α β hα Φ hΦs hΦ
  have hΩband : νZ (Ω ∩ band) ≤ νZ C₁ :=
    measure_inter_le_of_isFundamentalDomain L νZ Ω hΩ C₁ band (fun z hz => hlift z hz)
  have hI2 : ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}, f δ (x, z) ∂νZ ∂Haar < ⊤ := by
    calc ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}, f δ (x, z) ∂νZ ∂Haar
        ≤ ∫⁻ x in Φ, ∫⁻ z in Ω, band.indicator (fun _ => (N : ℝ≥0∞) * (cξ * cφ)) z ∂νZ ∂Haar :=
          lintegral_mono fun x => lintegral_mono fun z => hB (x, z)
      _ = ∫⁻ x in Φ, (N : ℝ≥0∞) * (cξ * cφ) * (νZ.restrict Ω) band ∂Haar := by
          congr 1; funext x
          exact lintegral_indicator_const hband_meas _
      _ = (N : ℝ≥0∞) * (cξ * cφ) * (νZ.restrict Ω) band * Haar Φ := setLIntegral_const _ _
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) hΦfin
          · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
              (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
          · rw [Measure.restrict_apply hband_meas, Set.inter_comm]
            exact hΩband.trans_lt hC₁c.measure_lt_top

  have hgoal : ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ}, f δ (x, z) ∂νZ ∂Haar < ⊤ := by
    have h1 : ∀ x, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ}, f δ (x, z) ∂νZ =
        (∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ ∧ Fam δ}, f δ (x, z) ∂νZ) +
          ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // P δ ∧ ¬ Fam δ}, f δ (x, z) ∂νZ := by
      intro x
      simp_rw [hsplit]
      exact lintegral_add_left' (hAm.comp measurable_prodMk_left).aemeasurable _
    simp_rw [h1]
    rw [lintegral_add_left' ((hAm.lintegral_prod_right' (ν := νZ.restrict Ω)).aemeasurable)]
    exact ENNReal.add_lt_top.mpr ⟨hI1, hI2⟩
  exact hgoal

end Main

end R3G3Red

end

section
open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (α β : ℝ) (hα : 0 < α) (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫⁻ x in Φ, ∫⁻ z in Ω,
        ∑' δ : {δ : GL (Fin 2) L // ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
              ConjClasses.mk γ},
          ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ₑ
          ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ⊤ :=
  R3G3Red.main K L hgen D α β hα Φ hΦs hΦ νZ Ω hΩ ξ hξc hξt φ hφ hφc

end

end S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top
end P2MW
export P2MW.S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top (solution)
