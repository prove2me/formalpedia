-- Prove2me | solution 1 for AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6ad05f54-bdb9-5960-9a2b-f99c67cdf784

import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl"
p2m_attr_erase "simp" "NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

noncomputable section

namespace R3C0Red

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

theorem sigmaCompactSpace_ideles : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

theorem countable_L : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := countable_L L
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := countable_L L
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L

end Instances

section Algebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

abbrev actU : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

abbrev σG : GL (Fin 2) L →* GL (Fin 2) L := Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * g = g * AutomorphicForm.centralScalar (𝓞 L) L z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 L) L) (fun r' => Commute.all _ r') _).eq

omit [NumberField L] in
theorem scalar_comm (u : Lˣ) (g : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (u : L) (fun r' => Commute.all _ r') _).eq

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

theorem globalPoints_scalar (u : Lˣ) :
    AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      AutomorphicForm.centralScalar (𝓞 L) L (princ L u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (u : L) i j) =
    Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem actU_princ (v : Lˣ) : actU K L D σ (princ L v) = princ L (Units.map (σ : L →* L) v) := by
  refine Units.ext ?_
  exact D.compat σ (v : L)

theorem princ_mul_actU (u : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    princ L u * actU K L D σ z = actU K L D σ (princ L (Units.map (σ.symm : L →* L) u) * z) := by
  rw [map_mul, actU_princ]
  congr 2
  refine Units.ext ?_
  show (u : L) = σ (σ.symm (u : L))
  rw [AlgEquiv.apply_symm_apply]

theorem kernelArg_eq (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (r : GL (Fin 2) L) (u : Lˣ)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L
        (Matrix.GeneralLinearGroup.scalar (Fin 2) u * (r⁻¹ * σG K L σ r)) *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
    (AutomorphicForm.globalPoints (𝓞 L) L r * x)⁻¹ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L r * x) *
      AutomorphicForm.centralScalar (𝓞 L) L (princ L u * actU K L D σ z) := by
  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι
  set θ := AutomorphicForm.sigmaAdelicAct K L D σ with hθ
  set c := AutomorphicForm.centralScalar (𝓞 L) L with hc
  have hσr : ι (σG K L σ r) = θ (ι r) := (AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ r).symm
  have h1 : ι (Matrix.GeneralLinearGroup.scalar (Fin 2) u * (r⁻¹ * σG K L σ r)) =
      c (princ L u) * ((ι r)⁻¹ * θ (ι r)) := by
    rw [map_mul, map_mul, map_inv, globalPoints_scalar, hσr]
  have h2 : θ (c z * x) = c (actU K L D σ z) * θ x := by
    rw [map_mul, hθ, hc, sigmaAdelicAct_centralScalar]
  rw [h1, h2, map_mul (c) (princ L u), map_mul θ (ι r) x, mul_inv_rev]
  have hcu := centralScalar_comm L (princ L u)
  have hcz := centralScalar_comm L (actU K L D σ z)

  calc x⁻¹ * (c (princ L u) * ((ι r)⁻¹ * θ (ι r))) * (c (actU K L D σ z) * θ x)
      = x⁻¹ * ((ι r)⁻¹ * θ (ι r)) * θ x * (c (princ L u) * c (actU K L D σ z)) := by
        rw [hcu ((ι r)⁻¹ * θ (ι r))]
        simp only [mul_assoc]
        rw [hcu (c (actU K L D σ z) * θ x), hcz (θ x)]
        simp only [mul_assoc]
        rw [← hcu (c (actU K L D σ z))]
    _ = x⁻¹ * (ι r)⁻¹ * (θ (ι r) * θ x) * (c (princ L u) * c (actU K L D σ z)) := by
        simp only [mul_assoc]

end Algebra

section Family

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

def cobScal : Subgroup (GL (Fin 2) L) where
  carrier := {s | ∃ u : Lˣ, s⁻¹ * σG K L σ s = Matrix.GeneralLinearGroup.scalar (Fin 2) u}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨u, ha⟩ ⟨v, hb⟩
    refine ⟨v * u, ?_⟩
    calc (a * b)⁻¹ * σG K L σ (a * b) = b⁻¹ * (a⁻¹ * σG K L σ a) * σG K L σ b := by
          simp only [mul_inv_rev, map_mul, mul_assoc]
      _ = b⁻¹ * σG K L σ b * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
          rw [ha, mul_assoc, scalar_comm, ← mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) (v * u) := by rw [hb, ← map_mul]
  inv_mem' := by
    rintro a ⟨u, ha⟩
    refine ⟨u⁻¹, ?_⟩
    have h : σG K L σ a = a * Matrix.GeneralLinearGroup.scalar (Fin 2) u :=
      inv_mul_eq_iff_eq_mul.mp ha
    rw [inv_inv, map_inv, h, mul_inv_rev, ← map_inv, scalar_comm, mul_inv_cancel_left]

theorem mem_cobScal_iff {s : GL (Fin 2) L} :
    s ∈ cobScal K L σ ↔ ∃ u : Lˣ, s⁻¹ * σG K L σ s = Matrix.GeneralLinearGroup.scalar (Fin 2) u :=
  Iff.rfl

abbrev CosetQ : Type := Quotient (QuotientGroup.rightRel (cobScal K L σ))

scoped instance countable_cosetQ [NumberField L] : Countable (CosetQ K L σ) := by
  haveI := countable_GL2 L
  exact Quotient.countable

theorem exists_out_eq_mul (h : GL (Fin 2) L) :
    ∃ s ∈ cobScal K L σ, (Quotient.mk'' h : CosetQ K L σ).out = s * h := by
  have hrel : QuotientGroup.rightRel (cobScal K L σ) ((Quotient.mk'' h : CosetQ K L σ).out) h :=
    Quotient.mk_out' h
  rw [QuotientGroup.rightRel_apply] at hrel
  refine ⟨(h * ((Quotient.mk'' h : CosetQ K L σ).out)⁻¹)⁻¹, (cobScal K L σ).inv_mem hrel, ?_⟩
  rw [mul_inv_rev, inv_inv, inv_mul_cancel_right]

abbrev Fam : Type :=
  {δ : GL (Fin 2) L // ∃ (h : GL (Fin 2) L) (u : Lˣ),
    δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u * (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)}

def famParam (p : CosetQ K L σ × Lˣ) : Fam K L σ :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 * ((p.1.out)⁻¹ * σG K L σ p.1.out), p.1.out, p.2, rfl⟩

theorem famParam_surjective : Function.Surjective (famParam K L σ) := by
  rintro ⟨δ, h, u, rfl⟩
  obtain ⟨s, hs, hout⟩ := exists_out_eq_mul K L σ h
  obtain ⟨v, hv⟩ := hs
  refine ⟨((Quotient.mk'' h : CosetQ K L σ), u * v⁻¹), Subtype.ext ?_⟩
  simp only [famParam, hout]
  show Matrix.GeneralLinearGroup.scalar (Fin 2) (u * v⁻¹) * ((s * h)⁻¹ * σG K L σ (s * h)) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * (h⁻¹ * σG K L σ h)
  have key : (s * h)⁻¹ * σG K L σ (s * h) = Matrix.GeneralLinearGroup.scalar (Fin 2) v * (h⁻¹ * σG K L σ h) := by
    calc (s * h)⁻¹ * σG K L σ (s * h) = h⁻¹ * (s⁻¹ * σG K L σ s) * σG K L σ h := by
          simp only [mul_inv_rev, map_mul, mul_assoc]
      _ = h⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) v * σG K L σ h := by rw [hv]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) v * (h⁻¹ * σG K L σ h) := by
          rw [← scalar_comm, mul_assoc]
  rw [key, ← mul_assoc, ← map_mul, mul_assoc u, inv_mul_cancel, mul_one]

theorem tsum_fam_le (f : Fam K L σ → ℝ≥0∞) :
    ∑' δ, f δ ≤ ∑' q : CosetQ K L σ, ∑' u : Lˣ, f (famParam K L σ (q, u)) := by
  calc ∑' δ, f δ ≤ ∑' p : CosetQ K L σ × Lˣ, f (famParam K L σ p) :=
        ENNReal.tsum_le_tsum_comp_of_surjective (famParam_surjective K L σ) f
    _ = ∑' q : CosetQ K L σ, ∑' u : Lˣ, f (famParam K L σ (q, u)) := ENNReal.tsum_prod'

theorem mul_out_injective {s s' : GL (Fin 2) L} (hs : s ∈ cobScal K L σ) (hs' : s' ∈ cobScal K L σ)
    {q q' : CosetQ K L σ} (h : s * q.out = s' * q'.out) : s = s' ∧ q = q' := by
  have hqq : q = q' := by
    rw [← Quotient.out_eq' q, ← Quotient.out_eq' q']
    refine Quotient.sound' ?_
    show QuotientGroup.rightRel (cobScal K L σ) q.out q'.out
    rw [QuotientGroup.rightRel_apply]
    have : q'.out * q.out⁻¹ = s'⁻¹ * s := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc]
      exact eq_inv_mul_of_mul_eq h.symm
    rw [this]
    exact (cobScal K L σ).mul_mem ((cobScal K L σ).inv_mem hs') hs
  subst hqq
  exact ⟨mul_right_cancel h, rfl⟩

end Family

section Centre

variable (L : Type) [Field L] [NumberField L]

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L :
      (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; simpa [Matrix.scalar_apply] using continuous_id'
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

def unipU : AutomorphicForm.AdelicGL2 (𝓞 L) L where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def unipL : AutomorphicForm.AdelicGL2 (𝓞 L) L where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_eq_centralScalar_of_mem_center {g : AutomorphicForm.AdelicGL2 (𝓞 L) L}
    (hg : g ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
    ∃ w : (AdeleRing (𝓞 L) L)ˣ, g = AutomorphicForm.centralScalar (𝓞 L) L w := by
  rw [Subgroup.mem_center_iff] at hg
  have hU := congrArg (fun m : AutomorphicForm.AdelicGL2 (𝓞 L) L => (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)))
    (hg (unipU L))
  have hL := congrArg (fun m : AutomorphicForm.AdelicGL2 (𝓞 L) L => (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)))
    (hg (unipL L))
  simp only [Units.val_mul] at hU hL
  set M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) with hM
  have hUv : ((unipU L : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![1, 1; 0, 1] := rfl
  have hLv : ((unipL L : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![1, 0; 1, 1] := rfl
  rw [hUv] at hU
  rw [hLv] at hL

  have e10 : M 1 0 = 0 := by
    have := congrFun (congrFun hU 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this

    linear_combination this
  have e01 : M 0 1 = 0 := by
    have := congrFun (congrFun hL 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have e0011 : M 0 0 = M 1 1 := by
    have := congrFun (congrFun hU 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this

  set Mi : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) :=
    ((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) with hMi
  have hmul : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmul' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h00 : M 0 0 * Mi 0 0 = 1 := by
    have := congrFun (congrFun hmul 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, e01, zero_mul, add_zero, Matrix.one_apply_eq] at this
    exact this
  have h00' : Mi 0 0 * M 0 0 = 1 := by
    have := congrFun (congrFun hmul' 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, e10, mul_zero, add_zero, Matrix.one_apply_eq] at this
    exact this
  refine ⟨⟨M 0 0, Mi 0 0, h00, h00'⟩, Units.ext ?_⟩
  show M = Matrix.scalar (Fin 2) (M 0 0)
  ext i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j
  · simp
  · simpa using e01
  · simpa using e10
  · simpa using e0011.symm

theorem isCompact_preimage_centralScalar {C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    IsCompact (AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C) := by

  set Φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ᵐᵒᵖ := fun g =>
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0,
      MulOpposite.op (((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0))
    with hΦ
  have hΦc : Continuous Φ := by
    refine Continuous.prodMk ?_ ?_
    · exact (Units.continuous_val.matrix_elem 0 0)
    · exact MulOpposite.continuous_op.comp (Units.continuous_coe_inv.matrix_elem 0 0)
  have hsub : AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C ⊆ Units.embedProduct _ ⁻¹' (Φ '' C) := by
    intro w hw
    refine ⟨AutomorphicForm.centralScalar (𝓞 L) L w, hw, ?_⟩
    simp only [hΦ, Units.embedProduct_apply]
    refine Prod.ext ?_ ?_
    · show Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L) 0 0 = (w : AdeleRing (𝓞 L) L)
      simp [Matrix.scalar_apply]
    · show MulOpposite.op (Matrix.scalar (Fin 2) ((w⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) 0 0) =
        MulOpposite.op ((w⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
      simp [Matrix.scalar_apply]
  have hclosed : IsClosed (AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C) :=
    hC.isClosed.preimage (continuous_centralScalar L)
  exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.image hΦc)).of_isClosed_subset hclosed hsub

end Centre

section PsiBound

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem continuous_actU : Continuous (actU K L D σ) :=
  Continuous.units_map _ (D.continuous_act σ)

theorem actU_inv_apply (w : (AdeleRing (𝓞 L) L)ˣ) : actU K L D σ⁻¹ (actU K L D σ w) = w := by
  refine Units.ext ?_
  show (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (w : AdeleRing (𝓞 L) L)) = w
  rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem actU_apply_inv (w : (AdeleRing (𝓞 L) L)ˣ) : actU K L D σ (actU K L D σ⁻¹ w) = w := by
  refine Units.ext ?_
  show (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) (w : AdeleRing (𝓞 L) L)) = w
  rw [← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem centralScalar_mem_center (w : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.centralScalar (𝓞 L) L w ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  Subgroup.mem_center_iff.mpr fun g => (centralScalar_comm L w g).symm

def tube (C' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  {g | ∃ g₁ k : AutomorphicForm.AdelicGL2 (𝓞 L) L,
    g₁⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g₁ ∈
        Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) ∧
      k ∈ C' ∧ g = g₁ * k}

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZ : Measure (AdeleRing (𝓞 L) L)ˣ)
  (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)

def Psi (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ w, ‖φ (y⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ y *
    AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ w))‖ₑ ∂νZ

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
theorem continuous_integrand (hφ : Continuous φ) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ‖φ (p.1⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ p.1 *
        AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ p.2))‖ₑ := by
  refine (hφ.comp ?_).enorm
  exact (continuous_fst.inv.mul ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp continuous_fst)).mul
    ((continuous_centralScalar L).comp ((continuous_actU K L D σ).comp continuous_snd))

theorem measurable_Psi [νZ.IsHaarMeasure] (hφ : Continuous φ) : Measurable (Psi K L D σ νZ φ) := by
  haveI := borelSpace_adelicGL2 L
  haveI : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI := secondCountableTopology_ideles L
  haveI := sigmaCompactSpace_ideles L
  exact (continuous_integrand K L D σ φ hφ).measurable.lintegral_prod_right'

theorem exists_Psi_le [νZ.IsHaarMeasure] (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (C' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC' : IsCompact C')
    (hP : ∀ y : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      y⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ y ∈
          (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
            Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * tsupport φ →
        ∃ g k : AutomorphicForm.AdelicGL2 (𝓞 L) L,
          g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g ∈
              Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) ∧
            k ∈ C' ∧ y = g * k) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ y, Psi K L D σ νZ φ y ≤ (tube K L D σ C').indicator (fun _ => M) y := by
  set θ := AutomorphicForm.sigmaAdelicAct K L D σ with hθ
  set c := AutomorphicForm.centralScalar (𝓞 L) L with hc

  obtain ⟨B, hB⟩ := hφ.bounded_above_of_compact_support hφc

  set C'' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    (fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      (θ p.1)⁻¹ * p.1 * p.2) '' (C' ×ˢ tsupport φ) with hC''
  have hC''c : IsCompact C'' := by
    refine (hC'.prod hφc.isCompact).image ?_
    exact ((((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp continuous_fst).inv.mul
      continuous_fst).mul continuous_snd)
  set K₀ : Set (AdeleRing (𝓞 L) L)ˣ := c ⁻¹' C'' with hK₀
  have hK₀c : IsCompact K₀ := isCompact_preimage_centralScalar L hC''c
  set K₁ : Set (AdeleRing (𝓞 L) L)ˣ := actU K L D σ ⁻¹' K₀ with hK₁
  have hK₁c : IsCompact K₁ := by
    have himg : IsCompact (actU K L D σ⁻¹ '' K₀) := hK₀c.image (continuous_actU K L D σ⁻¹)
    refine himg.of_isClosed_subset (hK₀c.isClosed.preimage (continuous_actU K L D σ)) ?_
    intro w hw
    exact ⟨actU K L D σ w, hw, actU_inv_apply K L D σ w⟩
  refine ⟨ENNReal.ofReal B * νZ K₁, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK₁c.measure_lt_top, fun y => ?_⟩
  by_cases hy : y ∈ tube K L D σ C'
  ·
    rw [Set.indicator_of_mem hy]
    obtain ⟨g₁, k, hg₁, hk, rfl⟩ := hy
    obtain ⟨w₁, hw₁⟩ := exists_eq_centralScalar_of_mem_center L hg₁
    have harg : (g₁ * k)⁻¹ * θ (g₁ * k) = k⁻¹ * θ k * c w₁ := by
      rw [mul_inv_rev, map_mul, mul_assoc, ← mul_assoc g₁⁻¹, show g₁⁻¹ * θ g₁ = c w₁ from hw₁,
        centralScalar_comm L w₁ (θ k), ← mul_assoc]

    set K₂ : Set (AdeleRing (𝓞 L) L)ˣ := {w | w₁ * actU K L D σ w ∈ K₀} with hK₂
    have hpt : ∀ w, ‖φ ((g₁ * k)⁻¹ * θ (g₁ * k) * c (actU K L D σ w))‖ₑ ≤
        K₂.indicator (fun _ => ENNReal.ofReal B) w := by
      intro w
      by_cases hw : w ∈ K₂
      · rw [Set.indicator_of_mem hw, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hB _)
      · rw [Set.indicator_of_notMem hw]
        refine le_of_eq ?_
        rw [enorm_eq_zero]
        refine image_eq_zero_of_notMem_tsupport fun ht => hw ?_

        show w₁ * actU K L D σ w ∈ c ⁻¹' C''
        refine ⟨(k, (g₁ * k)⁻¹ * θ (g₁ * k) * c (actU K L D σ w)), Set.mk_mem_prod hk ht, ?_⟩
        show (θ k)⁻¹ * k * ((g₁ * k)⁻¹ * θ (g₁ * k) * c (actU K L D σ w)) = c (w₁ * actU K L D σ w)
        rw [harg, map_mul]
        group
    calc Psi K L D σ νZ φ (g₁ * k)
        ≤ ∫⁻ w, K₂.indicator (fun _ => ENNReal.ofReal B) w ∂νZ := lintegral_mono hpt
      _ ≤ ENNReal.ofReal B * νZ K₂ := lintegral_indicator_const_le _ _
      _ = ENNReal.ofReal B * νZ K₁ := by

        have hK₂eq : K₂ = (fun w => actU K L D σ⁻¹ w₁ * w) ⁻¹' K₁ := by
          ext w
          simp only [hK₂, hK₁, Set.mem_setOf_eq, Set.mem_preimage, map_mul, actU_apply_inv]
        rw [hK₂eq, measure_preimage_mul]
  ·
    rw [Set.indicator_of_notMem hy]
    refine le_of_eq ?_
    refine (lintegral_congr fun w => ?_).trans lintegral_zero
    show ‖φ (y⁻¹ * θ y * c (actU K L D σ w))‖ₑ = 0
    rw [enorm_eq_zero]
    refine image_eq_zero_of_notMem_tsupport fun ht => hy ?_
    have hmem : y⁻¹ * θ y ∈
        (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) *
          tsupport φ := by
      refine Set.mem_mul.mpr ⟨(c (actU K L D σ w))⁻¹, ?_, y⁻¹ * θ y * c (actU K L D σ w), ht, ?_⟩
      · rw [← map_inv]
        exact centralScalar_mem_center L _
      · rw [← map_inv, centralScalar_comm L, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    exact hP y hmem

end PsiBound

section Unfold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem princ_injective : Function.Injective (princ L) := by
  intro a b h
  have := congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h
  exact Units.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L this)

def unitsPerm : Lˣ ≃ Lˣ where
  toFun := Units.map (σ.symm : L →* L)
  invFun := Units.map (σ : L →* L)
  left_inv u := Units.ext (σ.apply_symm_apply (u : L))
  right_inv u := Units.ext (σ.symm_apply_apply (u : L))

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)

theorem setLIntegral_tsum_princ_mul_actU_eq
    (hΩ : IsFundamentalDomain (princ L).range Ω νZ)
    (g : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z in Ω, ∑' u : Lˣ, g (princ L u * actU K L D σ z) ∂νZ = ∫⁻ w, g (actU K L D σ w) ∂νZ := by
  haveI := countable_units L
  haveI : Countable (princ L).range :=
    Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (princ L))
  set G' : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ := fun w => g (actU K L D σ w) with hG'
  have hG'm : Measurable G' := hg.comp (continuous_actU K L D σ).measurable

  have hsum : ∀ z, ∑' u : Lˣ, g (princ L u * actU K L D σ z) =
      ∑' γ : (princ L).range, G' (γ • z) := by
    intro z
    have h1 : ∀ u : Lˣ, g (princ L u * actU K L D σ z) = G' (princ L (unitsPerm K L σ u) * z) := by
      intro u
      rw [princ_mul_actU]
      rfl
    simp_rw [h1]
    rw [Equiv.tsum_eq (unitsPerm K L σ) (fun v => G' (princ L v * z))]
    let e : Lˣ ≃ (princ L).range := (MonoidHom.ofInjective (princ_injective L)).toEquiv
    rw [← Equiv.tsum_eq e (fun γ : (princ L).range => G' (γ • z))]
    exact tsum_congr fun v => rfl
  simp_rw [hsum]
  rw [lintegral_tsum (f := fun (γ : (princ L).range) (z : (AdeleRing (𝓞 L) L)ˣ) => G' (γ • z))
    fun γ => (hG'm.comp (measurable_const_smul (γ : (princ L).range))).aemeasurable]
  exact (hΩ.lintegral_eq_tsum'' G').symm

end Unfold

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem globalPoints_injective : Function.Injective (AutomorphicForm.globalPoints (𝓞 L) L) := by
  intro a b h
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have := congrArg (fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) h
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 L) L this

theorem image_mul_left_eq_smul {G : Type*} [Group G] (g : G) (s : Set G) :
    (fun x => g * x) '' s = g • s := rfl

def slab (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) := by
  haveI := borelSpace_adelicGL2 L
  exact measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable measurableSet_Icc

theorem globalPoints_smul_subset_slab {α β : ℝ} (γ : GL (Fin 2) L) {A : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)}
    (hA : A ⊆ slab L α β) : AutomorphicForm.globalPoints (𝓞 L) L γ • A ⊆ slab L α β := by
  rintro _ ⟨x, hx, rfl⟩
  show NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
    (AutomorphicForm.globalPoints (𝓞 L) L γ * x)) ∈ Set.Icc α β
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  exact hA hx

theorem main (σ : L ≃ₐ[K] L)
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
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫⁻ x in Φ, ∫⁻ z in Ω,
        ∑' δ : Fam K L σ,
          ‖φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ₑ
          ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ⊤ := by

  haveI := borelSpace_adelicGL2 L
  haveI : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI := secondCountableTopology_ideles L
  haveI := sigmaCompactSpace_ideles L
  haveI := countable_units L
  haveI := countable_GL2 L
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι
  set θ := AutomorphicForm.sigmaAdelicAct K L D σ with hθ
  set c := AutomorphicForm.centralScalar (𝓞 L) L with hc
  change Φ ⊆ slab L α β at hΦs
  change IsFundamentalDomain ι.range Φ (μ.restrict (slab L α β)) at hΦ

  obtain ⟨C', hC'c, hP⟩ :=
    AutomorphicForm.exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul
      K L σ D (tsupport φ) hφc.isCompact
  obtain ⟨M, hMtop, hΨle⟩ := exists_Psi_le K L D σ νZ φ hφ hφc C' hC'c hP
  have hΨm : Measurable (Psi K L D σ νZ φ) := measurable_Psi K L D σ νZ φ hφ

  have hinner : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      ∫⁻ z in Ω, ∑' δ : Fam K L σ, ‖φ (x⁻¹ * ι δ * θ (c z * x))‖ₑ ∂νZ ≤
        ∑' q : CosetQ K L σ, Psi K L D σ νZ φ (ι q.out * x) := by
    intro x
    have hcont : ∀ y : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        Measurable fun w : (AdeleRing (𝓞 L) L)ˣ => ‖φ (y⁻¹ * θ y * c w)‖ₑ := fun y =>
      ((hφ.comp (continuous_const.mul (continuous_centralScalar L))).enorm).measurable
    calc ∫⁻ z in Ω, ∑' δ : Fam K L σ, ‖φ (x⁻¹ * ι δ * θ (c z * x))‖ₑ ∂νZ
        ≤ ∫⁻ z in Ω, ∑' q : CosetQ K L σ, ∑' u : Lˣ,
            ‖φ ((ι q.out * x)⁻¹ * θ (ι q.out * x) * c (princ L u * actU K L D σ z))‖ₑ ∂νZ := by
          refine lintegral_mono fun z => ?_
          refine (tsum_fam_le K L σ _).trans (le_of_eq ?_)
          refine tsum_congr fun q => tsum_congr fun u => ?_
          show ‖φ (x⁻¹ * ι (Matrix.GeneralLinearGroup.scalar (Fin 2) u * ((q.out)⁻¹ * σG K L σ q.out)) *
              θ (c z * x))‖ₑ = _
          rw [kernelArg_eq]
      _ = ∑' q : CosetQ K L σ, ∫⁻ z in Ω, ∑' u : Lˣ,
            ‖φ ((ι q.out * x)⁻¹ * θ (ι q.out * x) * c (princ L u * actU K L D σ z))‖ₑ ∂νZ := by
          refine lintegral_tsum fun q => ?_
          refine (Measurable.tsum fun u => ?_).aemeasurable
          exact (hcont (ι q.out * x)).comp ((measurable_const_mul _).comp (continuous_actU K L D σ).measurable)
      _ = ∑' q : CosetQ K L σ, Psi K L D σ νZ φ (ι q.out * x) := by
          refine tsum_congr fun q => ?_
          exact setLIntegral_tsum_princ_mul_actU_eq K L D σ νZ Ω hΩ _ (hcont (ι q.out * x))

  obtain ⟨Φ₁, hΦ₁Φ, hΦ₁m, hΦ₁ae⟩ := hΦ.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hΦ₁s : Φ₁ ⊆ slab L α β := hΦ₁Φ.trans hΦs
  have hae : Φ =ᵐ[μ] Φ₁ := by
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · have h1 : (μ.restrict (slab L α β)) (Φ \ Φ₁) = 0 := (ae_eq_set.mp hΦ₁ae.symm).1
      rwa [Measure.restrict_apply' (measurableSet_slab L α β),
        Set.inter_eq_left.mpr (Set.diff_subset.trans hΦs)] at h1
    · rw [Set.diff_eq_empty.mpr hΦ₁Φ, measure_empty]

  have hpackΦ : ∀ γ γ' : GL (Fin 2) L, γ ≠ γ' → μ (ι γ • Φ₁ ∩ ι γ' • Φ₁) = 0 := by
    intro γ γ' hne
    have hne' : (⟨ι γ, γ, rfl⟩ : ι.range) ≠ ⟨ι γ', γ', rfl⟩ := fun h =>
      hne (globalPoints_injective L (congrArg Subtype.val h))
    have h0 := hΦ.aedisjoint hne'
    rw [Function.onFun, AEDisjoint] at h0
    change (μ.restrict (slab L α β)) (ι γ • Φ ∩ ι γ' • Φ) = 0 at h0
    rw [Measure.restrict_apply' (measurableSet_slab L α β),
      Set.inter_eq_left.mpr (Set.inter_subset_left.trans (globalPoints_smul_subset_slab L γ hΦs))] at h0
    exact measure_mono_null (Set.inter_subset_inter (Set.smul_set_mono hΦ₁Φ) (Set.smul_set_mono hΦ₁Φ)) h0

  set ΦT : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := ⋃ q : CosetQ K L σ, ι q.out • Φ₁ with hΦT
  have hΦTm : MeasurableSet ΦT := MeasurableSet.iUnion fun q => hΦ₁m.const_smul (ι q.out)
  have hΦTs : ΦT ⊆ slab L α β := Set.iUnion_subset fun q => globalPoints_smul_subset_slab L _ hΦ₁s
  have hdisj : Pairwise (AEDisjoint μ on fun q : CosetQ K L σ => ι q.out • Φ₁) := by
    intro q q' hqq
    exact hpackΦ _ _ fun h => hqq (Quotient.out_injective h)
  have hpackT : ∀ s s' : GL (Fin 2) L,
      (∃ u : Lˣ, s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      (∃ u : Lˣ, s'⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s' =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      s ≠ s' → μ (ι s • ΦT ∩ ι s' • ΦT) = 0 := by
    intro s s' hs hs' hne
    have hsub : ι s • ΦT ∩ ι s' • ΦT ⊆
        ⋃ q : CosetQ K L σ, ⋃ q' : CosetQ K L σ, (ι (s * q.out) • Φ₁ ∩ ι (s' * q'.out) • Φ₁) := by
      rintro y ⟨hy, hy'⟩
      rw [hΦT, Set.smul_set_iUnion, Set.mem_iUnion] at hy hy'
      obtain ⟨q, hq⟩ := hy
      obtain ⟨q', hq'⟩ := hy'
      rw [smul_smul, ← map_mul] at hq hq'
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨q', hq, hq'⟩⟩
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun q' => ?_)
    refine hpackΦ _ _ fun h => hne ?_
    exact (mul_out_injective K L σ hs hs' h).1

  have hfin : μ (ΦT ∩ tube K L D σ C') < ⊤ :=
    AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
      K L σ D α β hα C' hC'c ΦT hΦTs hΦTm hpackT
  have c1 : ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : Fam K L σ, ‖φ (x⁻¹ * ι δ * θ (c z * x))‖ₑ ∂νZ ∂μ
      ≤ ∫⁻ x in Φ, ∑' q : CosetQ K L σ, Psi K L D σ νZ φ (ι q.out * x) ∂μ := lintegral_mono hinner
  have c2 : ∫⁻ x in Φ, ∑' q : CosetQ K L σ, Psi K L D σ νZ φ (ι q.out * x) ∂μ
     = ∫⁻ x in Φ₁, ∑' q : CosetQ K L σ, Psi K L D σ νZ φ (ι q.out * x) ∂μ := setLIntegral_congr hae
  have c3 : ∫⁻ x in Φ₁, ∑' q : CosetQ K L σ, Psi K L D σ νZ φ (ι q.out * x) ∂μ
     = ∑' q : CosetQ K L σ, ∫⁻ x in Φ₁, Psi K L D σ νZ φ (ι q.out * x) ∂μ :=
        lintegral_tsum fun q => (hΨm.comp (measurable_const_mul _)).aemeasurable
  have c4 : ∀ q : CosetQ K L σ, ∫⁻ x in Φ₁, Psi K L D σ νZ φ (ι q.out * x) ∂μ =
      ∫⁻ y in ι q.out • Φ₁, Psi K L D σ νZ φ y ∂μ := by
        intro q
        have h := (measurePreserving_mul_left μ (ι q.out)).setLIntegral_comp_emb (measurableEmbedding_mulLeft _)
          (Psi K L D σ νZ φ) Φ₁
        rw [image_mul_left_eq_smul] at h
        exact h
  have c5 := (lintegral_iUnion₀ (μ := μ) (s := fun q : CosetQ K L σ => ι q.out • Φ₁)
      (fun q => (hΦ₁m.const_smul (ι q.out)).nullMeasurableSet) hdisj (Psi K L D σ νZ φ)).symm
  have c6 : ∫⁻ y in ΦT, Psi K L D σ νZ φ y ∂μ ≤ ∫⁻ y in ΦT, (tube K L D σ C').indicator (fun _ => M) y ∂μ :=
    lintegral_mono fun y => hΨle y
  have c7 : ∫⁻ y in ΦT, (tube K L D σ C').indicator (fun _ => M) y ∂μ ≤ M * (μ.restrict ΦT) (tube K L D σ C') :=
    lintegral_indicator_const_le _ _
  have c8 : (μ.restrict ΦT) (tube K L D σ C') = μ (ΦT ∩ tube K L D σ C') := by
    rw [Measure.restrict_apply' hΦTm, Set.inter_comm]
  rw [c8] at c7
  refine lt_of_le_of_lt (c1.trans ?_) (ENNReal.mul_lt_top hMtop hfin)
  rw [c2, c3]
  refine le_trans (le_of_eq ?_) (c6.trans c7)
  rw [← c5]
  exact tsum_congr c4

end Main

end R3C0Red
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top.R3C0Red"

end
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top.R3C0Red"

section

attribute [local instance] NumberField.AdelicHaar.glBorel
open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
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
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫⁻ x in Φ, ∫⁻ z in Ω,
        ∑' δ : {δ : GL (Fin 2) L // ∃ (h : GL (Fin 2) L) (u : Lˣ),
            δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
              (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)},
          ‖φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ₑ
          ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ⊤ :=
  R3C0Red.main K L σ D α β hα Φ hΦs hΦ νZ Ω hΩ φ hφ hφc

end
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top.R3C0Red"

end S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top
end P2MW
export P2MW.S_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top (solution)
