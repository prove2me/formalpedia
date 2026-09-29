-- Prove2me | solution 1 for AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9a12fe25-cdbc-567b-beb8-57e50d65ef93

import Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
import Theorems.Thm_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
import Theorems.Thm_AutomorphicForm_exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b"
p2m_attr_erase "simp" "AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply"
p2m_attr_erase "simp" "Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace R4VRed

open MeasureTheory MeasureTheory.Measure NumberField Filter Function Set
open scoped ENNReal NNReal Topology Pointwise

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev GG : Type := AutomorphicForm.AdelicGL2 (𝓞 L) L

abbrev θ : GG L →* GG L := AutomorphicForm.sigmaAdelicAct K L D σ

abbrev ZZ : Subgroup (GG L) := Subgroup.center (GG L)

abbrev G1 : Subgroup (GG L) :=
  MonoidHom.eqLocus ((QuotientGroup.mk' (ZZ L)).comp (θ K L D σ)) (QuotientGroup.mk' (ZZ L))

abbrev Hf : Subgroup (GG L) := MonoidHom.eqLocus (θ K L D σ) (MonoidHom.id (GG L))

abbrev ι : GL (Fin 2) L →* GG L := AutomorphicForm.globalPoints (𝓞 L) L

abbrev rsc (t : Lˣ) : GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2) t

abbrev sc (t : Lˣ) : GG L := ι L (rsc L t)

theorem mem_G1_iff {g : GG L} :
    g ∈ G1 K L D σ ↔ g⁻¹ * θ K L D σ g ∈ ZZ L := by
  show (QuotientGroup.mk' _ (θ K L D σ g) = QuotientGroup.mk' _ g) ↔ _
  rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]

theorem mem_Hf_iff {g : GG L} : g ∈ Hf K L D σ ↔ θ K L D σ g = g := Iff.rfl

theorem Hf_le_G1 : Hf K L D σ ≤ G1 K L D σ := by
  intro h hh
  rw [mem_G1_iff, (mem_Hf_iff K L D σ).mp hh, inv_mul_cancel]
  exact (ZZ L).one_mem

theorem θ_surjective : Function.Surjective (θ K L D σ) := by
  intro g
  refine ⟨AutomorphicForm.sigmaAdelicAct K L D σ⁻¹ g, ?_⟩
  have h : (θ K L D σ).comp (AutomorphicForm.sigmaAdelicAct K L D σ⁻¹) = MonoidHom.id _ := by
    rw [← AutomorphicForm.sigmaAdelicAct_mul, mul_inv_cancel, AutomorphicForm.sigmaAdelicAct_one]
  exact congrArg (fun f : GG L →* GG L => f g) h

theorem θ_mem_center {z : GG L} (hz : z ∈ ZZ L) : θ K L D σ z ∈ ZZ L := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := θ_surjective K L D σ g
  rw [← map_mul, ← map_mul, hz g']

theorem center_le_G1 : ZZ L ≤ G1 K L D σ := fun _ hz =>
  (mem_G1_iff K L D σ).mpr ((ZZ L).mul_mem ((ZZ L).inv_mem hz) (θ_mem_center K L D σ hz))

theorem scalar_mem_center {R : Type*} [CommRing R] (u : Rˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.center (GL (Fin 2) R) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem map_scalar {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* R') u) := by
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem sc_mem_center (t : Lˣ) : sc L t ∈ ZZ L := by
  show AutomorphicForm.globalPoints (𝓞 L) L (rsc L t) ∈ _
  unfold AutomorphicForm.globalPoints
  rw [map_scalar]
  exact scalar_mem_center _

theorem sc_mem_G1 (t : Lˣ) : sc L t ∈ G1 K L D σ := center_le_G1 K L D σ (sc_mem_center L t)

theorem sc_comm (t : Lˣ) (g : GG L) : g * sc L t = sc L t * g :=
  Subgroup.mem_center_iff.mp (sc_mem_center L t) g

theorem θ_ι (s : GL (Fin 2) L) :
    θ K L D σ (ι L s) = ι L (Matrix.GeneralLinearGroup.map (σ : L →+* L) s) :=
  AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ s

theorem ι_mem_Hf {s : GL (Fin 2) L} (hs : Matrix.GeneralLinearGroup.map (σ : L →+* L) s = s) :
    ι L s ∈ Hf K L D σ := by
  rw [mem_Hf_iff, θ_ι, hs]

def Kfix : Subgroup Lˣ where
  carrier := {t | σ (t : L) = t}
  mul_mem' {a b} ha hb := by
    show σ ((a * b : Lˣ) : L) = (a * b : Lˣ)
    rw [Units.val_mul, map_mul, ha, hb]
  one_mem' := by show σ ((1 : Lˣ) : L) = (1 : Lˣ); rw [Units.val_one, map_one]
  inv_mem' {a} ha := by
    show σ ((a⁻¹ : Lˣ) : L) = (a⁻¹ : Lˣ)
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha]

theorem mem_Kfix_iff {t : Lˣ} : t ∈ Kfix K L σ ↔ σ (t : L) = t := Iff.rfl

theorem map_rsc_of_mem_Kfix {t : Lˣ} (ht : t ∈ Kfix K L σ) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (rsc L t) = rsc L t := by
  rw [map_scalar]
  congr 1
  exact Units.ext ht

theorem mem_Kfix_of_map_rsc {t : Lˣ}
    (h : Matrix.GeneralLinearGroup.map (σ : L →+* L) (rsc L t) = rsc L t) : t ∈ Kfix K L σ := by
  rw [map_scalar] at h
  have h00 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
  exact h00

def InS (s : GL (Fin 2) L) : Prop :=
  ∃ u : Lˣ, s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s = Matrix.GeneralLinearGroup.scalar (Fin 2) u

theorem inS_of_fixed_mul_rsc {s : GL (Fin 2) L}
    (hs : Matrix.GeneralLinearGroup.map (σ : L →+* L) s = s) (t : Lˣ) :
    InS K L σ (s * rsc L t) := by
  refine ⟨t⁻¹ * Units.map ((σ : L →+* L) : L →* L) t, ?_⟩
  rw [map_mul, hs, map_scalar, mul_inv_rev, mul_assoc]
  have hc : (rsc L t)⁻¹ * (s⁻¹ * (s * Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map ((σ : L →+* L) : L →* L) t))) =
      (rsc L t)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map ((σ : L →+* L) : L →* L) t) := by
    rw [inv_mul_cancel_left]
  rw [hc]
  show (Matrix.GeneralLinearGroup.scalar (Fin 2) t)⁻¹ * _ = _
  rw [← map_inv, ← map_mul]

theorem inS_rsc_mul (t : Lˣ) {u : GL (Fin 2) L} (hu : InS K L σ u) : InS K L σ (rsc L t * u) := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨v * (t⁻¹ * Units.map ((σ : L →+* L) : L →* L) t), ?_⟩
  rw [map_mul, map_scalar, mul_inv_rev, map_mul, ← hv]

  have hc1 : (rsc L t)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map ((σ : L →+* L) : L →* L) t) *
      Matrix.GeneralLinearGroup.map (σ : L →+* L) u) =
      Matrix.GeneralLinearGroup.map (σ : L →+* L) u *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (t⁻¹ * Units.map ((σ : L →+* L) : L →* L) t) := by
    rw [map_mul, ← mul_assoc]
    show (Matrix.GeneralLinearGroup.scalar (Fin 2) t)⁻¹ * _ * _ = _
    rw [← map_inv]
    have hz := Subgroup.mem_center_iff.mp (scalar_mem_center (R := L) (Units.map ((σ : L →+* L) : L →* L) t))
      (Matrix.GeneralLinearGroup.map (σ : L →+* L) u)
    have hz' := Subgroup.mem_center_iff.mp (scalar_mem_center (R := L) t⁻¹)
      (Matrix.GeneralLinearGroup.map (σ : L →+* L) u)
    rw [mul_assoc, ← hz, ← mul_assoc, ← hz', mul_assoc]
  rw [mul_assoc u⁻¹, hc1, ← mul_assoc]

theorem inS_rsc_inv (t : Lˣ) : InS K L σ (rsc L t)⁻¹ := by
  have h := inS_of_fixed_mul_rsc K L σ (s := 1) (by rw [map_one]) t⁻¹
  rw [one_mul] at h
  show InS K L σ (Matrix.GeneralLinearGroup.scalar (Fin 2) t)⁻¹
  rw [← map_inv]
  exact h

theorem sc_inv_smul_smul (t : Lˣ) (s : GL (Fin 2) L) (E : Set (GG L)) :
    (sc L t)⁻¹ • (ι L s • E) = ι L ((rsc L t)⁻¹ * s) • E := by
  rw [smul_smul, map_mul, map_inv]

theorem mem_sc_inv_smul_iff (t : Lˣ) (z : GG L) (A : Set (GG L)) :
    z ∈ (sc L t)⁻¹ • A ↔ sc L t * z ∈ A :=
  Set.mem_inv_smul_set_iff

theorem mem_Kfix_of_eq {s s' : GL (Fin 2) L}
    (hs : Matrix.GeneralLinearGroup.map (σ : L →+* L) s = s)
    (hs' : Matrix.GeneralLinearGroup.map (σ : L →+* L) s' = s')
    {t t' : Lˣ} (h : s * (rsc L t)⁻¹ = s' * (rsc L t')⁻¹) : t'⁻¹ * t ∈ Kfix K L σ := by

  have h1 : s'⁻¹ * s = rsc L (t'⁻¹ * t) := by
    have h2 : s = s' * (rsc L t')⁻¹ * rsc L t := by
      rw [← h, inv_mul_cancel_right]
    rw [h2, mul_assoc, inv_mul_cancel_left]
    show _ = Matrix.GeneralLinearGroup.scalar (Fin 2) (t'⁻¹ * t)
    rw [map_mul, map_inv]
  refine mem_Kfix_of_map_rsc K L σ ?_
  rw [← h1, map_mul, map_inv, hs, hs']

theorem eq_of_rsc_inv_eq {s s' : GL (Fin 2) L} {t : Lˣ}
    (h : s * (rsc L t)⁻¹ = s' * (rsc L t)⁻¹) : s = s' :=
  mul_right_cancel h

theorem rsc_injective : Function.Injective (rsc L) := by
  intro t t' h
  have h00 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
  exact Units.ext h00

theorem sc_inv_eq (w : Lˣ) : (sc L w)⁻¹ = ι L (rsc L w)⁻¹ := (map_inv (ι L) (rsc L w)).symm

theorem sc_mul (t t' : Lˣ) : sc L (t * t') = sc L t * sc L t' := by
  show ι L (Matrix.GeneralLinearGroup.scalar (Fin 2) (t * t')) = _
  rw [map_mul, map_mul]

theorem sc_one : sc L 1 = 1 := by
  show ι L (Matrix.GeneralLinearGroup.scalar (Fin 2) 1) = 1
  rw [map_one, map_one]

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

theorem countable_GL : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → Matrix (Fin 2) (Fin 2) L))
    Units.val_injective

theorem isClosed_center : IsClosed (ZZ L : Set (GG L)) := by
  have h : (ZZ L : Set (GG L)) = ⋂ g : GG L, {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

theorem isClosed_G1 : IsClosed (G1 K L D σ : Set (GG L)) := by
  have h : (G1 K L D σ : Set (GG L)) =
      (fun g => g⁻¹ * θ K L D σ g) ⁻¹' (ZZ L : Set (GG L)) := by
    ext g; exact mem_G1_iff K L D σ
  rw [h]
  exact (isClosed_center L).preimage
    (continuous_id.inv.mul (AutomorphicForm.continuous_sigmaAdelicAct K L D σ))

theorem isClosed_Hf : IsClosed (Hf K L D σ : Set (GG L)) := by
  have h : (Hf K L D σ : Set (GG L)) = {g | θ K L D σ g = g} := by
    ext g; exact mem_Hf_iff K L D σ
  rw [h]
  exact isClosed_eq (AutomorphicForm.continuous_sigmaAdelicAct K L D σ) continuous_id

attribute [local instance] NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing

theorem secondCountable_GG : SecondCountableTopology (GG L) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L

theorem secondCountable_G1 : SecondCountableTopology (G1 K L D σ) :=
  haveI := secondCountable_GG L
  TopologicalSpace.Subtype.secondCountableTopology (G1 K L D σ : Set (GG L))

theorem locallyCompactSpace_G1 : LocallyCompactSpace (G1 K L D σ) :=
  (isClosed_G1 K L D σ).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem locallyCompactSpace_Hf : LocallyCompactSpace (Hf K L D σ) :=
  (isClosed_Hf K L D σ).isClosedEmbedding_subtypeVal.locallyCompactSpace

abbrev H1 : Subgroup (G1 K L D σ) := (Hf K L D σ).subgroupOf (G1 K L D σ)

theorem mem_H1_iff {x : G1 K L D σ} : x ∈ H1 K L D σ ↔ (x : GG L) ∈ Hf K L D σ :=
  Subgroup.mem_subgroupOf

theorem isClosed_H1 : IsClosed (H1 K L D σ : Set (G1 K L D σ)) := by
  have h : (H1 K L D σ : Set (G1 K L D σ)) = Subtype.val ⁻¹' (Hf K L D σ : Set (GG L)) := by
    ext x; exact mem_H1_iff K L D σ
  rw [h]
  exact (isClosed_Hf K L D σ).preimage continuous_subtype_val

theorem locallyCompactSpace_H1 : LocallyCompactSpace (H1 K L D σ) :=
  haveI := locallyCompactSpace_G1 K L D σ
  (isClosed_H1 K L D σ).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem secondCountable_H1 : SecondCountableTopology (H1 K L D σ) :=
  haveI := secondCountable_G1 K L D σ
  TopologicalSpace.Subtype.secondCountableTopology (H1 K L D σ : Set (G1 K L D σ))

def eH : H1 K L D σ →* Hf K L D σ where
  toFun x := ⟨(x : G1 K L D σ), (mem_H1_iff K L D σ).mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def eHinv : Hf K L D σ → H1 K L D σ := fun y =>
  ⟨⟨(y : GG L), Hf_le_G1 K L D σ y.2⟩, (mem_H1_iff K L D σ).mpr y.2⟩

def eHomeo : H1 K L D σ ≃ₜ Hf K L D σ where
  toFun := eH K L D σ
  invFun := eHinv K L D σ
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

theorem isOpenEmbedding_eH : Topology.IsOpenEmbedding (eH K L D σ) :=
  (eHomeo K L D σ).isOpenEmbedding

theorem eH_surjective : Function.Surjective (eH K L D σ) := (eHomeo K L D σ).surjective

section Weil

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]

theorem measurable_weight (H : Subgroup Γ) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · simp_rw [ENNReal.tsum_eq_iSup_sum]
    refine Measurable.iSup fun s => s.measurable_fun_sum fun n _ => ?_
    exact measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet))
  · exact measurable_const

theorem measurable_density (H : Subgroup Γ) (μH : Measure H) [SFinite μH] :
    Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : Γ × H => HaarQuotient.weight H μH ((z.2 : Γ) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

theorem lintegral_quot_comp_mul_right (μ : Measure Γ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (H : Subgroup Γ) (hH : IsClosed (H : Set Γ))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Ψ : Γ → ℝ≥0∞) (hΨ : Measurable Ψ) (hinv : ∀ (x : H) (g : Γ), Ψ ((x : Γ) * g) = Ψ g) (y : Γ) :
    ∫⁻ q, Ψ (q.out * y) ∂(HaarQuotient.measure μ H μH) =
      ∫⁻ q, Ψ q.out ∂(HaarQuotient.measure μ H μH) := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set Γ)
  set ν := HaarQuotient.measure μ H μH with hν
  set Dn := HaarQuotient.density H μH with hDn
  have hDm : Measurable Dn := measurable_density H μH
  have hD1 : ∀ g : Γ, ∫⁻ x : H, Dn ((x : Γ) * g) ∂μH = 1 :=
    HaarQuotient.lintegral_density_mul_eq_one H hH μH
  have hDxm : ∀ g : Γ, Measurable fun x : H => Dn ((x : Γ) * g) := fun g =>
    hDm.comp (measurable_subtype_coe.mul_const g)

  have ha : ∫⁻ q, Ψ q.out ∂ν = ∫⁻ g, Dn g * Ψ g ∂μ := by
    rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH (fun g => Dn g * Ψ g)
      (hDm.mul hΨ)]
    refine lintegral_congr fun q => ?_
    have h1 : ∀ x : H, Dn ((x : Γ) * q.out) * Ψ ((x : Γ) * q.out) = Dn ((x : Γ) * q.out) * Ψ q.out := by
      intro x; rw [hinv x]
    simp_rw [h1]
    rw [lintegral_mul_const _ (hDxm q.out), hD1, one_mul]

  have hΨy : Measurable fun g => Ψ (g * y) := hΨ.comp (measurable_mul_const y)
  have hb : ∫⁻ q, Ψ (q.out * y) ∂ν = ∫⁻ g, Dn g * Ψ (g * y) ∂μ := by
    rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH (fun g => Dn g * Ψ (g * y))
      (hDm.mul hΨy)]
    refine lintegral_congr fun q => ?_
    have h1 : ∀ x : H, Dn ((x : Γ) * q.out) * Ψ ((x : Γ) * q.out * y) =
        Dn ((x : Γ) * q.out) * Ψ (q.out * y) := by
      intro x; rw [mul_assoc, hinv x]
    simp_rw [h1]
    rw [lintegral_mul_const _ (hDxm q.out), hD1, one_mul]

  have hc : ∫⁻ g, Dn g * Ψ (g * y) ∂μ = ∫⁻ g, Dn (g * y⁻¹) * Ψ g ∂μ := by
    have := lintegral_mul_right_eq_self (μ := μ) (fun g => Dn (g * y⁻¹) * Ψ g) y
    simp only [mul_inv_cancel_right] at this
    exact this

  have hd : ∫⁻ g, Dn (g * y⁻¹) * Ψ g ∂μ = ∫⁻ q, Ψ q.out ∂ν := by
    rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH (fun g => Dn (g * y⁻¹) * Ψ g)
      ((hDm.comp (measurable_mul_const _)).mul hΨ)]
    refine lintegral_congr fun q => ?_
    have h1 : ∀ x : H, Dn ((x : Γ) * q.out * y⁻¹) * Ψ ((x : Γ) * q.out) =
        Dn ((x : Γ) * (q.out * y⁻¹)) * Ψ q.out := by
      intro x; rw [mul_assoc, hinv x]
    simp_rw [h1]
    rw [lintegral_mul_const _ (hDxm (q.out * y⁻¹)), hD1, one_mul]
  rw [hb, hc, hd]

omit [LocallyCompactSpace Γ] [SecondCountableTopology Γ] in

theorem lintegral_indicator_mul_eq (H : Subgroup Γ) (μH : Measure H) {T : Set Γ}
    (hT : MeasurableSet T) (g : Γ) :
    ∫⁻ x : H, T.indicator (1 : Γ → ℝ≥0∞) ((x : Γ) * g) ∂μH = μH {x : H | (x : Γ) * g ∈ T} := by
  have hm : MeasurableSet {x : H | (x : Γ) * g ∈ T} :=
    measurableSet_preimage (measurable_subtype_coe.mul_const g) hT
  rw [← lintegral_indicator_one hm]
  refine lintegral_congr fun x => ?_
  by_cases hx : (x : Γ) * g ∈ T
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : H | (x : Γ) * g ∈ T} from hx)]
    rfl
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ {x : H | (x : Γ) * g ∈ T} from hx)]

theorem apply_out_mk {H : Subgroup Γ} {α : Type*} {Φ : Γ → α}
    (hinv : ∀ (x : H) (g : Γ), Φ ((x : Γ) * g) = Φ g) (g : Γ) :
    Φ (Quotient.mk'' g : MulAction.orbitRel.Quotient H Γ).out = Φ g := by
  have h : (MulAction.orbitRel H Γ) (Quotient.mk'' g : MulAction.orbitRel.Quotient H Γ).out g :=
    Quotient.exact (Quotient.out_eq _)
  obtain ⟨x, hx⟩ := MulAction.orbitRel_apply.1 h
  rw [← hx]
  exact hinv x g

theorem measurable_comp_out {H : Subgroup Γ} {α : Type*}
    [MeasurableSpace α] {Φ : Γ → α} (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : Γ), Φ ((x : Γ) * g) = Φ g) :
    Measurable fun q : MulAction.orbitRel.Quotient H Γ => Φ q.out := by
  refine measurable_from_quotient.2 ?_
  have : (fun q : MulAction.orbitRel.Quotient H Γ => Φ q.out) ∘ Quotient.mk'' = Φ :=
    funext fun g => apply_out_mk hinv g
  rw [this]
  exact hΦ

omit [LocallyCompactSpace Γ] in

theorem measurable_slice (H : Subgroup Γ) (μH : Measure H) [SFinite μH] {T : Set Γ}
    (hT : MeasurableSet T) :
    Measurable fun g : Γ => ∫⁻ x : H, T.indicator (1 : Γ → ℝ≥0∞) ((x : Γ) * g) ∂μH := by
  have h2 : Measurable fun z : Γ × H => T.indicator (1 : Γ → ℝ≥0∞) ((z.2 : Γ) * z.1) :=
    (measurable_one.indicator hT).comp
      ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  exact h2.lintegral_prod_right'

omit [LocallyCompactSpace Γ] [SecondCountableTopology Γ] in

theorem slice_mul_left (H : Subgroup Γ) (μH : Measure H) [μH.IsMulRightInvariant] {T : Set Γ}
    (x₀ : H) (g : Γ) :
    μH {x : H | (x : Γ) * ((x₀ : Γ) * g) ∈ T} = μH {x : H | (x : Γ) * g ∈ T} := by
  have h : {x : H | (x : Γ) * ((x₀ : Γ) * g) ∈ T} = (fun x : H => x * x₀) ⁻¹' {x : H | (x : Γ) * g ∈ T} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Subgroup.coe_mul, mul_assoc]
  rw [h, measure_preimage_mul_right]

end Weil

section Main

variable [MeasurableSpace (GG L)] [BorelSpace (GG L)]

abbrev Nd (g : GG L) : ℝ := NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)

omit [MeasurableSpace (GG L)] [BorelSpace (GG L)] in
theorem Nd_mul (g h : GG L) : Nd L (g * h) = Nd L g * Nd L h := by
  simp only [Nd, map_mul, NumberField.TateGlobal.ideleNorm_mul]

omit [MeasurableSpace (GG L)] [BorelSpace (GG L)] in
theorem Nd_sc (t : Lˣ) : Nd L (sc L t) = 1 :=
  AutomorphicForm.ideleNorm_det_globalPoints (F := L) (rsc L t)

omit [MeasurableSpace (GG L)] [BorelSpace (GG L)] in
theorem Nd_ι (s : GL (Fin 2) L) : Nd L (ι L s) = 1 :=
  AutomorphicForm.ideleNorm_det_globalPoints (F := L) s

set_option maxHeartbeats 6400000 in

theorem main
    (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure] (a b : ℝ) (ha : 0 < a) :
    ∃ V₀ : ℝ≥0∞, V₀ < ⊤ ∧
      ∀ E : Set (GG L),
        E ⊆ {g | Nd L g ∈ Set.Icc a b} →
        MeasurableSet E →
        (∀ s s' : GL (Fin 2) L, InS K L σ s → InS K L σ s' → s ≠ s' →
            μ₁ (Subtype.val ⁻¹' (ι L s • E ∩ ι L s' • E)) = 0) →
        μ₁ (Subtype.val ⁻¹' E) ≤ V₀ := by
  classical

  haveI := secondCountable_GG L
  haveI := secondCountable_G1 K L D σ
  haveI := locallyCompactSpace_G1 K L D σ
  haveI := locallyCompactSpace_Hf K L D σ
  haveI := locallyCompactSpace_H1 K L D σ
  haveI := secondCountable_H1 K L D σ
  haveI : μ₁.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center K L σ D μ₁

  set μHf : Measure (Hf K L D σ) := Measure.haar with hμHf
  haveI : μHf.IsHaarMeasure := by rw [hμHf]; exact Measure.isHaarMeasure_haarMeasure _
  haveI : μHf.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id K L σ D μHf
  have heHm : MeasurableEmbedding (eH K L D σ) := (isOpenEmbedding_eH K L D σ).measurableEmbedding
  set μH1 : Measure (H1 K L D σ) := μHf.comap (eH K L D σ) with hμH1
  haveI : μH1.IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) (f := eH K L D σ) μHf (isOpenEmbedding_eH K L D σ)
  haveI : μH1.IsMulRightInvariant := IsMulRightInvariant.comap (f := eH K L D σ) μHf heHm
  have hHc : IsClosed (H1 K L D σ : Set (G1 K L D σ)) := isClosed_H1 K L D σ

  have htrans : ∀ (P : GG L → Prop),
      μH1 {x : H1 K L D σ | P ((x : G1 K L D σ) : GG L)} = μHf {y : Hf K L D σ | P (y : GG L)} := by
    intro P
    rw [hμH1, heHm.comap_apply]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := eH_surjective K L D σ y
      exact ⟨x, hy, rfl⟩

  obtain ⟨C, hCc, hCZ, hdec⟩ :=
    AutomorphicForm.exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
      K L σ D
  have hCne : C.Nonempty := by
    obtain ⟨h, c, l, -, hc, -⟩ := hdec 1 (by rw [inv_one, one_mul, map_one]; exact (ZZ L).one_mem)
    exact ⟨c, hc⟩
  have hNdc : Continuous (Nd L) := NumberField.TateGlobal.continuous_ideleNorm_det L
  obtain ⟨k₀, hk₀, hmin⟩ := hCc.exists_isMinOn hCne hNdc.continuousOn
  obtain ⟨k₁, hk₁, hmax⟩ := hCc.exists_isMaxOn hCne hNdc.continuousOn
  set m := Nd L k₀ with hm
  set M := Nd L k₁ with hM
  have hm0 : 0 < m := NumberField.TateGlobal.ideleNorm_pos (F := L) _
  have hM0 : 0 < M := NumberField.TateGlobal.ideleNorm_pos (F := L) _
  have hmle : ∀ c ∈ C, m ≤ Nd L c := fun c hc => hmin hc
  have hleM : ∀ c ∈ C, Nd L c ≤ M := fun c hc => hmax hc

  obtain ⟨VH, hVH, hVHb⟩ :=
    AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
      K L σ D μHf (a / M) (b / m) (div_pos ha hM0)

  set C₁ : Set (G1 K L D σ) := Subtype.val ⁻¹' C with hC₁
  have hC₁c : IsCompact C₁ :=
    (isClosed_G1 K L D σ).isClosedEmbedding_subtypeVal.isCompact_preimage hCc
  set PG : Set (G1 K L D σ) := (H1 K L D σ : Set (G1 K L D σ)) * C₁ with hPG
  have hPGc : IsClosed PG := hHc.mul_right_of_isCompact hC₁c
  have hPGm : MeasurableSet PG := hPGc.measurableSet
  obtain ⟨Kc, hKc, hK1⟩ := exists_compact_mem_nhds (1 : G1 K L D σ)
  set O : Set (G1 K L D σ) := interior Kc with hO
  have hOo : IsOpen O := isOpen_interior
  have hO1 : (1 : G1 K L D σ) ∈ O := mem_interior_iff_mem_nhds.mpr hK1
  set U : Set (G1 K L D σ) := O * C₁ with hU
  have hUo : IsOpen U := hOo.mul_right
  have hUm : MeasurableSet U := hUo.measurableSet
  have hUfin : μ₁ U < ⊤ := by
    refine lt_of_le_of_lt (measure_mono ?_) (hKc.mul hC₁c).measure_lt_top
    exact Set.mul_subset_mul_right interior_subset

  set OH : Set (H1 K L D σ) := {x | (x : G1 K L D σ) ∈ O} with hOH
  have hOHo : IsOpen OH := hOo.preimage continuous_subtype_val
  have hm₀ : 0 < μH1 OH := hOHo.measure_pos μH1 ⟨1, by show ((1 : H1 K L D σ) : G1 K L D σ) ∈ O; exact hO1⟩

  set ν := HaarQuotient.measure μ₁ (H1 K L D σ) μH1 with hν
  have hW : ∀ (T : Set (G1 K L D σ)), MeasurableSet T →
      μ₁ T = ∫⁻ q, μH1 {x : H1 K L D σ | (x : G1 K L D σ) * q.out ∈ T} ∂ν := by
    intro T hT
    rw [← lintegral_indicator_one hT,
      HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ₁ (H1 K L D σ) hHc μH1 _
        (measurable_one.indicator hT)]
    refine lintegral_congr fun q => ?_
    exact lintegral_indicator_mul_eq (H1 K L D σ) μH1 hT q.out
  have hslm : ∀ (T : Set (G1 K L D σ)), MeasurableSet T →
      Measurable fun q : MulAction.orbitRel.Quotient (H1 K L D σ) (G1 K L D σ) =>
        μH1 {x : H1 K L D σ | (x : G1 K L D σ) * q.out ∈ T} := by
    intro T hT
    have := HaarQuotient.measurable_lintegral_mul_out (H1 K L D σ) hHc μH1 _ (measurable_one.indicator hT)
    simp_rw [lintegral_indicator_mul_eq (H1 K L D σ) μH1 hT] at this
    exact this

  have hPGinv : ∀ (x₀ : H1 K L D σ) (y : G1 K L D σ), (x₀ : G1 K L D σ) * y ∈ PG ↔ y ∈ PG := by
    intro x₀ y
    constructor
    · rintro ⟨x, hx, c, hc, hxy⟩
      have hxy' : x * c = (x₀ : G1 K L D σ) * y := hxy
      refine ⟨(x₀ : G1 K L D σ)⁻¹ * x, (H1 K L D σ).mul_mem ((H1 K L D σ).inv_mem x₀.2) hx, c, hc, ?_⟩
      show (x₀ : G1 K L D σ)⁻¹ * x * c = y
      rw [mul_assoc, hxy', inv_mul_cancel_left]
    · rintro ⟨x, hx, c, hc, hxy⟩
      have hxy' : x * c = y := hxy
      refine ⟨(x₀ : G1 K L D σ) * x, (H1 K L D σ).mul_mem x₀.2 hx, c, hc, ?_⟩
      show (x₀ : G1 K L D σ) * x * c = (x₀ : G1 K L D σ) * y
      rw [mul_assoc, hxy']

  have hPGim : Measurable fun q : MulAction.orbitRel.Quotient (H1 K L D σ) (G1 K L D σ) =>
      PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out := by
    refine measurable_comp_out (measurable_one.indicator hPGm) fun x g => ?_
    by_cases hg : g ∈ PG
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hPGinv x g).mpr hg)]; rfl
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hPGinv x g).mp h))]
  have hνPG : ∫⁻ q, PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out ∂ν ≤ μ₁ U / μH1 OH := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm₀.ne') (Or.inr hUfin.ne), ← lintegral_mul_const _ hPGim,
      hW U hUm]
    refine lintegral_mono fun q => ?_
    by_cases hq : q.out ∈ PG
    · have hq0 := hq
      obtain ⟨x₀, hx₀, c₁, hc₁, hq'⟩ := hq
      rw [Set.indicator_of_mem hq0, Pi.one_apply, one_mul]
      have hsub : (fun x : H1 K L D σ => x * ⟨x₀, hx₀⟩) ⁻¹' OH ⊆
          {x : H1 K L D σ | (x : G1 K L D σ) * q.out ∈ U} := by
        intro x hx
        simp only [Set.mem_preimage, hOH, Set.mem_setOf_eq, Subgroup.coe_mul] at hx
        show (x : G1 K L D σ) * q.out ∈ O * C₁
        rw [← hq', ← mul_assoc]
        exact Set.mul_mem_mul hx hc₁
      calc μH1 OH = μH1 ((fun x : H1 K L D σ => x * ⟨x₀, hx₀⟩) ⁻¹' OH) :=
            (measure_preimage_mul_right μH1 _ _).symm
        _ ≤ _ := measure_mono hsub
    · rw [Set.indicator_of_notMem hq, zero_mul]; exact zero_le

  haveI : Countable Lˣ := countable_units L
  haveI : Countable (GL (Fin 2) L) := countable_GL L
  haveI : Countable (Lˣ ⧸ Kfix K L σ) :=
    Function.Surjective.countable (QuotientGroup.mk_surjective (s := Kfix K L σ))
  set rep : Lˣ ⧸ Kfix K L σ → Lˣ := Quotient.out with hrep
  have hrep_mk : ∀ r : Lˣ ⧸ Kfix K L σ, (QuotientGroup.mk (rep r) : Lˣ ⧸ Kfix K L σ) = r := fun r =>
    QuotientGroup.out_eq' r
  have hrep_inj : ∀ r r' : Lˣ ⧸ Kfix K L σ, (rep r')⁻¹ * rep r ∈ Kfix K L σ → r = r' := by
    intro r r' h
    rw [← hrep_mk r, ← hrep_mk r']
    exact (QuotientGroup.eq.mpr h).symm

  set jj : Lˣ → G1 K L D σ := fun t => ⟨sc L t, sc_mem_G1 K L D σ t⟩ with hjj
  have hjj_coe : ∀ t, ((jj t : G1 K L D σ) : GG L) = sc L t := fun t => rfl

  have hcover : ∀ g : G1 K L D σ, ∃ r : Lˣ ⧸ Kfix K L σ, g * (jj (rep r))⁻¹ ∈ PG := by
    intro g
    obtain ⟨h, c, l, hh, hc, hg⟩ := hdec g ((mem_G1_iff K L D σ).mp g.2)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (Kfix K L σ) l
    refine ⟨QuotientGroup.mk l, ?_⟩
    have hrepl : rep (QuotientGroup.mk l) = l * k := hk
    have hkfix : ι L (rsc L (k : Lˣ)) ∈ Hf K L D σ := ι_mem_Hf K L D σ (map_rsc_of_mem_Kfix K L σ k.2)
    have hhH : h ∈ Hf K L D σ := (mem_Hf_iff K L D σ).mpr hh
    have h1H : h * (sc L (k : Lˣ))⁻¹ ∈ Hf K L D σ := (Hf K L D σ).mul_mem hhH ((Hf K L D σ).inv_mem hkfix)
    refine ⟨⟨h * (sc L (k : Lˣ))⁻¹, Hf_le_G1 K L D σ h1H⟩, (mem_H1_iff K L D σ).mpr h1H,
      ⟨c, center_le_G1 K L D σ (hCZ hc)⟩, hc, Subtype.ext ?_⟩
    show h * (sc L (k : Lˣ))⁻¹ * c = (g : GG L) * (sc L (rep (QuotientGroup.mk l)))⁻¹
    rw [hrepl, hg]
    show h * (sc L (k : Lˣ))⁻¹ * c = h * c * sc L l * (ι L (rsc L (l * k)))⁻¹
    have hck : (sc L (k : Lˣ))⁻¹ = sc L (k⁻¹ : Lˣ) := by
      show (ι L (Matrix.GeneralLinearGroup.scalar (Fin 2) (k : Lˣ)))⁻¹ =
        ι L (Matrix.GeneralLinearGroup.scalar (Fin 2) ((k : Lˣ)⁻¹))
      rw [map_inv, map_inv]
    have hlk : (ι L (rsc L (l * k)))⁻¹ = sc L (k⁻¹ : Lˣ) * (sc L l)⁻¹ := by
      show (ι L (Matrix.GeneralLinearGroup.scalar (Fin 2) (l * (k : Lˣ))))⁻¹ = _
      rw [map_mul, map_mul, mul_inv_rev, ← hck]
    rw [hlk, hck, mul_assoc h, ← sc_comm L (k⁻¹ : Lˣ) c, ← mul_assoc, mul_assoc (h * c),
      ← mul_assoc (sc L l), sc_comm L (k⁻¹ : Lˣ) (sc L l), mul_assoc (sc L (k⁻¹ : Lˣ)),
      mul_inv_cancel, mul_one]

  refine ⟨VH * (μ₁ U / μH1 OH), ENNReal.mul_lt_top hVH (ENNReal.div_lt_top hUfin.ne hm₀.ne'), ?_⟩
  intro E hEslab hE hpack
  set E' : Set (G1 K L D σ) := Subtype.val ⁻¹' E with hE'
  have hE'm : MeasurableSet E' := measurable_subtype_coe hE

  set f : G1 K L D σ → ℝ≥0∞ := fun g => μH1 {x : H1 K L D σ | (x : G1 K L D σ) * g ∈ E'} with hf
  have hfm : Measurable f := by
    have h := measurable_slice (H1 K L D σ) μH1 hE'm
    simp_rw [lintegral_indicator_mul_eq (H1 K L D σ) μH1 hE'm] at h
    exact h
  have hfinv : ∀ (x : H1 K L D σ) (g : G1 K L D σ), f ((x : G1 K L D σ) * g) = f g := fun x g =>
    slice_mul_left (H1 K L D σ) μH1 x g

  set Φ : Lˣ ⧸ Kfix K L σ → G1 K L D σ → ℝ≥0∞ := fun r g =>
    PG.indicator (1 : G1 K L D σ → ℝ≥0∞) (g * (jj (rep r))⁻¹) * f g with hΦ
  have hΦm : ∀ r, Measurable (Φ r) := fun r =>
    ((measurable_one.indicator hPGm).comp (measurable_mul_const _)).mul hfm
  have hΦinv : ∀ r (x : H1 K L D σ) (g : G1 K L D σ), Φ r ((x : G1 K L D σ) * g) = Φ r g := by
    intro r x g
    show PG.indicator 1 ((x : G1 K L D σ) * g * (jj (rep r))⁻¹) * f ((x : G1 K L D σ) * g) =
      PG.indicator 1 (g * (jj (rep r))⁻¹) * f g
    rw [hfinv, mul_assoc]
    by_cases hg : g * (jj (rep r))⁻¹ ∈ PG
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hPGinv x _).mpr hg)]; rfl
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hPGinv x _).mp h))]
  set Ψ : Lˣ ⧸ Kfix K L σ → G1 K L D σ → ℝ≥0∞ := fun r g =>
    PG.indicator (1 : G1 K L D σ → ℝ≥0∞) g * f (g * jj (rep r)) with hΨ
  have hΨm : ∀ r, Measurable (Ψ r) := fun r =>
    (measurable_one.indicator hPGm).mul (hfm.comp (measurable_mul_const _))
  have hΨinv : ∀ r (x : H1 K L D σ) (g : G1 K L D σ), Ψ r ((x : G1 K L D σ) * g) = Ψ r g := by
    intro r x g
    show PG.indicator 1 ((x : G1 K L D σ) * g) * f ((x : G1 K L D σ) * g * jj (rep r)) =
      PG.indicator 1 g * f (g * jj (rep r))
    rw [mul_assoc, hfinv]
    by_cases hg : g ∈ PG
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hPGinv x _).mpr hg)]; rfl
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hPGinv x _).mp h))]
  have hstep1 : μ₁ E' ≤ ∫⁻ q, PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out *
      ∑' r : Lˣ ⧸ Kfix K L σ, f (q.out * jj (rep r)) ∂ν := by
    rw [hW E' hE'm]
    calc ∫⁻ q, μH1 {x : H1 K L D σ | (x : G1 K L D σ) * q.out ∈ E'} ∂ν
        = ∫⁻ q, f q.out ∂ν := rfl
      _ ≤ ∫⁻ q, ∑' r, Φ r q.out ∂ν := by
          refine lintegral_mono fun q => ?_
          obtain ⟨r₀, hr₀⟩ := hcover q.out
          refine le_trans ?_ (ENNReal.le_tsum r₀)
          show f q.out ≤ PG.indicator 1 (q.out * (jj (rep r₀))⁻¹) * f q.out
          rw [Set.indicator_of_mem hr₀, Pi.one_apply, one_mul]
      _ = ∑' r, ∫⁻ q, Φ r q.out ∂ν :=
          lintegral_tsum fun r => (measurable_comp_out (hΦm r) (hΦinv r)).aemeasurable
      _ = ∑' r, ∫⁻ q, Φ r (q.out * jj (rep r)) ∂ν := by
          refine tsum_congr fun r => ?_
          exact (lintegral_quot_comp_mul_right μ₁ (H1 K L D σ) hHc μH1 (Φ r) (hΦm r) (hΦinv r)
            (jj (rep r))).symm
      _ = ∑' r, ∫⁻ q, PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out * f (q.out * jj (rep r)) ∂ν := by
          refine tsum_congr fun r => lintegral_congr fun q => ?_
          show PG.indicator 1 (q.out * jj (rep r) * (jj (rep r))⁻¹) * f (q.out * jj (rep r)) = _
          rw [mul_inv_cancel_right]
      _ = ∫⁻ q, ∑' r, PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out * f (q.out * jj (rep r)) ∂ν := by
          refine (lintegral_tsum fun r => ?_).symm
          exact (measurable_comp_out (hΨm r) (hΨinv r)).aemeasurable
      _ = _ := by
          refine lintegral_congr fun q => ?_
          rw [ENNReal.tsum_mul_left]

  set PS := {p : GL (Fin 2) L × GL (Fin 2) L // InS K L σ p.1 ∧ InS K L σ p.2 ∧ p.1 ≠ p.2} with hPS
  haveI : Countable PS := Subtype.countable
  set T : PS → Set (G1 K L D σ) := fun p => Subtype.val ⁻¹' (ι L p.1.1 • E ∩ ι L p.1.2 • E) with hT
  have hTm : ∀ p, MeasurableSet (T p) := fun p =>
    measurable_subtype_coe ((hE.const_smul _).inter (hE.const_smul _))
  have hnull : ∀ p : PS, ∀ᵐ q ∂ν, μH1 {x : H1 K L D σ | (x : G1 K L D σ) * q.out ∈ T p} = 0 := by
    intro p
    have h0 : μ₁ (T p) = 0 := hpack p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2
    rw [hW (T p) (hTm p)] at h0
    have h1 := (lintegral_eq_zero_iff (hslm (T p) (hTm p))).mp h0
    exact h1.mono fun q hq => hq
  have hgood : ∀ᵐ q ∂ν, ∀ p : PS, μH1 {x : H1 K L D σ | (x : G1 K L D σ) * q.out ∈ T p} = 0 :=
    ae_all_iff.mpr hnull
  have hae : ∀ᵐ q ∂ν, ∑' r : Lˣ ⧸ Kfix K L σ, f (q.out * jj (rep r)) ≤ VH := by
    refine hgood.mono fun q hq => ?_

    obtain ⟨h, c, l, hh, hc, hg⟩ := hdec q.out ((mem_G1_iff K L D σ).mp q.out.2)
    have hhH : h ∈ Hf K L D σ := (mem_Hf_iff K L D σ).mpr hh
    set x₀ : H1 K L D σ := ⟨⟨h, Hf_le_G1 K L D σ hhH⟩, (mem_H1_iff K L D σ).mpr hhH⟩ with hx₀
    set c₁ : G1 K L D σ := ⟨c, center_le_G1 K L D σ (hCZ hc)⟩ with hc₁
    have hgeq : q.out = (x₀ : G1 K L D σ) * (c₁ * jj l) :=
      Subtype.ext (by rw [hg, Subgroup.coe_mul, Subgroup.coe_mul]; exact mul_assoc _ _ _)
    have hcpos : 0 < Nd L c := NumberField.TateGlobal.ideleNorm_pos (F := L) _

    have hKS : ∀ (t : Lˣ) (A : Set (GG L)), MeasurableSet A →
        μH1 {x : H1 K L D σ | (x : G1 K L D σ) * (q.out * jj t) ∈ Subtype.val ⁻¹' A} =
          μHf {y : Hf K L D σ | (y : GG L) * c ∈ (sc L (l * t))⁻¹ • A} := by
      intro t A hA
      have hAm : MeasurableSet (Subtype.val ⁻¹' A : Set (G1 K L D σ)) := measurable_subtype_coe hA
      have e1 : {x : H1 K L D σ | (x : G1 K L D σ) * (q.out * jj t) ∈ Subtype.val ⁻¹' A} =
          {x : H1 K L D σ | (x : G1 K L D σ) * ((x₀ : G1 K L D σ) * (c₁ * jj l * jj t)) ∈
            Subtype.val ⁻¹' A} := by
        rw [hgeq]; simp only [mul_assoc]
      rw [e1, slice_mul_left (H1 K L D σ) μH1 x₀ (c₁ * jj l * jj t),
        ← htrans (fun z => z * c ∈ (sc L (l * t))⁻¹ • A)]
      congr 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Subgroup.coe_mul, hjj_coe]
      rw [mem_sc_inv_smul_iff, ← sc_comm L (l * t) (((x : G1 K L D σ) : GG L) * c), sc_mul]
      show ((x : G1 K L D σ) : GG L) * (c * sc L l * sc L t) ∈ A ↔
        ((x : G1 K L D σ) : GG L) * c * (sc L l * sc L t) ∈ A
      simp only [mul_assoc]

    have hjj1 : jj 1 = 1 := Subtype.ext (sc_one L)
    have hnullc : ∀ u u' : GL (Fin 2) L, InS K L σ u → InS K L σ u' → u ≠ u' →
        μHf {y : Hf K L D σ | (y : GG L) * c ∈ ι L u • E ∩ ι L u' • E} = 0 := by
      intro u u' hu hu' hne
      have hne' : rsc L l * u ≠ rsc L l * u' := fun h => hne (mul_left_cancel h)
      let p : PS := ⟨(rsc L l * u, rsc L l * u'), inS_rsc_mul K L σ l hu, inS_rsc_mul K L σ l hu', hne'⟩
      have h0 := hq p
      have h1 := hKS 1 (ι L (rsc L l * u) • E ∩ ι L (rsc L l * u') • E)
        ((hE.const_smul _).inter (hE.const_smul _))
      rw [hjj1, mul_one, mul_one] at h1
      have h2 : (sc L l)⁻¹ • (ι L (rsc L l * u) • E ∩ ι L (rsc L l * u') • E) = ι L u • E ∩ ι L u' • E := by
        rw [Set.smul_set_inter, sc_inv_smul_smul, sc_inv_smul_smul, inv_mul_cancel_left,
          inv_mul_cancel_left]
      rw [h2] at h1
      rw [← h1]
      exact h0

    set B : Lˣ ⧸ Kfix K L σ → Set (Hf K L D σ) := fun r =>
      {y : Hf K L D σ | (y : GG L) * c ∈ (sc L (l * rep r))⁻¹ • E} with hB
    have hfB : ∀ r, f (q.out * jj (rep r)) = μHf (B r) := fun r => hKS (rep r) E hE
    have hBm : ∀ r, MeasurableSet (B r) := fun r =>
      measurableSet_preimage (measurable_subtype_coe.mul_const c) (hE.const_smul _)
    have hBalt : ∀ r, B r = {y : Hf K L D σ | (y : GG L) * c ∈ ι L (rsc L (l * rep r))⁻¹ • E} := by
      intro r; simp only [hB, sc_inv_eq]
    have hBdisj : Pairwise (Function.onFun (AEDisjoint μHf) B) := by
      intro r r' hne
      show μHf (B r ∩ B r') = 0
      rw [hBalt r, hBalt r']
      have hne' : (rsc L (l * rep r))⁻¹ ≠ (rsc L (l * rep r'))⁻¹ := by
        intro h
        have h1 : l * rep r = l * rep r' := rsc_injective L (inv_injective h)
        have h2 : rep r = rep r' := mul_left_cancel h1
        exact hne (by rw [← hrep_mk r, ← hrep_mk r', h2])
      exact hnullc _ _ (inS_rsc_inv K L σ _) (inS_rsc_inv K L σ _) hne'
    have hsum : ∑' r, μHf (B r) = μHf (⋃ r, B r) :=
      (measure_iUnion₀ hBdisj fun r => (hBm r).nullMeasurableSet).symm

    set F : Set (GG L) := ⋃ r : Lˣ ⧸ Kfix K L σ, (sc L (l * rep r))⁻¹ • E with hF
    have hFm : MeasurableSet F := MeasurableSet.iUnion fun r => hE.const_smul _
    set EH : Set (GG L) := {z | z * c ∈ F} with hEH
    have hEHm : MeasurableSet EH := measurableSet_preimage (measurable_id.mul_const c) hFm
    have hUB : (⋃ r, B r) = Subtype.val ⁻¹' EH := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_preimage, hEH, Set.mem_setOf_eq, hB, hF]
    have hEHslab : EH ⊆ {z | Nd L z ∈ Set.Icc (a / M) (b / m)} := by
      intro z hz
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hz
      rw [mem_sc_inv_smul_iff] at hr
      have h1 := hEslab hr
      simp only [Set.mem_setOf_eq, Nd_mul, Nd_sc, one_mul] at h1
      obtain ⟨h1, h2⟩ := h1
      have hb : 0 ≤ b := le_trans (le_trans ha.le h1) h2
      refine ⟨le_trans (div_le_div_of_nonneg_left ha.le hcpos (hleM c hc)) ((div_le_iff₀ hcpos).mpr h1),
        le_trans ((le_div_iff₀ hcpos).mpr h2) (div_le_div_of_nonneg_left hb hm0 (hmle c hc))⟩
    have hEHpack : ∀ s s' : GL (Fin 2) L,
        Matrix.GeneralLinearGroup.map (σ : L →+* L) s = s →
        Matrix.GeneralLinearGroup.map (σ : L →+* L) s' = s' → s ≠ s' →
          μHf (Subtype.val ⁻¹' (ι L s • EH ∩ ι L s' • EH)) = 0 := by
      intro s s' hs hs' hne
      have hsub : Subtype.val ⁻¹' (ι L s • EH ∩ ι L s' • EH) ⊆
          ⋃ pr : (Lˣ ⧸ Kfix K L σ) × (Lˣ ⧸ Kfix K L σ),
            {y : Hf K L D σ | (y : GG L) * c ∈
              ι L (s * (rsc L (l * rep pr.1))⁻¹) • E ∩ ι L (s' * (rsc L (l * rep pr.2))⁻¹) • E} := by
        rintro y ⟨hy1, hy2⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hy1 hy2
        obtain ⟨r₁, hr₁⟩ := Set.mem_iUnion.mp (show (ι L s)⁻¹ * (y : GG L) * c ∈ F from hy1)
        obtain ⟨r₂, hr₂⟩ := Set.mem_iUnion.mp (show (ι L s')⁻¹ * (y : GG L) * c ∈ F from hy2)
        refine Set.mem_iUnion.mpr ⟨(r₁, r₂), ?_, ?_⟩
        · rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, ← map_inv, mul_inv_rev, inv_inv, map_mul,
            mul_assoc, ← mul_assoc _ (y : GG L) c]
          rw [mem_sc_inv_smul_iff] at hr₁
          exact hr₁
        · rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, ← map_inv, mul_inv_rev, inv_inv, map_mul,
            mul_assoc, ← mul_assoc _ (y : GG L) c]
          rw [mem_sc_inv_smul_iff] at hr₂
          exact hr₂
      refine measure_mono_null hsub (measure_iUnion_null fun pr => ?_)
      have hu : InS K L σ (s * (rsc L (l * rep pr.1))⁻¹) := by
        have := inS_of_fixed_mul_rsc K L σ hs (l * rep pr.1)⁻¹
        rwa [show rsc L (l * rep pr.1)⁻¹ = (rsc L (l * rep pr.1))⁻¹ from map_inv _ _] at this
      have hu' : InS K L σ (s' * (rsc L (l * rep pr.2))⁻¹) := by
        have := inS_of_fixed_mul_rsc K L σ hs' (l * rep pr.2)⁻¹
        rwa [show rsc L (l * rep pr.2)⁻¹ = (rsc L (l * rep pr.2))⁻¹ from map_inv _ _] at this
      refine hnullc _ _ hu hu' fun heq => ?_
      have hk := mem_Kfix_of_eq K L σ hs hs' heq
      have hk' : (rep pr.2)⁻¹ * rep pr.1 ∈ Kfix K L σ := by
        have e : (l * rep pr.2)⁻¹ * (l * rep pr.1) = (rep pr.2)⁻¹ * rep pr.1 := by group
        rwa [e] at hk
      have hr : pr.1 = pr.2 := hrep_inj pr.1 pr.2 hk'
      rw [hr] at heq
      exact hne (mul_right_cancel heq)
    have hbound := hVHb EH hEHslab hEHm hEHpack
    calc ∑' r, f (q.out * jj (rep r)) = ∑' r, μHf (B r) := tsum_congr hfB
      _ = μHf (⋃ r, B r) := hsum
      _ = μHf (Subtype.val ⁻¹' EH) := by rw [hUB]
      _ ≤ VH := hbound

  calc μ₁ E' ≤ ∫⁻ q, PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out *
        ∑' r : Lˣ ⧸ Kfix K L σ, f (q.out * jj (rep r)) ∂ν := hstep1
    _ ≤ ∫⁻ q, PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out * VH ∂ν :=
        lintegral_mono_ae (hae.mono fun q hq => mul_le_mul_right hq _)
    _ = (∫⁻ q, PG.indicator (1 : G1 K L D σ → ℝ≥0∞) q.out ∂ν) * VH := lintegral_mul_const VH hPGim
    _ ≤ (μ₁ U / μH1 OH) * VH := mul_le_mul_left hνPG VH
    _ = VH * (μ₁ U / μH1 OH) := mul_comm _ _

end Main

end R4VRed

open MeasureTheory NumberField
open scoped ENNReal Pointwise

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    [MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    [BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    (μH : Measure (MonoidHom.eqLocus
        ((QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L))).comp
          (AutomorphicForm.sigmaAdelicAct K L D σ))
        (QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))))
    [μH.IsHaarMeasure] (a b : ℝ) (ha : 0 < a) :
    ∃ V₀ : ℝ≥0∞, V₀ < ⊤ ∧
      ∀ E : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L),
        E ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
        MeasurableSet E →
        (∀ s s' : GL (Fin 2) L,
          (∃ u : Lˣ, s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s =
            Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
          (∃ u : Lˣ, s'⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s' =
            Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
          s ≠ s' →
            μH (Subtype.val ⁻¹'
              (AutomorphicForm.globalPoints (𝓞 L) L s • E ∩
                AutomorphicForm.globalPoints (𝓞 L) L s' • E)) = 0) →
        μH (Subtype.val ⁻¹' E) ≤ V₀ :=
  R4VRed.main K L D σ μH a b ha

end

end S_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
end P2MW
export P2MW.S_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center (solution)
