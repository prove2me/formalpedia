-- Prove2me | solution 1 for AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c42f120b-cb09-5a9a-84c5-daa55fbc760e

import Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
import Theorems.Thm_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b"
p2m_attr_erase "simp" "AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply"
p2m_attr_erase "simp" "Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

noncomputable section

namespace R3TubeRed

open MeasureTheory NumberField NumberField.AdelicHaar Filter Function Set
open scoped ENNReal NNReal Topology Pointwise

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

attribute [local instance] NumberField.AdelicHaar.glBorel

abbrev H1 : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  MonoidHom.eqLocus
    ((QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L))).comp
      (AutomorphicForm.sigmaAdelicAct K L D σ))
    (QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))

theorem mem_H1_iff {g : AutomorphicForm.AdelicGL2 (𝓞 L) L} :
    g ∈ H1 K L D σ ↔ g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g ∈
      Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  show (QuotientGroup.mk' _ (AutomorphicForm.sigmaAdelicAct K L D σ g) = QuotientGroup.mk' _ g) ↔ _
  rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]

theorem isClosed_center : IsClosed (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
  have h : (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) =
      ⋂ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

theorem isClosed_H1 : IsClosed (H1 K L D σ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
  have h : (H1 K L D σ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) =
      (fun g => g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g) ⁻¹'
        (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
    ext g; exact mem_H1_iff K L D σ
  rw [h]
  exact (isClosed_center L).preimage (continuous_id.inv.mul (AutomorphicForm.continuous_sigmaAdelicAct K L D σ))

theorem tube_eq_mul (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
    {g | ∃ g₁ k : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        g₁⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g₁ ∈
            Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) ∧ k ∈ C ∧ g = g₁ * k} =
      (H1 K L D σ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * C := by
  ext g
  constructor
  · rintro ⟨g₁, k, hg₁, hk, rfl⟩
    exact Set.mul_mem_mul ((mem_H1_iff K L D σ).mpr hg₁) hk
  · rintro ⟨g₁, hg₁, k, hk, rfl⟩
    exact ⟨g₁, k, (mem_H1_iff K L D σ).mp hg₁, hk, rfl⟩

section Slices

variable {G : Type*} [Group G]

theorem exists_out_eq (H : Subgroup G) (v : G) :
    ∃ h : H, (Quotient.mk'' v : MulAction.orbitRel.Quotient H G).out = (h : G) * v := by
  have hrel : MulAction.orbitRel H G ((Quotient.mk'' v : MulAction.orbitRel.Quotient H G).out) v :=
    Quotient.mk_out' v
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨h, hh⟩ := hrel
  exact ⟨h, hh.symm⟩

theorem preimage_mk_image (H : Subgroup G) (C : Set G) :
    (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹'
        ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' C) = (H : Set G) * C := by
  ext g
  constructor
  · rintro ⟨v, hv, hgv⟩
    have hrel : MulAction.orbitRel H G v g := Quotient.eq''.mp hgv
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨h, rfl⟩ := hrel

    refine Set.mem_mul.mpr ⟨((h⁻¹ : H) : G), (h⁻¹).2, (h : G) * g, hv, ?_⟩
    rw [Subgroup.coe_inv, inv_mul_cancel_left]
  · rintro ⟨h, hh, v, hv, rfl⟩
    refine ⟨v, hv, Quotient.sound' ?_⟩
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨⟨h, hh⟩⁻¹, ?_⟩
    change (((⟨h, hh⟩ : H)⁻¹ : H) : G) * (h * v) = v
    rw [Subgroup.coe_inv]
    exact inv_mul_cancel_left h v

end Slices

section Main

theorem main (α β : ℝ) (hα : 0 < α)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C)
    (F : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hFs : F ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFm : MeasurableSet F)
    (hF : ∀ s s' : GL (Fin 2) L,
      (∃ u : Lˣ, s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      (∃ u : Lˣ, s'⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s' =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      s ≠ s' →
        adelicGLHaar (Fin 2) (𝓞 L) L
          (AutomorphicForm.globalPoints (𝓞 L) L s • F ∩
            AutomorphicForm.globalPoints (𝓞 L) L s' • F) = 0) :
    adelicGLHaar (Fin 2) (𝓞 L) L
        (F ∩ {g | ∃ g₁ k : AutomorphicForm.AdelicGL2 (𝓞 L) L,
          g₁⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g₁ ∈
              Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) ∧
            k ∈ C ∧ g = g₁ * k}) < ⊤ := by

  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι
  set Nd : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ := fun g =>
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) with hNd
  have hNdc : Continuous Nd := NumberField.TateGlobal.continuous_ideleNorm_det L
  rw [tube_eq_mul K L D σ C]

  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · rw [hC0, Set.mul_empty, Set.inter_empty, measure_empty]; exact ENNReal.zero_lt_top

  obtain ⟨k₀, hk₀, hmin⟩ := hC.exists_isMinOn hCne hNdc.continuousOn
  obtain ⟨k₁, hk₁, hmax⟩ := hC.exists_isMaxOn hCne hNdc.continuousOn
  set m := Nd k₀ with hm
  set M := Nd k₁ with hM
  have hm0 : 0 < m := NumberField.TateGlobal.ideleNorm_pos (F := L) _
  have hM0 : 0 < M := NumberField.TateGlobal.ideleNorm_pos (F := L) _
  have hmle : ∀ k ∈ C, m ≤ Nd k := fun k hk => hmin hk
  have hleM : ∀ k ∈ C, Nd k ≤ M := fun k hk => hmax hk

  set H := H1 K L D σ with hH
  have hHc : IsClosed (H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := isClosed_H1 K L D σ
  haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set μH : Measure H := Measure.haar with hμH
  haveI : μH.IsHaarMeasure := by rw [hμH]; exact Measure.isHaarMeasure_haarMeasure _
  haveI : μH.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center K L σ D μH
  obtain ⟨V₀, hV₀, hV⟩ :=
    AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
      K L σ D μH (α / M) (β / m) (div_pos hα hM0)
  set ν : Measure (MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :=
    HaarQuotient.measure μ H μH with hν

  have hslice_meas : ∀ (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)), MeasurableSet S →
      ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, MeasurableSet {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * g ∈ S} :=
    fun S hS g => measurableSet_preimage (continuous_subtype_val.mul continuous_const).measurable hS
  have hinner : ∀ (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)), MeasurableSet S →
      ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        ∫⁻ x : H, S.indicator (1 : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ≥0∞) ((x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * g) ∂μH =
          μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * g ∈ S} := by
    intro S hS g
    rw [← lintegral_indicator_one (hslice_meas S hS g)]
    rfl
  have hW : ∀ (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)), MeasurableSet S →
      μ S = ∫⁻ q, μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ S} ∂ν := by
    intro S hS
    rw [← lintegral_indicator_one hS,
      HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hHc μH _ (measurable_one.indicator hS)]
    simp_rw [hinner S hS]
    rfl
  have hWm : ∀ (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)), MeasurableSet S →
      Measurable fun q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
        μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ S} := by
    intro S hS
    have h := HaarQuotient.measurable_lintegral_mul_out H hHc μH _ (measurable_one.indicator hS)
    simp_rw [hinner S hS] at h
    exact h

  have hslice_eq : ∀ (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (h₀ : H) (v : AutomorphicForm.AdelicGL2 (𝓞 L) L),
      μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * ((h₀ : AutomorphicForm.AdelicGL2 (𝓞 L) L) * v) ∈ S} =
        μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * v ∈ S} := by
    intro S h₀ v
    have hset : {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * ((h₀ : AutomorphicForm.AdelicGL2 (𝓞 L) L) * v) ∈ S} =
        (fun x : H => x * h₀) ⁻¹' {y : H | (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) * v ∈ S} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Subgroup.coe_mul, mul_assoc]
    rw [hset, measure_preimage_mul_right]

  set IsS : GL (Fin 2) L → Prop := fun s => ∃ u : Lˣ,
    s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s = Matrix.GeneralLinearGroup.scalar (Fin 2) u with hIsS

  haveI : Countable (GL (Fin 2) L) := by
    haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
    haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
    exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective
  have hN_meas : ∀ s s' : GL (Fin 2) L, MeasurableSet (ι s • F ∩ ι s' • F) := fun s s' =>
    (hFm.const_smul (ι s)).inter (hFm.const_smul (ι s'))
  have hae : ∀ᵐ q ∂ν, ∀ s s' : GL (Fin 2) L, IsS s → IsS s' → s ≠ s' →
      μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ ι s • F ∩ ι s' • F} = 0 := by
    refine ae_all_iff.mpr fun s => ae_all_iff.mpr fun s' => ?_
    by_cases hs : IsS s
    swap; · exact Eventually.of_forall fun q h => absurd h hs
    by_cases hs' : IsS s'
    swap; · exact Eventually.of_forall fun q _ h => absurd h hs'
    by_cases hne : s = s'
    · exact Eventually.of_forall fun q _ _ h => absurd hne h
    have h0 : μ (ι s • F ∩ ι s' • F) = 0 := hF s s' hs hs' hne
    rw [hW _ (hN_meas s s')] at h0
    have hae0 := (lintegral_eq_zero_iff (hWm _ (hN_meas s s'))).mp h0
    filter_upwards [hae0] with q hq
    intro _ _ _
    exact hq

  set A : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := F ∩ ((H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * C) with hA
  have hHCc : IsClosed ((H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * C) := hHc.mul_right_of_isCompact hC
  have hAm : MeasurableSet A := hFm.inter hHCc.measurableSet
  set Q : Set (MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :=
    (Quotient.mk'' : AutomorphicForm.AdelicGL2 (𝓞 L) L → _) '' C with hQ
  have hQm : MeasurableSet Q := by
    rw [hQ]
    refine measurableSet_quotient.mpr ?_
    rw [preimage_mk_image]
    exact hHCc.measurableSet
  have hbound : ∀ᵐ q ∂ν,
      μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ A} ≤ Q.indicator (fun _ => V₀) q := by
    filter_upwards [hae] with q hq
    by_cases hq' : q.out ∈ (H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * C
    · obtain ⟨h₀, hh₀, v, hv, hq0⟩ := Set.mem_mul.mp hq'
      have hqQ : q ∈ Q := by
        refine ⟨v, hv, ?_⟩
        rw [← Quotient.out_eq' q, ← hq0]
        refine Quotient.sound' ?_
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        refine ⟨⟨h₀, hh₀⟩⁻¹, ?_⟩
        change (((⟨h₀, hh₀⟩ : H)⁻¹ : H) : AutomorphicForm.AdelicGL2 (𝓞 L) L) * (h₀ * v) = v
        rw [Subgroup.coe_inv]
        exact inv_mul_cancel_left h₀ v
      rw [Set.indicator_of_mem hqQ, ← hq0]
      rw [show h₀ * v = ((⟨h₀, hh₀⟩ : H) : AutomorphicForm.AdelicGL2 (𝓞 L) L) * v from rfl, hslice_eq A ⟨h₀, hh₀⟩ v]

      set E : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := {g | g * v ∈ A} with hE
      have hEm : MeasurableSet E := measurableSet_preimage (continuous_id.mul continuous_const).measurable hAm
      have hNdv0 : 0 < Nd v := NumberField.TateGlobal.ideleNorm_pos (F := L) _
      have hEs : E ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈
          Set.Icc (α / M) (β / m)} := by
        intro g hg
        have hgv : g * v ∈ F := (hg : g * v ∈ A).1
        have hsl := hFs hgv
        simp only [Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul, Set.mem_Icc] at hsl
        change Nd g * Nd v ∈ Set.Icc α β at hsl
        have hαβ : α ≤ β := (hsl.1.trans hsl.2)
        have hβ0 : 0 ≤ β := hα.le.trans hαβ
        refine ⟨?_, ?_⟩
        ·
          calc α / M ≤ α / Nd v := div_le_div_of_nonneg_left hα.le hNdv0 (hleM v hv)
            _ ≤ Nd g := by rw [div_le_iff₀ hNdv0]; exact hsl.1
        · calc Nd g ≤ β / Nd v := by rw [le_div_iff₀ hNdv0]; exact hsl.2
            _ ≤ β / m := div_le_div_of_nonneg_left hβ0 hm0 (hmle v hv)
      have hEpack : ∀ s s' : GL (Fin 2) L, IsS s → IsS s' → s ≠ s' →
          μH (Subtype.val ⁻¹' (ι s • E ∩ ι s' • E)) = 0 := by
        intro s s' hs hs' hne
        have hsub : Subtype.val ⁻¹' (ι s • E ∩ ι s' • E) ⊆
            {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * v ∈ ι s • F ∩ ι s' • F} := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          rw [Set.mem_smul_set_iff_inv_smul_mem] at hx1 hx2
          refine ⟨?_, ?_⟩
          · rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, ← mul_assoc]
            exact ((hx1 : ((ι s)⁻¹ • (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)) * v ∈ A)).1
          · rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, ← mul_assoc]
            exact ((hx2 : ((ι s')⁻¹ • (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)) * v ∈ A)).1
        refine measure_mono_null hsub ?_
        rw [← hslice_eq _ ⟨h₀, hh₀⟩ v]
        change μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * (h₀ * v) ∈ ι s • F ∩ ι s' • F} = 0
        rw [hq0]
        exact hq s s' hs hs' hne
      exact hV E hEs hEm hEpack
    ·
      have hempty : {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ A} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => hq' ?_
        obtain ⟨g₁, hg₁, k, hk, hgk⟩ := Set.mem_mul.mp (hx : _ ∈ A).2
        refine Set.mem_mul.mpr ⟨(x : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * g₁, H.mul_mem (H.inv_mem x.2) hg₁, k, hk, ?_⟩
        rw [mul_assoc, hgk, inv_mul_cancel_left]
      rw [hempty, measure_empty]
      exact zero_le

  have hνQ : ν Q < ⊤ := by
    obtain ⟨Kc, hKc, h1⟩ := exists_compact_mem_nhds (1 : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    set O : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := interior Kc with hO
    have hOo : IsOpen O := isOpen_interior
    have h1O : (1 : AutomorphicForm.AdelicGL2 (𝓞 L) L) ∈ O := mem_interior_iff_mem_nhds.mpr h1
    set B : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := O * C with hB
    have hBm : MeasurableSet B := (hOo.mul_right).measurableSet
    have hBfin : μ B < ⊤ :=
      lt_of_le_of_lt (measure_mono (Set.mul_subset_mul_right interior_subset)) (hKc.mul hC).measure_lt_top
    set m₀ : ℝ≥0∞ := μH (Subtype.val ⁻¹' O) with hm₀
    have hm₀0 : m₀ ≠ 0 :=
      (hOo.preimage continuous_subtype_val).measure_ne_zero μH ⟨1, h1O⟩
    have hlow : ∀ q, Q.indicator (fun _ => m₀) q ≤
        μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ B} := by
      intro q
      by_cases hqQ : q ∈ Q
      · rw [Set.indicator_of_mem hqQ]
        obtain ⟨v, hv, hvq⟩ := hqQ
        obtain ⟨h₀, hh₀⟩ := exists_out_eq H v
        rw [← hvq, hh₀, hslice_eq B h₀ v]
        refine measure_mono fun x hx => ?_
        exact Set.mul_mem_mul hx hv
      · rw [Set.indicator_of_notMem hqQ]; exact zero_le
    have hle : m₀ * ν Q ≤ μ B := by
      rw [hW B hBm, ← lintegral_indicator_const hQm]
      exact lintegral_mono hlow
    have hlt : m₀ * ν Q < ⊤ := lt_of_le_of_lt hle hBfin
    rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
    · exact h.2
    · exact absurd h hm₀0
    · rw [h]; exact ENNReal.zero_lt_top

  calc μ (F ∩ ((H1 K L D σ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * C)) = μ A := rfl
    _ = ∫⁻ q, μH {x : H | (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ A} ∂ν := hW A hAm
    _ ≤ ∫⁻ q, Q.indicator (fun _ => V₀) q ∂ν := lintegral_mono_ae hbound
    _ = V₀ * ν Q := lintegral_indicator_const hQm _
    _ < ⊤ := ENNReal.mul_lt_top hV₀ hνQ

end Main

end R3TubeRed

end

section

attribute [local instance] NumberField.AdelicHaar.glBorel
open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal Pointwise

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (α β : ℝ) (hα : 0 < α)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C)
    (F : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hFs : F ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFm : MeasurableSet F)
    (hF : ∀ s s' : GL (Fin 2) L,
      (∃ u : Lˣ, s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      (∃ u : Lˣ, s'⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s' =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      s ≠ s' →
        adelicGLHaar (Fin 2) (𝓞 L) L
          (AutomorphicForm.globalPoints (𝓞 L) L s • F ∩
            AutomorphicForm.globalPoints (𝓞 L) L s' • F) = 0) :
    adelicGLHaar (Fin 2) (𝓞 L) L
        (F ∩ {g | ∃ g₁ k : AutomorphicForm.AdelicGL2 (𝓞 L) L,
          g₁⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g₁ ∈
              Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) ∧
            k ∈ C ∧ g = g₁ * k}) < ⊤ :=
  R3TubeRed.main K L D σ α β hα C hC F hFs hFm hF

end

end S_AutomorphicForm_adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
end P2MW
export P2MW.S_AutomorphicForm_adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter (solution)
