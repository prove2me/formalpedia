-- Prove2me | solution 1 for AutomorphicForm.setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9fb5d3e0-7718-539c-bbcb-8eedab3ff7f1

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
import Theorems.Thm_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
import Theorems.Thm_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top
import Theorems.Thm_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl"
p2m_attr_erase "simp" "NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

noncomputable section

namespace R2UnfL

open LT.TwistedNorm LT.TwistedNorm.GL2

section Family

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

abbrev sc : Lˣ →* GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2)

abbrev σG (σ : L ≃ₐ[F] L) : GL (Fin 2) L →* GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem sc_comm (u : Lˣ) (g : GL (Fin 2) L) : sc u * g = g * sc u := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (u : L) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) L)).eq

theorem mul_sc (g : GL (Fin 2) L) (u : Lˣ) : g * sc u = sc u * g := (sc_comm u g).symm

theorem mul_sc_left (g k : GL (Fin 2) L) (u : Lˣ) : g * (sc u * k) = sc u * (g * k) := by
  rw [← mul_assoc, mul_sc, mul_assoc]

theorem σG_sc (σ : L ≃ₐ[F] L) (u : Lˣ) : σG σ (sc u) = sc (Units.map ((σ : L →+* L) : L →* L) u) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change σ ((Matrix.scalar (Fin 2) (u : L)) i j) = Matrix.scalar (Fin 2) (σ (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem coe_units_map (σ : L ≃ₐ[F] L) (u : Lˣ) :
    ((Units.map ((σ : L →+* L) : L →* L) u : Lˣ) : L) = σ (u : L) := rfl

def stabU (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) : Subgroup Lˣ where
  carrier := {u | ∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σG σ h}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro u v ⟨h, hh⟩ ⟨k, hk⟩
    refine ⟨h * k, ?_⟩
    calc sc (u * v) * δ₀ = sc u * (sc v * δ₀) := by rw [map_mul, mul_assoc]
      _ = sc u * (k⁻¹ * δ₀ * σG σ k) := by rw [hk]
      _ = k⁻¹ * (sc u * δ₀) * σG σ k := by simp only [mul_assoc, mul_sc_left, mul_sc, one_mul]
      _ = k⁻¹ * (h⁻¹ * δ₀ * σG σ h) * σG σ k := by rw [hh]
      _ = (h * k)⁻¹ * δ₀ * σG σ (h * k) := by rw [map_mul, mul_inv_rev]; group
  inv_mem' := by
    rintro u ⟨h, hh⟩
    refine ⟨h⁻¹, ?_⟩
    have h1 : h * (sc u * δ₀) * (σG σ h)⁻¹ = δ₀ := by rw [hh]; group
    have h2 : sc u * (h * δ₀ * (σG σ h)⁻¹) = δ₀ := by
      calc sc u * (h * δ₀ * (σG σ h)⁻¹) = h * (sc u * δ₀) * (σG σ h)⁻¹ := by
            simp only [mul_assoc, mul_sc_left, mul_sc, one_mul]
        _ = δ₀ := h1
    calc sc u⁻¹ * δ₀ = sc u⁻¹ * (sc u * (h * δ₀ * (σG σ h)⁻¹)) := by rw [h2]
      _ = h * δ₀ * (σG σ h)⁻¹ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      _ = (h⁻¹)⁻¹ * δ₀ * σG σ h⁻¹ := by rw [inv_inv, map_inv]

theorem mem_stabU_iff (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) (u : Lˣ) :
    u ∈ stabU σ δ₀ ↔ ∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σG σ h := Iff.rfl

abbrev gammaHom (σ : L ≃ₐ[F] L) : Lˣ →* Lˣ := Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ

theorem gammaHom_apply (σ : L ≃ₐ[F] L) (w : Lˣ) :
    gammaHom σ w = Units.map ((σ : L →+* L) : L →* L) w * w⁻¹ := by
  simp [gammaHom, div_eq_mul_inv]

theorem gammaHom_mem_stabU (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) (w : Lˣ) :
    gammaHom σ w ∈ stabU σ δ₀ := by
  refine ⟨sc w, ?_⟩
  rw [gammaHom_apply, σG_sc, ← map_inv, mul_assoc (sc w⁻¹), mul_sc, ← mul_assoc, ← map_mul,
    mul_comm w⁻¹]

theorem range_gammaHom_le_stabU (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) :
    (gammaHom σ).range ≤ stabU σ δ₀ := by
  rintro _ ⟨w, rfl⟩; exact gammaHom_mem_stabU σ δ₀ w

theorem mk_sc_mul_eq_mk_sc_mul_iff (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) (u u' : Lˣ) :
    SigmaConjClasses.mk σ (sc u * δ₀) = SigmaConjClasses.mk σ (sc u' * δ₀) ↔ u⁻¹ * u' ∈ stabU σ δ₀ := by
  rw [SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map, mem_stabU_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    calc sc (u⁻¹ * u') * δ₀ = sc u⁻¹ * (sc u' * δ₀) := by rw [map_mul, mul_assoc]
      _ = sc u⁻¹ * (h⁻¹ * (sc u * δ₀) * σG σ h) := by rw [hh]
      _ = sc u⁻¹ * (sc u * (h⁻¹ * δ₀ * σG σ h)) := by
          congr 1; simp only [mul_assoc, mul_sc_left, mul_sc, one_mul]
      _ = h⁻¹ * δ₀ * σG σ h := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    calc sc u' * δ₀ = sc u * (sc (u⁻¹ * u') * δ₀) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel_left]
      _ = sc u * (h⁻¹ * δ₀ * σG σ h) := by rw [hh]
      _ = h⁻¹ * (sc u * δ₀) * σG σ h := by simp only [mul_assoc, mul_sc_left, mul_sc, one_mul]

theorem mk_σG (σ : L ≃ₐ[F] L) (δ : GL (Fin 2) L) :
    SigmaConjClasses.mk σ (σG σ δ) = SigmaConjClasses.mk σ δ := by
  symm
  exact SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨δ, by group⟩

theorem mk_sc_map_mul (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) (u : Lˣ) :
    SigmaConjClasses.mk σ (sc (Units.map ((σ : L →+* L) : L →* L) u) * δ₀) =
      SigmaConjClasses.mk σ (sc u * δ₀) := by
  rw [← mk_σG σ (sc u * δ₀), map_mul, σG_sc]

  refine SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨δ₀, ?_⟩
  simp only [mul_assoc, mul_sc_left, mul_sc, one_mul]
  rw [inv_mul_cancel_left]

theorem map_mem_stabU_iff (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) (u : Lˣ) :
    Units.map ((σ : L →+* L) : L →* L) u ∈ stabU σ δ₀ ↔ u ∈ stabU σ δ₀ := by
  have h1 := mk_sc_mul_eq_mk_sc_mul_iff σ δ₀ 1 u
  have h2 := mk_sc_mul_eq_mk_sc_mul_iff σ δ₀ 1 (Units.map ((σ : L →+* L) : L →* L) u)
  simp only [inv_one, one_mul, map_one] at h1 h2
  rw [← h1, ← h2, mk_sc_map_mul]

theorem symm_map_mem_stabU_iff (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) (u : Lˣ) :
    Units.map ((σ.symm : L →+* L) : L →* L) u ∈ stabU σ δ₀ ↔ u ∈ stabU σ δ₀ := by
  rw [← map_mem_stabU_iff σ δ₀ (Units.map ((σ.symm : L →+* L) : L →* L) u)]
  congr! 1
  ext
  simp

theorem sigmaCentralizer_sc_mul (σ : L ≃ₐ[F] L) (u : Lˣ) (δ : GL (Fin 2) L) :
    AutomorphicForm.sigmaCentralizer (σG σ) (sc u * δ) = AutomorphicForm.sigmaCentralizer (σG σ) δ := by
  ext t
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, AutomorphicForm.mem_sigmaCentralizer_iff]
  have : t * (sc u * δ) * (σG σ t)⁻¹ = sc u * (t * δ * (σG σ t)⁻¹) := by
    simp only [mul_assoc, mul_sc_left, mul_sc, one_mul]
  rw [this]
  constructor
  · intro h; exact mul_left_cancel h
  · intro h; rw [h]

theorem sq_eq_of_mem_stabU (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) {u : Lˣ} (hu : u ∈ stabU σ δ₀) :
    ∃ d : Lˣ, u ^ 2 = Units.map ((σ : L →+* L) : L →* L) d * d⁻¹ := by
  obtain ⟨h, hh⟩ := hu
  refine ⟨Matrix.GeneralLinearGroup.det h, ?_⟩
  have := congrArg Matrix.GeneralLinearGroup.det hh
  rw [map_mul, map_mul, map_mul, map_inv, Matrix.GeneralLinearGroup.map_det] at this
  have hsc : Matrix.GeneralLinearGroup.det (sc u : GL (Fin 2) L) = u ^ 2 := by
    apply Units.ext
    simp [pow_two]
  rw [hsc] at this
  have hcomm : (Matrix.GeneralLinearGroup.det h)⁻¹ * Matrix.GeneralLinearGroup.det δ₀ *
      Units.map ((σ : L →+* L) : L →* L) (Matrix.GeneralLinearGroup.det h) =
      Units.map ((σ : L →+* L) : L →* L) (Matrix.GeneralLinearGroup.det h) *
        (Matrix.GeneralLinearGroup.det h)⁻¹ * Matrix.GeneralLinearGroup.det δ₀ := by
    rw [mul_comm, ← mul_assoc]
  rw [hcomm] at this
  exact mul_right_cancel this

end Family

section NormScalar

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem sigmaPartialNorm_sc_mul (σ : L ≃ₐ[F] L) (u : Lˣ) (δ : GL (Fin 2) L) (r : ℕ) :
    sigmaPartialNorm (σG σ) (sc u * δ) r =
      sc (sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) u r) * sigmaPartialNorm (σG σ) δ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul, map_mul,
        σG_sc]
      rw [mul_assoc (sc u), ← mul_assoc δ, ← sc_comm _ δ]
      simp only [mul_assoc]

variable [FiniteDimensional F L] [IsGalois F L]

theorem coe_sc_norm (σ : L ≃ₐ[F] L) (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    ((sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L (Algebra.norm F (u : L)) • (1 : Matrix (Fin 2) (Fin 2) L) := by
  rw [← coe_sigmaNormPow_units_eq_algebraMap_norm hgen u]
  ext i j
  change Matrix.scalar (Fin 2) _ i j = _
  rw [Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

def normUnit (u : Lˣ) : Fˣ :=
  Units.mk0 (Algebra.norm F (u : L)) (Algebra.norm_ne_zero_iff.mpr u.ne_zero)

@[scoped simp] theorem coe_normUnit (u : Lˣ) : ((normUnit (F := F) u : Fˣ) : F) = Algebra.norm F (u : L) := rfl

theorem isNormRep_sc_mul {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) F} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (u : Lˣ) :
    IsNormRep σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (normUnit (F := F) u) * γ) (sc u * δ) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_def, sigmaPartialNorm_sc_mul, ← sigmaNormPow_def, ← sigmaNormPow_def, map_mul]
  have hnorm : P⁻¹ * (sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) *
      sigmaNormPow (σG σ) (Module.finrank F L) δ) * P =
      sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) *
        (P⁻¹ * sigmaNormPow (σG σ) (Module.finrank F L) δ * P) := by
    simp only [mul_assoc, mul_sc_left, mul_sc, one_mul]
  rw [hnorm]
  erw [hP]
  congr 1
  apply Units.ext
  rw [coe_sc_norm σ hgen u]
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change _ = algebraMap F L (Matrix.scalar (Fin 2) _ i j)
  rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem scalar_mul_mem_cells {γ : GL (Fin 2) F} (a : Fˣ)
    (hγ : γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ ∈ AutomorphicForm.ellipticCell F ∨
      Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ ∈ AutomorphicForm.centralCell F := by
  have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (a : F) • (γ : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul]
    change Matrix.scalar (Fin 2) (a : F) * _ = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rcases hγ with hγ | hγ
  · left
    rw [AutomorphicForm.mem_ellipticCell_iff, AutomorphicForm.IsEllipticType, hcoe]
    intro b hb
    apply hγ (b / a)
    rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at hb ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.trace_fin_two, Matrix.det_fin_two,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] at hb ⊢
    have ha : (a : F) ≠ 0 := a.ne_zero
    field_simp
    linear_combination hb
  · right
    obtain ⟨c, hc⟩ := AutomorphicForm.mem_centralCell_iff.mp hγ
    refine AutomorphicForm.mem_centralCell_iff.mpr ⟨a * c, ?_⟩
    rw [hcoe, hc, smul_smul]

theorem sc_mul_mem_I {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) (u : Lˣ) :
    ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ (sc u * δ)) = ConjClasses.mk γ := by
  obtain ⟨γ, hγ, hN⟩ := hδ

  have hrep : IsNormRep σ γ δ := by
    rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hN
    obtain ⟨Q, hQ⟩ := hN
    obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
    refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, ?_⟩
    rw [← hQ, map_mul, map_mul, map_inv, ← hP]
    group
  refine ⟨_, scalar_mul_mem_cells (normUnit (F := F) u) hγ, ?_⟩
  exact normClassMap_mk_eq_of_isNormRep hgen (isNormRep_sc_mul hgen hrep u)

theorem mem_I_of_mk_eq {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ δ' : GL (Fin 2) L} (hmk : SigmaConjClasses.mk σ δ' = SigmaConjClasses.mk σ δ)
    (hδ : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ') = ConjClasses.mk γ := by
  rwa [hmk]

end NormScalar

section Index

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [FiniteDimensional F L] [IsGalois F L] in

theorem norm_units_map (σ : L ≃ₐ[F] L) (d : Lˣ) :
    Algebra.norm F ((Units.map ((σ : L →+* L) : L →* L) d : Lˣ) : L) = Algebra.norm F (d : L) := by
  rw [coe_units_map]
  exact Algebra.norm_eq_of_algEquiv σ (d : L)

theorem norm_sq_eq_one_of_mem_stabU (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) {u : Lˣ} (hu : u ∈ stabU σ δ₀) :
    Algebra.norm F (u : L) ^ 2 = 1 := by
  obtain ⟨d, hd⟩ := sq_eq_of_mem_stabU σ δ₀ hu
  have := congrArg (fun w : Lˣ => Algebra.norm F (w : L)) hd
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_mul, map_mul] at this
  rw [this, norm_units_map, Units.val_inv_eq_inv_val, Algebra.norm_inv, mul_inv_cancel₀]
  exact Algebra.norm_ne_zero_iff.mpr d.ne_zero

theorem mem_range_gammaHom_of_norm_eq_one {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {u : Lˣ} (hu : Algebra.norm F (u : L) = 1) : u ∈ (gammaHom σ).range := by
  haveI : IsCyclic (L ≃ₐ[F] L) := ⟨⟨σ, fun τ => Subgroup.mem_zpowers_iff.mp (hgen τ)⟩⟩
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one (K := F) (L := L) hgen hu

  refine ⟨y⁻¹, ?_⟩
  apply Units.ext
  rw [gammaHom_apply, Units.val_mul, coe_units_map]
  push_cast
  rw [← hy]
  simp [div_eq_mul_inv, AlgEquiv.smul_units_def, mul_comm]

theorem finite_stabQuot {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) :
    Finite {q : Lˣ ⧸ (gammaHom σ).range // ∃ u : Lˣ, QuotientGroup.mk u = q ∧
      ∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σG σ h} := by
  classical

  let f : {q : Lˣ ⧸ (gammaHom σ).range // ∃ u : Lˣ, QuotientGroup.mk u = q ∧
      ∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σG σ h} → Bool :=
    fun q => decide (Algebra.norm F ((q.2.choose : Lˣ) : L) = 1)
  refine Finite.of_injective f ?_
  intro q q' hqq'
  obtain ⟨hq, hq2⟩ := q.2.choose_spec
  obtain ⟨hq', hq2'⟩ := q'.2.choose_spec
  set u := q.2.choose
  set u' := q'.2.choose
  have hu : u ∈ stabU σ δ₀ := hq2
  have hu' : u' ∈ stabU σ δ₀ := hq2'
  have hsq := norm_sq_eq_one_of_mem_stabU σ δ₀ hu
  have hsq' := norm_sq_eq_one_of_mem_stabU σ δ₀ hu'

  have hN : Algebra.norm F (u : L) = Algebra.norm F (u' : L) := by
    simp only [f, decide_eq_decide] at hqq'
    by_cases h1 : Algebra.norm F (u : L) = 1
    · rw [h1, hqq'.mp h1]
    · have h2 : Algebra.norm F (u' : L) ≠ 1 := fun h => h1 (hqq'.mpr h)
      rw [(sq_eq_one_iff.mp hsq).resolve_left h1, (sq_eq_one_iff.mp hsq').resolve_left h2]

  have hquot : Algebra.norm F ((u⁻¹ * u' : Lˣ) : L) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, Algebra.norm_inv, hN, inv_mul_cancel₀]
    exact Algebra.norm_ne_zero_iff.mpr u'.ne_zero
  have hmem := mem_range_gammaHom_of_norm_eq_one hgen hquot
  apply Subtype.ext
  rw [← hq, ← hq']
  exact QuotientGroup.eq.mpr hmem

omit [FiniteDimensional F L] [IsGalois F L] in
theorem nonempty_stabQuot (σ : L ≃ₐ[F] L) (δ₀ : GL (Fin 2) L) :
    Nonempty {q : Lˣ ⧸ (gammaHom σ).range // ∃ u : Lˣ, QuotientGroup.mk u = q ∧
      ∃ h : GL (Fin 2) L, sc u * δ₀ = h⁻¹ * δ₀ * σG σ h} :=
  ⟨⟨QuotientGroup.mk 1, 1, rfl, 1, by simp⟩⟩

end Index

section Instances

open MeasureTheory NumberField NumberField.AdelicHaar

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_units {M : Type*} [TopologicalSpace M] [Monoid M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  exact secondCountableTopology_units

theorem secondCountableTopology_adelicGL2 :
    SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 L) L))
  exact secondCountableTopology_units

def slab (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) L) :
    NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 L) L γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  unfold NumberField.TateGlobal.ideleNorm AutomorphicForm.globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  have := NumberField.AdeleRing.distribHaarChar_algebraMap L (Matrix.GeneralLinearGroup.det γ)
  simp only [RingHom.toMonoidHom_eq_coe] at this
  rw [this]
  simp

theorem globalPoints_mul_mem_slab_iff (α β : ℝ) (γ : GL (Fin 2) L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.globalPoints (𝓞 L) L γ * g ∈ slab L α β ↔ g ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_det_globalPoints, one_mul]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_adelicGL2

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (AutomorphicForm.globalPoints (𝓞 L) L).range
      (AutomorphicForm.AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨_, γ, rfl⟩ := γ
  have hmeas : MeasurableSet ((fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s) := (measurable_const_mul _) hs
  change ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β))
      ((fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s) = _
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s ∩ slab L α β =
      (fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

theorem smulInvariantMeasure_of_le {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    {μ : Measure X} {H₁ H₂ : Subgroup G} (hle : H₂ ≤ H₁) [SMulInvariantMeasure H₁ X μ] :
    SMulInvariantMeasure H₂ X μ :=
  ⟨fun g s hs => SMulInvariantMeasure.measure_preimage_smul (μ := μ) (⟨(g : G), hle g.2⟩ : H₁) hs⟩

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

theorem countable_unitsL : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

end Instances

section Kernel

open MeasureTheory NumberField

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

def kfun (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (δ : GL (Fin 2) L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L w * y = y * AutomorphicForm.centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem globalPoints_sc (u : Lˣ) :
    AutomorphicForm.globalPoints (𝓞 L) L (sc u) = AutomorphicForm.centralScalar (𝓞 L) L (princ L u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (u : L) i j) =
    Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem sigmaAdelicAct_centralScalar_princ (u : Lˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L (princ L u)) =
      AutomorphicForm.centralScalar (𝓞 L) L (princ L (Units.map ((σ : L →+* L) : L →* L) u)) := by
  rw [← globalPoints_sc, ← globalPoints_sc]
  have h := AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ (sc u)
  have h2 : Matrix.GeneralLinearGroup.map (σ : L →+* L) (sc u) = sc (Units.map ((σ : L →+* L) : L →* L) u) :=
    σG_sc σ u
  rw [h2] at h
  exact h

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) := by
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

theorem mul_cs (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * AutomorphicForm.centralScalar (𝓞 L) L w = AutomorphicForm.centralScalar (𝓞 L) L w * g :=
  (centralScalar_comm L w g).symm

theorem mul_cs_left (g y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (AutomorphicForm.centralScalar (𝓞 L) L w * y) = AutomorphicForm.centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, mul_cs, mul_assoc]

theorem kfun_sc_mul (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (u : Lˣ) (δ₀ : GL (Fin 2) L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    kfun K L D σ φ (sc u * δ₀) x z =
      kfun K L D σ φ δ₀ x (princ L (Units.map ((σ.symm : L →+* L) : L →* L) u) * z) := by
  unfold kfun
  congr 1
  have hu : Units.map ((σ : L →+* L) : L →* L) (Units.map ((σ.symm : L →+* L) : L →* L) u) = u := by
    ext; simp
  have h1 : AutomorphicForm.globalPoints (𝓞 L) L (sc u * δ₀) =
      AutomorphicForm.centralScalar (𝓞 L) L (princ L u) * AutomorphicForm.globalPoints (𝓞 L) L δ₀ := by
    rw [map_mul, globalPoints_sc]
  have h2 : AutomorphicForm.sigmaAdelicAct K L D σ
      (AutomorphicForm.centralScalar (𝓞 L) L (princ L (Units.map ((σ.symm : L →+* L) : L →* L) u) * z) * x) =
      AutomorphicForm.centralScalar (𝓞 L) L (princ L u) *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) := by
    rw [map_mul (AutomorphicForm.centralScalar (𝓞 L) L), mul_assoc,
      map_mul (AutomorphicForm.sigmaAdelicAct K L D σ), sigmaAdelicAct_centralScalar_princ, hu]
  rw [h1, h2, ← mul_cs L _ (princ L u)]
  simp only [mul_assoc]

theorem kfun_sigmaConj (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (h δ₀ : GL (Fin 2) L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    kfun K L D σ φ (h⁻¹ * δ₀ * σG σ h) x z =
      kfun K L D σ φ δ₀ (AutomorphicForm.globalPoints (𝓞 L) L h * x) z := by
  unfold kfun
  congr 1
  have h3 : AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L h) =
      AutomorphicForm.globalPoints (𝓞 L) L (σG σ h) :=
    AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ h
  rw [map_mul, map_mul, map_inv, mul_inv_rev, map_mul (AutomorphicForm.sigmaAdelicAct K L D σ),
    map_mul (AutomorphicForm.sigmaAdelicAct K L D σ), map_mul (AutomorphicForm.sigmaAdelicAct K L D σ),
    h3, sigmaAdelicAct_centralScalar]
  simp only [mul_assoc, mul_cs, mul_cs_left]

theorem kfun_centralizer (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (δ₀ : GL (Fin 2) L)
    {t : GL (Fin 2) L} (ht : t ∈ AutomorphicForm.sigmaCentralizer (σG σ) δ₀)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    kfun K L D σ φ δ₀ (AutomorphicForm.globalPoints (𝓞 L) L t * x) z = kfun K L D σ φ δ₀ x z := by
  rw [← kfun_sigmaConj, AutomorphicForm.mem_sigmaCentralizer_iff_inv.mp ht]

theorem mem_sigmaCentralizer_sigmaConj_iff (h δ₀ t : GL (Fin 2) L) :
    t ∈ AutomorphicForm.sigmaCentralizer (σG σ) (h⁻¹ * δ₀ * σG σ h) ↔
      h * t * h⁻¹ ∈ AutomorphicForm.sigmaCentralizer (σG σ) δ₀ := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, AutomorphicForm.mem_sigmaCentralizer_iff]
  constructor
  · intro e
    calc h * t * h⁻¹ * δ₀ * (σG σ (h * t * h⁻¹))⁻¹
        = h * (t * (h⁻¹ * δ₀ * σG σ h) * (σG σ t)⁻¹) * (σG σ h)⁻¹ := by
          simp only [map_mul, map_inv, mul_inv_rev, inv_inv]; group
      _ = h * (h⁻¹ * δ₀ * σG σ h) * (σG σ h)⁻¹ := by rw [e]
      _ = δ₀ := by group
  · intro e
    calc t * (h⁻¹ * δ₀ * σG σ h) * (σG σ t)⁻¹
        = h⁻¹ * (h * t * h⁻¹ * δ₀ * (σG σ (h * t * h⁻¹))⁻¹) * σG σ h := by
          simp only [map_mul, map_inv, mul_inv_rev, inv_inv]; group
      _ = h⁻¹ * δ₀ * σG σ h := by rw [e]

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L :
      (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; (simp [Matrix.scalar_apply]; exact continuous_id)
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

theorem continuous_kfun {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (δ : GL (Fin 2) L) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => kfun K L D σ φ δ p.1 p.2 :=
  hφ.comp (((continuous_fst.inv).mul continuous_const).mul
    ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst)))

end Kernel

section Family

open MeasureTheory NumberField NumberField.AdelicHaar Filter Function Set
open scoped ENNReal Pointwise

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adelicGL2

set_option maxHeartbeats 6400000 in

theorem family_hasSum
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (α β : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ : IsFundamentalDomain (princ L).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ (princ L).range → ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ)
    (δ₀ : GL (Fin 2) L) (Ψ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hΨ₀s : Ψ₀ ⊆ slab L α β)
    (hΨ₀ : IsFundamentalDomain ((AutomorphicForm.sigmaCentralizer (σG σ) δ₀).map
      (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ₀ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZ)
    {ιc : Type} [Countable ιc] (u : ιc → Lˣ)
    (hu_inj : ∀ c c', (u c)⁻¹ * u c' ∈ stabU σ δ₀ → c = c')
    (hu_surj : ∀ w : Lˣ, ∃ c, (u c)⁻¹ * w ∈ stabU σ δ₀)
    (hB : ∑' c, ∫⁻ z in Ω, ∫⁻ x in Ψ₀,
        ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * kfun K L D σ φ (sc (u c) * δ₀) x z‖ₑ
          ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) ∂νZ < ⊤) :
    HasSum (fun c => ∫ x in Ψ₀, ∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        kfun K L D σ φ (sc (u c) * δ₀) x z ∂νZ ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
      (((Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in Ψ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZ) := by
  classical

  haveI hSCG : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) := secondCountableTopology_adelicGL2 L
  haveI hSCZ : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_ideles L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := inferInstance
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := inferInstance
  haveI : SigmaFinite νZ := inferInstance
  haveI := smulInvariantMeasure_restrict_slab L α β
  haveI hMCS : MeasurableConstSMul (AutomorphicForm.globalPoints (𝓞 L) L).range
      (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    ⟨fun g => measurable_const_mul (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)⟩
  haveI : Countable (GL (Fin 2) L) := countable_GL2 L
  haveI : Countable Lˣ := countable_unitsL L
  haveI : Countable (princ L).range := Set.countable_range _ |>.to_subtype

  set Haar := adelicGLHaar (Fin 2) (𝓞 L) L with hHaar
  set μS : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L) := Haar.restrict (slab L α β) with hμS
  set ξf : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξf
  set k := kfun K L D σ φ with hk
  set ιA := AutomorphicForm.globalPoints (𝓞 L) L with hιA
  set U := stabU σ δ₀ with hU
  set UI : Subgroup (AdeleRing (𝓞 L) L)ˣ := U.map (princ L) with hUI
  set ΓI : Subgroup (AdeleRing (𝓞 L) L)ˣ := ((princ L).comp (gammaHom σ)).range with hΓI
  set P : Subgroup (AdeleRing (𝓞 L) L)ˣ := (princ L).range with hP

  set p : ιc → (AdeleRing (𝓞 L) L)ˣ := fun c => princ L (Units.map ((σ.symm : L →+* L) : L →* L) (u c)) with hp
  have hpP : ∀ c, p c ∈ P := fun c => ⟨_, rfl⟩

  have hξp : ∀ (w : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ), ξf (princ L w * z) = ξf z := by
    intro w z
    simp only [hξf]
    have : (⟨princ L w * z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
        ⟨princ L w, Subgroup.mem_top _⟩ * ⟨z, Subgroup.mem_top _⟩ := rfl
    rw [this, map_mul, hξt (princ L w) ⟨w, rfl⟩, one_mul]

  set F : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ → ℂ := fun q => ξf q.2 * k δ₀ q.1 q.2 with hF
  have hFc : Continuous F := (hξc.comp continuous_snd).mul (continuous_kfun K L D σ hφ δ₀)
  have hclass : ∀ (c : ιc) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      ξf z * k (sc (u c) * δ₀) x z = F (x, p c * z) := by
    intro c x z
    simp only [hF, hk, hp]
    rw [kfun_sc_mul, hξp]

  have hprinc_inj : Function.Injective (princ L) :=
    Units.map_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 L) (K := L))
  have hmemUI : ∀ v : Lˣ, princ L v ∈ UI ↔ v ∈ U := by
    intro v
    simp only [hUI, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwv⟩; rwa [← hprinc_inj hwv]
    · intro hv; exact ⟨v, hv, rfl⟩
  have hleUI : UI ≤ P := by
    rintro _ ⟨v, _, rfl⟩; exact ⟨v, rfl⟩
  set R₁ : ιc → P := fun c => ⟨(p c)⁻¹, P.inv_mem (hpP c)⟩ with hR₁def
  have hR₁coe : ∀ c, ((R₁ c : (AdeleRing (𝓞 L) L)ˣ))⁻¹ = p c := fun c => by simp [hR₁def]
  have hσσ : ∀ w : Lˣ, Units.map ((σ.symm : L →+* L) : L →* L) (Units.map ((σ : L →+* L) : L →* L) w) = w := by
    intro w; ext; simp
  have hcrit : ∀ (c : ιc) (w : Lˣ), p c * princ L w ∈ UI ↔
      (u c)⁻¹ * (Units.map ((σ : L →+* L) : L →* L) w)⁻¹ ∈ U := by
    intro c w
    have e1 : p c * princ L w = princ L (Units.map ((σ.symm : L →+* L) : L →* L)
        (u c * Units.map ((σ : L →+* L) : L →* L) w)) := by
      rw [hp, ← map_mul, map_mul (Units.map ((σ.symm : L →+* L) : L →* L)), hσσ]
    rw [e1, hmemUI, hU, symm_map_mem_stabU_iff, ← Subgroup.inv_mem_iff, mul_inv_rev, mul_comm]
  have hR₁ : ∀ γ : P, ∃! c, ((R₁ c)⁻¹ * γ : (AdeleRing (𝓞 L) L)ˣ) ∈ UI := by
    rintro ⟨_, w, rfl⟩
    have hcoe : ∀ c, ((((R₁ c)⁻¹ : P) : (AdeleRing (𝓞 L) L)ˣ)) = p c := fun c => by simp [hR₁def]
    obtain ⟨c₀, hc₀⟩ := hu_surj (Units.map ((σ : L →+* L) : L →* L) w)⁻¹
    refine ⟨c₀, ?_, ?_⟩
    · show (((R₁ c₀)⁻¹ : P) : (AdeleRing (𝓞 L) L)ˣ) * princ L w ∈ UI
      rw [hcoe, hcrit]; exact hc₀
    · intro c hc
      change (((R₁ c)⁻¹ : P) : (AdeleRing (𝓞 L) L)ˣ) * princ L w ∈ UI at hc
      rw [hcoe, hcrit] at hc
      refine (hu_inj c₀ c ?_).symm
      have := U.mul_mem hc₀ (U.inv_mem hc)
      have heq : (u c₀)⁻¹ * (Units.map ((σ : L →+* L) : L →* L) w)⁻¹ *
          ((u c)⁻¹ * (Units.map ((σ : L →+* L) : L →* L) w)⁻¹)⁻¹ = (u c₀)⁻¹ * u c := by group
      rwa [heq] at this

  have hΩ' := MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    νZ P UI hleUI Ω hΩ R₁ hR₁
  set Ω' : Set (AdeleRing (𝓞 L) L)ˣ := ⋃ c, ((R₁ c : (AdeleRing (𝓞 L) L)ˣ)⁻¹) • Ω with hΩ'def

  set hh : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ∫ x in Ψ₀, F (x, z) ∂μS with hhh
  have hFsm : StronglyMeasurable F := hFc.stronglyMeasurable
  have hhh_sm : StronglyMeasurable hh := hFsm.integral_prod_left' (μ := μS.restrict Ψ₀)

  have hFp_cont : ∀ c, Continuous fun q : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      F (q.1, p c * q.2) := fun c => hFc.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))
  have hFp_meas : ∀ c, Measurable fun q : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ‖F (q.1, p c * q.2)‖ₑ := fun c => (hFp_cont c).measurable.enorm

  have hB' : ∑' c, ∫⁻ z in Ω, ∫⁻ x in Ψ₀, ‖F (x, p c * z)‖ₑ ∂μS ∂νZ < ⊤ := by
    have : ∀ c, (∫⁻ z in Ω, ∫⁻ x in Ψ₀, ‖F (x, p c * z)‖ₑ ∂μS ∂νZ) =
        ∫⁻ z in Ω, ∫⁻ x in Ψ₀, ‖ξf z * k (sc (u c) * δ₀) x z‖ₑ ∂μS ∂νZ := by
      intro c; simp_rw [hclass]
    simp_rw [this]
    exact hB
  have hBc : ∀ c, ∫⁻ z in Ω, ∫⁻ x in Ψ₀, ‖F (x, p c * z)‖ₑ ∂μS ∂νZ < ⊤ := fun c =>
    lt_of_le_of_lt (ENNReal.le_tsum c) hB'

  have hhh_le : ∀ c z, ‖hh (p c * z)‖ₑ ≤ ∫⁻ x in Ψ₀, ‖F (x, p c * z)‖ₑ ∂μS := fun c z =>
    enorm_integral_le_lintegral_enorm _
  have hbound₁ : ∑' c, ∫⁻ z in Ω, ‖hh (p c * z)‖ₑ ∂νZ < ⊤ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun c => lintegral_mono fun z => hhh_le c z) hB'

  have coset₁ := (MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    νZ P UI hleUI Ω hΩ R₁ hR₁).2 hh hhh_sm.aestronglyMeasurable ?_
  swap
  ·
    have : (fun z => ∑' c, ‖hh ((R₁ c : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • z)‖ₑ) =
        fun z => ∑' c, ‖hh (p c * z)‖ₑ := by
      funext z; simp only [hR₁coe, smul_eq_mul]
    rw [this, lintegral_tsum fun c =>
      (show Measurable (fun z => ‖hh (p c * z)‖ₑ) from
        (hhh_sm.measurable.comp (measurable_const_mul (p c))).enorm).aemeasurable]
    exact hbound₁
  obtain ⟨hint', -, hunfold₁⟩ := coset₁
  have hunfold₁' : ∫ z in Ω', hh z ∂νZ = ∫ z in Ω, ∑' c, hh (p c * z) ∂νZ := by
    rw [hunfold₁]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hR₁coe, smul_eq_mul]

  have hint_c : ∀ c, Integrable (fun z => hh (p c * z)) (νZ.restrict Ω) := by
    intro c
    refine ⟨(hhh_sm.measurable.comp (measurable_const_mul (p c))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (le_trans (lintegral_mono fun z => hhh_le c z) (ENNReal.le_tsum c)) hB'
  have hsum_norm : Summable fun c => ∫ z in Ω, ‖hh (p c * z)‖ ∂νZ := by
    have : (fun c => ∫ z in Ω, ‖hh (p c * z)‖ ∂νZ) = fun c => (∫⁻ z in Ω, ‖hh (p c * z)‖ₑ ∂νZ).toReal := by
      funext c
      exact integral_norm_eq_lintegral_enorm (hint_c c).aestronglyMeasurable
    rw [this]
    exact ENNReal.summable_toReal hbound₁.ne
  have hS5 : HasSum (fun c => ∫ z in Ω, hh (p c * z) ∂νZ) (∫ z in Ω, ∑' c, hh (p c * z) ∂νZ) :=
    hasSum_integral_of_summable_integral_norm hint_c hsum_norm

  have hS6 : ∀ c, (∫ x in Ψ₀, ∫ z in Ω, ξf z * k (sc (u c) * δ₀) x z ∂νZ ∂μS) = ∫ z in Ω, hh (p c * z) ∂νZ := by
    intro c
    have e1 : (∫ x in Ψ₀, ∫ z in Ω, ξf z * k (sc (u c) * δ₀) x z ∂νZ ∂μS) =
        ∫ x in Ψ₀, ∫ z in Ω, F (x, p c * z) ∂νZ ∂μS := by
      simp_rw [hclass]
    rw [e1]

    have hprod : Integrable (Function.uncurry fun x z => F (x, p c * z)) ((μS.restrict Ψ₀).prod (νZ.restrict Ω)) := by
      refine ⟨(hFp_cont c).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      change ∫⁻ q, ‖F (q.1, p c * q.2)‖ₑ ∂((μS.restrict Ψ₀).prod (νZ.restrict Ω)) < ⊤
      rw [lintegral_prod _ (hFp_meas c).aemeasurable]
      rw [lintegral_lintegral_swap (hFp_meas c).aemeasurable]
      exact hBc c
    exact integral_integral_swap hprod

  have hinv : ∀ (v : Lˣ), v ∈ U → ∀ z, hh (princ L v * z) = hh z := by
    intro v hv z

    have hv' : Units.map ((σ : L →+* L) : L →* L) v ∈ U := (map_mem_stabU_iff σ δ₀ v).mpr hv
    obtain ⟨h, hh_eq⟩ := hv'

    have hpt : ∀ x, F (x, princ L v * z) = ξf z * k δ₀ (ιA h * x) z := by
      intro x
      simp only [hF]
      rw [hξp]
      congr 1
      have := kfun_sc_mul K L D σ φ (Units.map ((σ : L →+* L) : L →* L) v) δ₀ x z
      rw [hσσ] at this
      rw [hk, ← this, hh_eq, kfun_sigmaConj]
    have e1 : hh (princ L v * z) = ξf z * ∫ x in Ψ₀, k δ₀ (ιA h * x) z ∂μS := by
      simp only [hhh, hpt]
      exact integral_const_mul _ _
    have e2 : hh z = ξf z * ∫ x in Ψ₀, k δ₀ x z ∂μS := by
      simp only [hhh, hF]
      exact integral_const_mul _ _
    rw [e1, e2]
    congr 1

    set g : ιA.range := ⟨ιA h, h, rfl⟩ with hgdef
    have hmp : MeasurePreserving (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => g • x) μS μS :=
      measurePreserving_smul g μS
    have e3 : ∫ x in Ψ₀, k δ₀ (ιA h * x) z ∂μS = ∫ y in (ιA h) • Ψ₀, k δ₀ y z ∂μS := by
      have := hmp.setIntegral_preimage_emb (measurableEmbedding_const_smul g) (fun y => k δ₀ y z) ((ιA h) • Ψ₀)
      have hpre : (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => g • x) ⁻¹' ((ιA h) • Ψ₀) = Ψ₀ := by
        have : (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => g • x) = fun x => (ιA h) • x := rfl
        rw [this, Set.preimage_smul, inv_smul_smul]
      rw [hpre] at this
      exact this
    have hmp' : MeasurePreserving (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => g⁻¹ • x) μS μS :=
      measurePreserving_smul g⁻¹ μS
    have hfeq : (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => g⁻¹ • x) =
        fun x => (ιA h)⁻¹ • x := by
      funext x
      rw [Subgroup.smul_def, Subgroup.coe_inv]
    rw [hfeq] at hmp'
    rw [e3]

    have hT_eq : AutomorphicForm.sigmaCentralizer (σG σ) δ₀ =
        AutomorphicForm.sigmaCentralizer (σG σ) (h⁻¹ * δ₀ * σG σ h) := by
      rw [← hh_eq, sigmaCentralizer_sc_mul]
    have hnorm : ∀ t, t ∈ AutomorphicForm.sigmaCentralizer (σG σ) δ₀ ↔
        h * t * h⁻¹ ∈ AutomorphicForm.sigmaCentralizer (σG σ) δ₀ := by
      intro t
      conv_lhs => rw [hT_eq]
      exact mem_sigmaCentralizer_sigmaConj_iff K L σ h δ₀ t

    have e4 : ∫ y in (ιA h) • Ψ₀, k δ₀ y z ∂μS = ∫ y in Ψ₀, k δ₀ y z ∂μS := by
      set TΛ : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
        (AutomorphicForm.sigmaCentralizer (σG σ) δ₀).map ιA with hTΛ
      haveI : SMulInvariantMeasure TΛ (AutomorphicForm.AdelicGL2 (𝓞 L) L) μS :=
        smulInvariantMeasure_of_le (Subgroup.map_le_range _ _)
      haveI : MeasurableConstSMul TΛ (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
        ⟨fun g => measurable_const_mul (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)⟩
      haveI : Countable TΛ := by
        have hc : (TΛ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)).Countable :=
          (Set.countable_range ιA).mono fun y hy => Subgroup.map_le_range _ _ hy
        exact hc.to_subtype
      have hmemT : ∀ y, y ∈ TΛ ↔ ∃ t ∈ AutomorphicForm.sigmaCentralizer (σG σ) δ₀, ιA t = y := fun y =>
        Subgroup.mem_map
      have hconj_mem : ∀ y ∈ TΛ, (ιA h)⁻¹ * y * ιA h ∈ TΛ := by
        intro y hy
        obtain ⟨t, ht, rfl⟩ := (hmemT y).mp hy
        refine (hmemT _).mpr ⟨h⁻¹ * t * h, ?_, by rw [map_mul, map_mul, map_inv]⟩
        rw [hnorm]
        have heq : h * (h⁻¹ * t * h) * h⁻¹ = t := by group
        rwa [heq]
      have hconj_mem' : ∀ y ∈ TΛ, ιA h * y * (ιA h)⁻¹ ∈ TΛ := by
        intro y hy
        obtain ⟨t, ht, rfl⟩ := (hmemT y).mp hy
        refine (hmemT _).mpr ⟨h * t * h⁻¹, (hnorm t).mp ht, by rw [map_mul, map_mul, map_inv]⟩
      let e : TΛ ≃ TΛ :=
        { toFun := fun y => ⟨ιA h * y * (ιA h)⁻¹, hconj_mem' y y.2⟩
          invFun := fun y => ⟨(ιA h)⁻¹ * y * ιA h, hconj_mem y y.2⟩
          left_inv := fun y => by
            apply Subtype.ext
            show (ιA h)⁻¹ * (ιA h * (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) * (ιA h)⁻¹) * ιA h = y
            simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
          right_inv := fun y => by
            apply Subtype.ext
            show ιA h * ((ιA h)⁻¹ * (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) * ιA h) * (ιA h)⁻¹ = y
            simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] }
      have hfd : IsFundamentalDomain TΛ ((ιA h) • Ψ₀) μS := by
        have hpre : (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => (ιA h)⁻¹ • x) ⁻¹' Ψ₀ = ιA h • Ψ₀ :=
          Set.preimage_smul_inv (ιA h) Ψ₀
        rw [← hpre]
        refine hΨ₀.preimage_of_equiv hmp'.quasiMeasurePreserving e.bijective (fun y x => ?_)
        show (ιA h)⁻¹ • ((e y : TΛ) • x) = y • ((ιA h)⁻¹ • x)
        rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        show (ιA h)⁻¹ * (ιA h * (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) * (ιA h)⁻¹ * x) =
          (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) * ((ιA h)⁻¹ * x)
        simp only [mul_assoc, inv_mul_cancel_left]
      refine IsFundamentalDomain.setIntegral_eq hfd hΨ₀ (f := fun y => k δ₀ y z) fun t y => ?_
      obtain ⟨t', ht', ht'eq⟩ := (hmemT t).mp t.2
      show k δ₀ (t • y) z = k δ₀ y z
      rw [Subgroup.smul_def, smul_eq_mul, ← ht'eq, hk, kfun_centralizer K L D σ φ δ₀ ht']
    exact e4
  have hinvUI : ∀ w ∈ UI, ∀ z, hh (w * z) = hh z := by
    intro w hw z
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    exact hinv v hv z

  set Qt := {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
      ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
        Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
          h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} with hQt
  haveI : Finite Qt := finite_stabQuot hgen δ₀
  letI : Fintype Qt := Fintype.ofFinite Qt
  have hleΓ : ΓI ≤ UI := by
    rintro _ ⟨w, rfl⟩
    exact (hmemUI _).mpr (gammaHom_mem_stabU σ δ₀ w)
  haveI : Countable UI := by
    have hc : (UI : Set (AdeleRing (𝓞 L) L)ˣ).Countable :=
      (Set.countable_range (princ L)).mono fun y hy => hleUI hy
    exact hc.to_subtype
  have hlift : ∀ q : Qt, ∃ uq : Lˣ, QuotientGroup.mk uq = (q : Lˣ ⧸ (gammaHom σ).range) ∧ uq ∈ U := by
    intro q
    obtain ⟨uq, h1, h2⟩ := q.2
    exact ⟨uq, h1, h2⟩
  choose lift hlift1 hlift2 using hlift
  set R₂ : Qt → UI := fun q => ⟨princ L (lift q), (hmemUI _).mpr (hlift2 q)⟩ with hR₂def
  have hR₂ : ∀ γ : UI, ∃! q, ((R₂ q)⁻¹ * γ : (AdeleRing (𝓞 L) L)ˣ) ∈ ΓI := by
    rintro ⟨_, hγ⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hγ
    have hcrit₂ : ∀ q : Qt, (((R₂ q)⁻¹ * ⟨princ L v, hγ⟩ : UI) : (AdeleRing (𝓞 L) L)ˣ) ∈ ΓI ↔
        (q : Lˣ ⧸ (gammaHom σ).range) = QuotientGroup.mk v := by
      intro q
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      change (princ L (lift q))⁻¹ * princ L v ∈ ΓI ↔ _
      rw [← map_inv, ← map_mul, ← hlift1 q, QuotientGroup.eq]
      simp only [hΓI, MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply]
      constructor
      · rintro ⟨w, hw⟩; exact ⟨w, hprinc_inj hw⟩
      · rintro ⟨w, hw⟩; exact ⟨w, by rw [hw]⟩
    refine ⟨⟨QuotientGroup.mk v, v, rfl, hv⟩, (hcrit₂ _).mpr rfl, fun q hq => ?_⟩
    apply Subtype.ext
    exact (hcrit₂ q).mp hq
  haveI : Countable ΓI := by
    have hc : (ΓI : Set (AdeleRing (𝓞 L) L)ˣ).Countable :=
      (Set.countable_range (princ L)).mono fun y hy => hleUI (hleΓ hy)
    exact hc.to_subtype
  have hΘ' := MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    νZ UI ΓI hleΓ Ω' hΩ' R₂ hR₂
  have coset₂ := (MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    νZ UI ΓI hleΓ Ω' hΩ' R₂ hR₂).2 hh hhh_sm.aestronglyMeasurable ?_
  swap
  ·
    have hpt : ∀ z, (∑' q : Qt, ‖hh ((R₂ q : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • z)‖ₑ) = (Fintype.card Qt : ℝ≥0∞) * ‖hh z‖ₑ := by
      intro z
      have : ∀ q : Qt, hh ((R₂ q : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • z) = hh z := fun q =>
        hinvUI _ (UI.inv_mem (R₂ q).2) z
      simp only [this, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [hpt]
    rw [lintegral_const_mul _ hhh_sm.measurable.enorm]
    exact ENNReal.mul_lt_top (by simp) hint'.2
  obtain ⟨-, -, hunfold₂⟩ := coset₂
  set Θ' : Set (AdeleRing (𝓞 L) L)ˣ := ⋃ q, ((R₂ q : (AdeleRing (𝓞 L) L)ˣ)⁻¹) • Ω' with hΘ'def
  have hunfold₂' : ∫ z in Θ', hh z ∂νZ = (Fintype.card Qt : ℂ) * ∫ z in Ω', hh z ∂νZ := by
    rw [hunfold₂]
    have hpt : ∀ z, (∑' q : Qt, hh ((R₂ q : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • z)) = (Fintype.card Qt : ℂ) * hh z := by
      intro z
      have : ∀ q : Qt, hh ((R₂ q : (AdeleRing (𝓞 L) L)ˣ)⁻¹ • z) = hh z := fun q =>
        hinvUI _ (UI.inv_mem (R₂ q).2) z
      simp only [this, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [hpt]
    exact integral_const_mul _ _

  have hΘeq : ∫ z in Θ, hh z ∂νZ = ∫ z in Θ', hh z ∂νZ := by
    refine IsFundamentalDomain.setIntegral_eq hΘ hΘ' fun w z => ?_
    change hh ((w : (AdeleRing (𝓞 L) L)ˣ) * z) = hh z
    exact hinvUI _ (hleΓ w.2) z

  have hcard : (Nat.card Qt : ℂ) = Fintype.card Qt := by rw [Nat.card_eq_fintype_card]
  have hcard0 : (Fintype.card Qt : ℂ) ≠ 0 := by
    haveI : Nonempty Qt := nonempty_stabQuot σ δ₀
    exact_mod_cast Fintype.card_ne_zero
  have hΘhh : ∫ z in Θ, ξf z * (∫ x in Ψ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂Haar) ∂νZ =
      ∫ z in Θ, hh z ∂νZ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hhh, hF]
    rw [integral_const_mul]
    congr 1
    rw [hμS, Measure.restrict_restrict_of_subset hΨ₀s]
    rfl
  have hvalue : ∫ z in Ω, ∑' c, hh (p c * z) ∂νZ =
      ((Nat.card Qt : ℕ) : ℂ)⁻¹ * ∫ z in Θ, ξf z * (∫ x in Ψ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂Haar) ∂νZ := by
    calc ∫ z in Ω, ∑' c, hh (p c * z) ∂νZ = ∫ z in Ω', hh z ∂νZ := hunfold₁'.symm
      _ = (Fintype.card Qt : ℂ)⁻¹ * ((Fintype.card Qt : ℂ) * ∫ z in Ω', hh z ∂νZ) := by
          rw [← mul_assoc, inv_mul_cancel₀ hcard0, one_mul]
      _ = (Fintype.card Qt : ℂ)⁻¹ * ∫ z in Θ', hh z ∂νZ := by rw [hunfold₂']
      _ = (Fintype.card Qt : ℂ)⁻¹ * ∫ z in Θ, hh z ∂νZ := by rw [hΘeq]
      _ = ((Nat.card Qt : ℕ) : ℂ)⁻¹ * ∫ z in Θ, ξf z * (∫ x in Ψ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂Haar) ∂νZ := by
          rw [hcard, hΘhh]
  rw [← hvalue]
  have hfun : (fun c => ∫ x in Ψ₀, ∫ z in Ω, ξf z * k (sc (u c) * δ₀) x z ∂νZ ∂μS) =
      fun c => ∫ z in Ω, hh (p c * z) ∂νZ := funext hS6
  rw [hfun]
  exact hS5

end Family

section Main

open MeasureTheory NumberField NumberField.AdelicHaar Filter Function Set
open scoped ENNReal Pointwise
open IsDedekindDomain

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adelicGL2

theorem twist_centralScalar_mul (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    x⁻¹ * g * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
      x⁻¹ * g * AutomorphicForm.sigmaAdelicAct K L D σ x *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) := by
  rw [map_mul, sigmaAdelicAct_centralScalar, centralScalar_comm]
  simp only [mul_assoc]

set_option maxHeartbeats 6400000 in
theorem main
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Ω νZ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (R : Set (GL (Fin 2) L))
    (hRsub : R ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (hR : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ R ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h))
    (Ψ : GL (Fin 2) L → Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨs : ∀ δ₀ ∈ R, Ψ δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : ∀ δ₀ ∈ R, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZ) :
    (∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
              ConjClasses.mk γ},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZ)
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
    ∑ᶠ δ₀ ∈ R,
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in Ψ δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZ := by
  classical

  haveI hSCG : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) := secondCountableTopology_adelicGL2 L
  haveI hSCZ : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_ideles L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := inferInstance
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := inferInstance
  haveI : SigmaFinite νZ := inferInstance
  haveI := smulInvariantMeasure_restrict_slab L α β
  haveI : Countable (GL (Fin 2) L) := countable_GL2 L
  haveI : Countable (LT.TwistedNorm.SigmaConjClasses σ) :=
    (LT.TwistedNorm.SigmaConjClasses.mk_surjective σ).countable

  let PredI : GL (Fin 2) L → Prop := fun δ => ∃ γ : GL (Fin 2) K,
    (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
    LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ
  let PredC : LT.TwistedNorm.SigmaConjClasses σ → Prop := fun c => ∃ γ : GL (Fin 2) K,
    (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
    LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ
  let ξf : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)
  let k := kfun K L D σ φ
  let Haar := adelicGLHaar (Fin 2) (𝓞 L) L
  let μS : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L) := Haar.restrict (slab L α β)

  have hout : ∀ c : LT.TwistedNorm.SigmaConjClasses σ, ∃ δ, LT.TwistedNorm.SigmaConjClasses.mk σ δ = c :=
    LT.TwistedNorm.SigmaConjClasses.mk_surjective σ
  choose δc hδc using hout
  have hPredI : ∀ c : {c // PredC c}, PredI (δc c.1) := by
    intro c
    show PredC (LT.TwistedNorm.SigmaConjClasses.mk σ (δc c.1))
    rw [hδc]; exact c.2
  have hfam0 : ∀ c : {c // PredC c}, ∃ δ₀, δ₀ ∈ R ∧ ∃ (h : GL (Fin 2) L) (v : Lˣ),
      δc c.1 = sc v * (h⁻¹ * δ₀ * σG σ h) := fun c => (hR (δc c.1) (hPredI c)).exists
  choose fam hfamR hfam1 using hfam0
  choose hc vc hdecomp using hfam1
  have huniq : ∀ (c : {c // PredC c}) (δ₀' : GL (Fin 2) L), δ₀' ∈ R →
      (∃ (h : GL (Fin 2) L) (v : Lˣ), δc c.1 = sc v * (h⁻¹ * δ₀' * σG σ h)) → δ₀' = fam c := by
    intro c δ₀' h1 h2
    exact (hR (δc c.1) (hPredI c)).unique ⟨h1, h2⟩ ⟨hfamR c, hc c, vc c, hdecomp c⟩
  have hcls : ∀ c : {c // PredC c}, (c : LT.TwistedNorm.SigmaConjClasses σ) =
      LT.TwistedNorm.SigmaConjClasses.mk σ (sc (vc c) * fam c) := by
    intro c
    rw [← hδc c.1]
    symm
    refine LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨hc c, ?_⟩
    rw [hdecomp c]
    simp only [mul_assoc, mul_sc_left, mul_sc]

  have hPredC_sc : ∀ (r : R) (w : Lˣ), PredC (LT.TwistedNorm.SigmaConjClasses.mk σ (sc w * r)) :=
    fun r w => sc_mul_mem_I hgen (hRsub r.2) w

  have hfam_sc : ∀ (r : R) (w : Lˣ),
      fam ⟨LT.TwistedNorm.SigmaConjClasses.mk σ (sc w * r), hPredC_sc r w⟩ = r := by
    intro r w
    symm
    apply huniq _ r r.2
    set c : {c // PredC c} := ⟨LT.TwistedNorm.SigmaConjClasses.mk σ (sc w * r), hPredC_sc r w⟩
    have hmk : LT.TwistedNorm.SigmaConjClasses.mk σ (sc w * r) =
        LT.TwistedNorm.SigmaConjClasses.mk σ (δc c.1) := by rw [hδc]
    obtain ⟨h, hh⟩ := LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mp hmk
    refine ⟨h, w, ?_⟩
    rw [hh]
    simp only [mul_assoc, mul_sc_left, mul_sc]

  let rep : LT.TwistedNorm.SigmaConjClasses σ → GL (Fin 2) L := fun c =>
    if h : PredC c then sc (vc ⟨c, h⟩) * fam ⟨c, h⟩ else δc c
  have hrep : ∀ c, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c := by
    intro c
    by_cases h : PredC c
    · simp only [rep, dif_pos h]; exact (hcls ⟨c, h⟩).symm
    · simp only [rep, dif_neg h]; exact hδc c
  let Ψ' : LT.TwistedNorm.SigmaConjClasses σ → Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := fun c =>
    if h : PredC c then Ψ (fam ⟨c, h⟩) else ∅
  have hΨ' : ∀ c : LT.TwistedNorm.SigmaConjClasses σ, PredC c →
      IsFundamentalDomain
        ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
          (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ' c) μS := by
    intro c h
    have hrepc : rep c = sc (vc ⟨c, h⟩) * fam ⟨c, h⟩ := dif_pos h
    have hΨc : Ψ' c = Ψ (fam ⟨c, h⟩) := dif_pos h
    have hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c) =
        AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (fam ⟨c, h⟩) := by
      rw [hrepc]
      exact sigmaCentralizer_sc_mul σ (vc ⟨c, h⟩) (fam ⟨c, h⟩)
    rw [hT, hΨc]
    exact hΨ (fam ⟨c, h⟩) (hfamR ⟨c, h⟩)

  have habs := AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top
    K L hgen D α β hα Φ hΦs hΦ νZ Ω hΩ ξ hξc hξt φ hφ hφc
  have hG2 := AutomorphicForm.hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
    K L hgen D α β Φ hΦs hΦ νZ Ω ξ hξc rep hrep Ψ' hΨ' φ hφ hφc habs

  set σA := AutomorphicForm.sigmaAdelicAct K L D σ with hσA
  set hf : GL (Fin 2) L → AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ → ℂ :=
    fun δ q => ξf q.2 * k δ q.1 q.2 with hhf
  have hcont : ∀ δ, Continuous (hf δ) := fun δ =>
    (hξc.comp continuous_snd).mul (continuous_kfun K L D σ hφ δ)
  have hμΦ : μS.restrict Φ = Haar.restrict Φ := Measure.restrict_restrict_of_subset hΦs
  have hGm : Measurable fun q : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑' δ : {δ : GL (Fin 2) L // PredC (LT.TwistedNorm.SigmaConjClasses.mk σ δ)}, ‖hf δ q‖ₑ :=
    Measurable.tsum fun δ => (hcont δ).measurable.enorm
  set T : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ := fun z => ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // PredC (LT.TwistedNorm.SigmaConjClasses.mk σ δ)}, ‖hf δ (x, z)‖ₑ ∂Haar with hT
  have hTm : Measurable T := hGm.lintegral_prod_left'
  have hswap : ∫⁻ z in Ω, T z ∂νZ = ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : {δ : GL (Fin 2) L // PredC (LT.TwistedNorm.SigmaConjClasses.mk σ δ)}, ‖hf δ (x, z)‖ₑ ∂νZ ∂Haar := by
    simp only [hT]
    exact (lintegral_lintegral_swap (μ := Haar.restrict Φ) (ν := νZ.restrict Ω)
      (f := fun x z => ∑' δ : {δ : GL (Fin 2) L // PredC (LT.TwistedNorm.SigmaConjClasses.mk σ δ)}, ‖hf δ (x, z)‖ₑ) hGm.aemeasurable).symm
  have hTfin : ∫⁻ z in Ω, T z ∂νZ < ⊤ := by rw [hswap]; exact habs
  have hae : ∀ᵐ z ∂νZ.restrict Ω, T z < ⊤ := ae_lt_top hTm hTfin.ne

  set Fz : (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ := fun z y =>
    ξf z * φ (y * σA (AutomorphicForm.centralScalar (𝓞 L) L z)) with hFz
  have hFz_eq : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L),
      Fz z (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * σA x) = hf δ (x, z) := by
    intro z x δ
    simp only [hFz, hhf, hσA, k, kfun, twist_centralScalar_mul]
  have hFz_sm : ∀ z, StronglyMeasurable (Fz z) := fun z =>
    (continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))).stronglyMeasurable
  have hrep' : ∀ c ∈ {c | PredC c}, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c := fun c _ => hrep c
  have hΨ'' : ∀ c ∈ {c | PredC c}, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ' c) μS := fun c hcQ => hΨ' c hcQ
  have hG1 : ∀ z, T z < ⊤ →
      (∑' c : {c // PredC c}, ∫⁻ x in Ψ' c, ‖hf (rep c) (x, z)‖ₑ ∂μS) = T z := by
    intro z hz
    have habsz : ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ {c | PredC c}},
        ‖Fz z (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * σA x)‖ₑ ∂μS < ⊤ := by
      simp_rw [hFz_eq]
      rw [hμΦ]
      exact hz
    have key := AutomorphicForm.hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top K L (𝓞 L)
      σ σA (AutomorphicForm.continuous_sigmaAdelicAct K L D σ)
      (fun γ => AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ γ) μS Φ hΦ {c | PredC c} rep hrep' Ψ' hΨ''
      (Fz z) (hFz_sm z) habsz
    have h1 := key.1
    simp_rw [hFz_eq] at h1
    rw [hμΦ] at h1
    exact h1

  let famR : {c // PredC c} → R := fun c => ⟨fam c, hfamR c⟩
  have hper : ∀ r : R, HasSum
      (fun c : {c : {c // PredC c} // famR c = r} => ∫ x in Ψ r, ∫ z in Ω, ξf z * kfun K L D σ φ (sc (vc c.1) * r) x z ∂νZ ∂μS)
      (((Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * (r : GL (Fin 2) L) =
              h⁻¹ * (r : GL (Fin 2) L) * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in Ψ r, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L r *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZ) := by
    intro r
    have hfam_eq : ∀ c : {c : {c // PredC c} // famR c = r}, fam c.1 = r := fun c => congrArg Subtype.val c.2

    have hu_inj : ∀ c c' : {c : {c // PredC c} // famR c = r}, (vc c.1)⁻¹ * vc c'.1 ∈ stabU σ (r : GL (Fin 2) L) → c = c' := by
      intro c c' hcc'
      have hmk := (mk_sc_mul_eq_mk_sc_mul_iff σ (r : GL (Fin 2) L) (vc c.1) (vc c'.1)).mpr hcc'
      apply Subtype.ext; apply Subtype.ext
      rw [hcls c.1, hcls c'.1, hfam_eq c, hfam_eq c']
      exact hmk
    have hu_surj : ∀ w : Lˣ, ∃ c : {c : {c // PredC c} // famR c = r}, (vc c.1)⁻¹ * w ∈ stabU σ (r : GL (Fin 2) L) := by
      intro w
      let c₀ : {c // PredC c} := ⟨LT.TwistedNorm.SigmaConjClasses.mk σ (sc w * r), hPredC_sc r w⟩
      have hc₀ : famR c₀ = r := Subtype.ext (hfam_sc r w)
      refine ⟨⟨c₀, hc₀⟩, ?_⟩
      rw [← mk_sc_mul_eq_mk_sc_mul_iff]
      have := hcls c₀
      rw [hfam_sc r w] at this
      exact this.symm

    have hB : ∑' c : {c : {c // PredC c} // famR c = r}, ∫⁻ z in Ω, ∫⁻ x in Ψ r,
        ‖ξf z * kfun K L D σ φ (sc (vc c.1) * r) x z‖ₑ ∂μS ∂νZ < ⊤ := by

      have hsummand : ∀ (c : {c : {c // PredC c} // famR c = r}) (z : (AdeleRing (𝓞 L) L)ˣ),
          (∫⁻ x in Ψ r, ‖ξf z * kfun K L D σ φ (sc (vc c.1) * r) x z‖ₑ ∂μS) =
            ∫⁻ x in Ψ' c.1, ‖hf (rep c.1) (x, z)‖ₑ ∂μS := by
        intro c z
        have hrepc : rep c.1 = sc (vc c.1) * fam c.1 :=
          (dif_pos c.1.2 : rep c.1 = sc (vc ⟨c.1.1, c.1.2⟩) * fam ⟨c.1.1, c.1.2⟩)
        have hΨc : Ψ' c.1 = Ψ (fam c.1) := (dif_pos c.1.2 : Ψ' c.1 = Ψ (fam ⟨c.1.1, c.1.2⟩))
        rw [hrepc, hΨc, hfam_eq c]
      have hmeas : ∀ c : {c : {c // PredC c} // famR c = r}, AEMeasurable
          (fun z => ∫⁻ x in Ψ' c.1, ‖hf (rep c.1) (x, z)‖ₑ ∂μS) (νZ.restrict Ω) := fun c =>
        ((hcont (rep c.1)).measurable.enorm.lintegral_prod_left' (μ := μS.restrict (Ψ' c.1))).aemeasurable
      simp_rw [hsummand]
      rw [← lintegral_tsum hmeas]
      refine lt_of_le_of_lt (lintegral_mono_ae ?_) hTfin
      filter_upwards [hae] with z hz
      rw [← hG1 z hz]
      exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        (fun c : {c // PredC c} => ∫⁻ x in Ψ' c, ‖hf (rep c) (x, z)‖ₑ ∂μS)
    exact family_hasSum K L σ hgen D α β νZ Ω hΩ ξ hξc hξt φ hφ (r : GL (Fin 2) L) (Ψ r) (hΨs r r.2)
      (hΨ r r.2) Θ hΘ (fun c : {c : {c // PredC c} // famR c = r} => vc c.1) hu_inj hu_surj hB

  let term : GL (Fin 2) L → ℂ := fun δ₀ =>
    ((Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
        ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
          Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
            h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} : ℕ) : ℂ)⁻¹ *
      ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∫ x in Ψ δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZ
  let e := Equiv.sigmaFiberEquiv famR
  have hG2' := (Equiv.hasSum_iff e).mpr hG2
  have hfib : ∀ r : R, HasSum (fun c : {c : {c // PredC c} // famR c = r} =>
      ((fun c : {c // PredC c} => ∫ x in Ψ' c, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (rep c) *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZ)
          ∂μS) ∘ e) ⟨r, c⟩) (term r) := by
    intro r
    have hfam_eq : ∀ c : {c : {c // PredC c} // famR c = r}, fam c.1 = r := fun c => congrArg Subtype.val c.2
    have hfun : (fun c : {c : {c // PredC c} // famR c = r} =>
        ((fun c : {c // PredC c} => ∫ x in Ψ' c, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (rep c) *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZ)
          ∂μS) ∘ e) ⟨r, c⟩) =
        fun c => ∫ x in Ψ r, ∫ z in Ω, ξf z * kfun K L D σ φ (sc (vc c.1) * r) x z ∂νZ ∂μS := by
      funext c
      have hrepc : rep c.1 = sc (vc c.1) * fam c.1 :=
        (dif_pos c.1.2 : rep c.1 = sc (vc ⟨c.1.1, c.1.2⟩) * fam ⟨c.1.1, c.1.2⟩)
      have hΨc : Ψ' c.1 = Ψ (fam c.1) := (dif_pos c.1.2 : Ψ' c.1 = Ψ (fam ⟨c.1.1, c.1.2⟩))
      simp only [Function.comp_apply, e, Equiv.sigmaFiberEquiv_apply]
      rw [hrepc, hΨc, hfam_eq c]
      rfl
    rw [hfun]
    exact hper r
  have h1 : HasSum (fun r : R => term r) _ := hG2'.sigma hfib

  have hfin := AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
    K L σ hgen D φ hφc R hRsub hR
  have hfinR : {r : R | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L r *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.Finite := by
    refine (hfin.preimage (Subtype.val_injective.injOn)).subset fun r hr => ?_
    exact ⟨r.2, hr⟩
  set TT : Finset R := hfinR.toFinset with hTT
  have hzero : ∀ r : R, r ∉ TT → term r = 0 := by
    intro r hr
    rw [hTT, Set.Finite.mem_toFinset] at hr
    simp only [Set.mem_setOf_eq, not_exists, not_not] at hr
    simp only [term]
    have : ∀ z, (∫ x in Ψ r, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L r *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0 := by
      intro z
      simp only [hr, integral_zero]
    simp only [this, mul_zero, integral_zero]
  have h2 : HasSum (fun r : R => term r) (∑ r ∈ TT, term r) := hasSum_sum_of_ne_finset_zero hzero
  refine (h1.unique h2).trans ?_

  show ∑ r ∈ TT, term r = ∑ᶠ δ₀ ∈ R, term δ₀
  rw [finsum_mem_eq_sum_of_subset term (t := TT.image Subtype.val) ?_ ?_]
  · rw [Finset.sum_image fun r _ r' _ h => Subtype.val_injective h]
  · rintro δ₀ ⟨hδ₀R, hne⟩
    rw [Finset.coe_image]
    refine ⟨⟨δ₀, hδ₀R⟩, ?_, rfl⟩
    by_contra hnot
    exact hne (hzero ⟨δ₀, hδ₀R⟩ hnot)
  · intro δ₀ hδ₀
    rw [Finset.coe_image] at hδ₀
    obtain ⟨r, -, rfl⟩ := hδ₀
    exact r.2

end Main

end R2UnfL
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain.R2UnfL"

section
open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

p2m_open "AutomorphicForm~ideleNorm_det_globalPoints" in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Ω νZ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (R : Set (GL (Fin 2) L))
    (hRsub : R ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (hR : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ R ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h))
    (Ψ : GL (Fin 2) L → Set (AdelicGL2 (𝓞 L) L))
    (hΨs : ∀ δ₀ ∈ R, Ψ δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : ∀ δ₀ ∈ R, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZ) :
    (∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
              ConjClasses.mk γ},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZ)
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
    ∑ᶠ δ₀ ∈ R,
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in Ψ δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZ :=
  R2UnfL.main K L σ hgen α β hα hαβ Φ hΦs hΦ νZ Ω hΩ D ξ hξc hξt φ hφ hφc R hRsub hR Ψ hΨs hΨ Θ hΘ

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain.R2UnfL"

end
end S_AutomorphicForm_setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain (solution)
