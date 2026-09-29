-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ff8b66bd-9037-581f-86c8-52b9ead63372

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul"
p2m_attr_erase "simp" "NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun"
p2m_attr_erase "simp" "FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

open NumberField
open scoped MatrixGroups

namespace R4VC

section GLFacts

variable {R : Type*} [CommRing R]

theorem val_scalar (u : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.diagonal fun _ => (u : R) := rfl

theorem val_scalar_apply (u : Rˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      if i = j then (u : R) else 0 := by
  rw [val_scalar, Matrix.diagonal_apply]

theorem map_scalar {S : Type*} [CommRing S] (f : R →+* S) (u : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) u) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, val_scalar_apply, val_scalar_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, map_zero]

theorem scalar_injective : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Rˣ → GL (Fin 2) R) := by
  intro a b h
  have h' := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0) h
  simp only [val_scalar_apply, if_true] at h'
  exact Units.ext h'

theorem scalar_mem_center (u : Rˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.center (GL (Fin 2) R) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

theorem scalar_comm (u : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u :=
  ((Subgroup.mem_center_iff.mp (scalar_mem_center u)) g).symm

theorem exists_scalar_of_mem_center {z : GL (Fin 2) R} (hz : z ∈ Subgroup.center (GL (Fin 2) R)) :
    ∃ u : Rˣ, z = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, rfl⟩ := hz
  exact ⟨u, rfl⟩

theorem continuous_scalar [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) : Rˣ → GL (Fin 2) R) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun u : Rˣ =>
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    simp_rw [val_scalar]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
  · show Continuous fun u : Rˣ =>
      (((Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    simp_rw [← map_inv, val_scalar]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)

end GLFacts

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

noncomputable abbrev uτ (τ : L ≃ₐ[K] L) : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ := (D.unitsAct τ).toMonoidHom

theorem uτ_apply (τ : L ≃ₐ[K] L) (u : (AdeleRing (𝓞 L) L)ˣ) : uτ K L D τ u = D.unitsAct τ u := rfl

theorem sigmaAdelicAct_scalar (τ : L ≃ₐ[K] L) (u : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D τ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (uτ K L D τ u) := by
  unfold AutomorphicForm.sigmaAdelicAct
  rw [map_scalar]
  rfl

theorem uτ_mul_apply (τ τ' : L ≃ₐ[K] L) (u : (AdeleRing (𝓞 L) L)ˣ) :
    uτ K L D (τ * τ') u = uτ K L D τ (uτ K L D τ' u) := by
  show D.unitsAct (τ * τ') u = D.unitsAct τ (D.unitsAct τ' u)
  rw [map_mul]; rfl

theorem uτ_one_apply (u : (AdeleRing (𝓞 L) L)ˣ) : uτ K L D 1 u = u := by
  show D.unitsAct 1 u = u
  rw [map_one]; rfl

theorem prod_succ (u : (AdeleRing (𝓞 L) L)ˣ) (k : ℕ) :
    ∏ j ∈ Finset.range (k + 1), uτ K L D (σ ^ j) u = u * uτ K L D σ (∏ j ∈ Finset.range k, uτ K L D (σ ^ j) u) := by
  rw [Finset.prod_range_succ', pow_zero, uτ_one_apply, mul_comm, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← uτ_mul_apply, ← pow_succ']

theorem iterate_eq (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (u : (AdeleRing (𝓞 L) L)ˣ)
    (hg : g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g = Matrix.GeneralLinearGroup.scalar (Fin 2) u) (k : ℕ) :
    AutomorphicForm.sigmaAdelicAct K L D (σ ^ k) g =
      g * Matrix.GeneralLinearGroup.scalar (Fin 2) (∏ j ∈ Finset.range k, uτ K L D (σ ^ j) u) := by
  have hg' : AutomorphicForm.sigmaAdelicAct K L D σ g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    rw [← hg, mul_inv_cancel_left]
  induction k with
  | zero =>
    rw [pow_zero, AutomorphicForm.sigmaAdelicAct_one, Finset.prod_range_zero, map_one, mul_one]
    rfl
  | succ k ih =>
    rw [pow_succ', AutomorphicForm.sigmaAdelicAct_mul, MonoidHom.comp_apply, ih, map_mul, hg',
      sigmaAdelicAct_scalar, prod_succ, map_mul, mul_assoc]

theorem orderOf_pos_aut : 0 < orderOf σ := by

  let f : (L ≃ₐ[K] L) → (L ≃ₐ[ℚ] L) := fun τ => AlgEquiv.ofRingEquiv (f := (τ : L ≃+* L)) (fun q => by simp)
  have hf : Function.Injective f := by
    intro a b h
    ext x
    exact congrArg (fun e : L ≃ₐ[ℚ] L => e x) h
  haveI : Finite (L ≃ₐ[K] L) := Finite.of_injective f hf
  exact orderOf_pos σ

theorem prod_eq_one (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (u : (AdeleRing (𝓞 L) L)ˣ)
    (hg : g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g = Matrix.GeneralLinearGroup.scalar (Fin 2) u) :
    ∏ j ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ j) u = 1 := by
  have h := iterate_eq K L σ D g u hg (orderOf σ)
  rw [pow_orderOf_eq_one, AutomorphicForm.sigmaAdelicAct_one, MonoidHom.id_apply] at h
  have h2 : Matrix.GeneralLinearGroup.scalar (Fin 2) (∏ j ∈ Finset.range (orderOf σ), uτ K L D (σ ^ j) u) = 1 :=
    mul_left_cancel (a := g) (by rw [mul_one]; exact h.symm)
  rw [← map_one (Matrix.GeneralLinearGroup.scalar (Fin 2))] at h2
  exact scalar_injective h2

noncomputable def normHom : (AdeleRing (𝓞 L) L)ˣ →* ℝ where
  toFun := NumberField.TateGlobal.ideleNorm L
  map_one' := by
    have h := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
    rw [one_mul] at h
    have h1 := NumberField.TateGlobal.ideleNorm_pos (F := L) 1
    nlinarith [h, h1]
  map_mul' := NumberField.TateGlobal.ideleNorm_mul

theorem normHom_apply (x : (AdeleRing (𝓞 L) L)ˣ) : normHom L x = NumberField.TateGlobal.ideleNorm L x := rfl

theorem ideleNorm_uτ (τ : L ≃ₐ[K] L) (x : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (uτ K L D τ x) = NumberField.TateGlobal.ideleNorm L x := by
  have h := AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D τ (Matrix.GeneralLinearGroup.scalar (Fin 2) x)
  rw [sigmaAdelicAct_scalar] at h
  have hdet : ∀ y : (AdeleRing (𝓞 L) L)ˣ,
      Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) y) = y * y := by
    intro y
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalar, Matrix.det_diagonal, Fin.prod_univ_two, Units.val_mul]
  rw [hdet, hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul] at h
  have h1 := NumberField.TateGlobal.ideleNorm_pos (F := L) (uτ K L D τ x)
  have h2 := NumberField.TateGlobal.ideleNorm_pos (F := L) x
  nlinarith [h, h1, h2, sq_nonneg (NumberField.TateGlobal.ideleNorm L (uτ K L D τ x) - NumberField.TateGlobal.ideleNorm L x),
    sq_nonneg (NumberField.TateGlobal.ideleNorm L (uτ K L D τ x) + NumberField.TateGlobal.ideleNorm L x)]

theorem exists_fixed_ideleNorm_eq (t : ℝ) (ht : 0 < t) :
    ∃ r : (AdeleRing (𝓞 L) L)ˣ, uτ K L D σ r = r ∧ NumberField.TateGlobal.ideleNorm L r = t := by
  have hnpos : 0 < orderOf σ := orderOf_pos_aut K L σ
  obtain ⟨r₀, -, hr₀⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one L (t ^ ((1 : ℝ) / (orderOf σ)))
    (Real.rpow_pos_of_pos ht _)
  refine ⟨∏ j ∈ Finset.range (orderOf σ), uτ K L D (σ ^ j) r₀, ?_, ?_⟩
  ·
    rw [map_prod]
    have h1 : ∀ j, uτ K L D σ (uτ K L D (σ ^ j) r₀) = uτ K L D (σ ^ (j + 1)) r₀ := fun j => by
      rw [← uτ_mul_apply, ← pow_succ']
    simp_rw [h1]
    have key := Finset.prod_range_succ' (fun j => uτ K L D (σ ^ j) r₀) (orderOf σ)
    rw [Finset.prod_range_succ, pow_zero, uτ_one_apply, pow_orderOf_eq_one, uτ_one_apply] at key
    exact mul_right_cancel key.symm
  · rw [← normHom_apply, map_prod]
    simp_rw [normHom_apply, ideleNorm_uτ, hr₀, Finset.prod_const, Finset.card_range]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, one_div, inv_mul_cancel₀ (Nat.cast_pos.mpr hnpos).ne',
      Real.rpow_one]

theorem globalPoints_scalar (l : Lˣ) :
    AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) l) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) l) := by
  unfold AutomorphicForm.globalPoints
  rw [map_scalar]

theorem main :
    ∃ C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L), IsCompact C ∧
      C ⊆ (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) ∧
      ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g ∈
            Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) →
          ∃ (h c : AutomorphicForm.AdelicGL2 (𝓞 L) L) (l : Lˣ),
            AutomorphicForm.sigmaAdelicAct K L D σ h = h ∧ c ∈ C ∧
              g = h * c * AutomorphicForm.globalPoints (𝓞 L) L
                (Matrix.GeneralLinearGroup.scalar (Fin 2) l) := by

  obtain ⟨K₁, hK₁c, -, hK₁⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) '' K₁, hK₁c.image continuous_scalar, ?_, ?_⟩
  · rintro _ ⟨κ, -, rfl⟩
    exact scalar_mem_center κ
  intro g hg

  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hg

  obtain ⟨w, hw⟩ := M4aHerbrand.IdeleGaloisDescent.exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
    K L σ D u (prod_eq_one K L σ D g u hu)
  have hσg : AutomorphicForm.sigmaAdelicAct K L D σ g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    rw [← hu, mul_inv_cancel_left]
  set h₀ : AutomorphicForm.AdelicGL2 (𝓞 L) L := g * (Matrix.GeneralLinearGroup.scalar (Fin 2) w)⁻¹ with hh₀
  have hh₀fix : AutomorphicForm.sigmaAdelicAct K L D σ h₀ = h₀ := by
    rw [hh₀, map_mul, map_inv, hσg, sigmaAdelicAct_scalar, mul_assoc, ← map_inv, ← map_mul, hw, uτ_apply,
      mul_inv_cancel_right, map_inv]

  obtain ⟨r, hrfix, hrnorm⟩ := exists_fixed_ideleNorm_eq K L σ D (NumberField.TateGlobal.ideleNorm L w)
    (NumberField.TateGlobal.ideleNorm_pos w)
  have hwr : w * r⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, ← normHom_apply, map_mul]
    have hr1 : normHom L r⁻¹ * normHom L r = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [normHom_apply L r, hrnorm, ← normHom_apply] at hr1
    rw [mul_comm]
    exact hr1
  obtain ⟨η, κ, hκ, hwr'⟩ := hK₁ _ hwr

  refine ⟨h₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) r, Matrix.GeneralLinearGroup.scalar (Fin 2) κ, η, ?_,
    ⟨κ, hκ, rfl⟩, ?_⟩
  · rw [map_mul, hh₀fix, sigmaAdelicAct_scalar, hrfix]
  · have hw' : w = r * κ * ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom) η) := by
      have : w = (w * r⁻¹) * r := by rw [inv_mul_cancel_right]
      rw [this, hwr']
      simp only [RingHom.toMonoidHom_eq_coe]
      rw [mul_comm _ κ, mul_assoc, mul_comm _ r, ← mul_assoc, mul_comm κ r]
    rw [globalPoints_scalar]
    have hg' : g = h₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
      rw [hh₀, inv_mul_cancel_right]
    rw [hg', hw', map_mul, map_mul, ← mul_assoc, ← mul_assoc]
    rfl

end Main

end R4VC

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :
    ∃ C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L), IsCompact C ∧
      C ⊆ (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) ∧
      ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g ∈
            Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) →
          ∃ (h c : AutomorphicForm.AdelicGL2 (𝓞 L) L) (l : Lˣ),
            AutomorphicForm.sigmaAdelicAct K L D σ h = h ∧ c ∈ C ∧
              g = h * c * AutomorphicForm.globalPoints (𝓞 L) L
                (Matrix.GeneralLinearGroup.scalar (Fin 2) l) :=
  R4VC.main K L σ D

end S_AutomorphicForm_exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center (solution)
