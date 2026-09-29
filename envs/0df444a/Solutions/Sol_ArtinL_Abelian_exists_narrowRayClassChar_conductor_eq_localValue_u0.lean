-- Prove2me | solution 1 for ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/dfba6945-85e2-5e5a-b077-a0bbe1e12ff0

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_ArtinL_Abelian_apply_artinSymbol_eq_prod_sign_of_sub_one_mem_conductor_u0
import Theorems.Thm_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_conductor_lt_u0
import Theorems.Thm_ArtinL_Abelian_conductor_comp_restrictNormalHom
import Theorems.Thm_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt
import Theorems.Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b"
p2m_attr_erase "simp" "AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply"
p2m_attr_erase "simp" "galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin

noncomputable section

namespace ArtinCharAssembly

open scoped nonZeroDivisors

section Clauses

variable (K : Type) [Field K] [NumberField K]

def Clauses (𝔣 : Ideal (𝓞 K)) (loc : HeightOneSpectrum (𝓞 K) → ℂ)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (P : Prop)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), χ (primeClass K 𝔣 v hv) = loc v) ∧
  (χ = 1 ↔ P) ∧
  (∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
    α - 1 ∈ 𝔣 →
      χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
        ∏ w ∈ S, ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) ∧
  (∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
    ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1)

theorem Clauses.transfer {𝔣 𝔣' : Ideal (𝓞 K)} (h : 𝔣 = 𝔣')
    {loc loc' : HeightOneSpectrum (𝓞 K) → ℂ} (hloc : ∀ v, loc v = loc' v)
    {S S' : Finset {w : InfinitePlace K // w.IsReal}} (hS : S = S')
    {P P' : Prop} (hP : P ↔ P')
    (H : ∃ χ, Clauses K 𝔣' loc' S' P' χ) : ∃ χ, Clauses K 𝔣 loc S P χ := by
  subst h hS
  obtain rfl : loc = loc' := funext hloc
  obtain rfl : P = P' := propext hP
  exact H

end Clauses

section Abelian

open scoped IsMulCommutative

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (φ : (L ≃ₐ[K] L) →* ℂˣ)

def frobValue : HeightOneSpectrum (𝓞 K) → ℂˣ := fun v => φ (artinFrob K L v)

omit [IsMulCommutative (L ≃ₐ[K] L)] in
@[scoped simp] theorem frobValue_apply (v : HeightOneSpectrum (𝓞 K)) :
    frobValue K L φ v = φ (artinFrob K L v) := rfl

theorem map_raySymbol (I : FractionalIdeal ((𝓞 K)⁰) K) :
    φ (raySymbol K (artinFrob K L) I) = raySymbol K (frobValue K L φ) I := by
  unfold raySymbol
  rw [φ.map_finprod (hasFiniteMulSupport_raySymbol_factors K (artinFrob K L) I)]
  refine finprod_congr fun v => ?_
  rw [map_zpow]
  rfl

theorem apply_artinSymbol (𝔪 : Ideal (𝓞 K)) (y : ↥(coprimeToModulus K 𝔪)) :
    φ (artinSymbol K L 𝔪 y) = raySymbolHom K 𝔪 (frobValue K L φ) y := by
  rw [raySymbolHom_apply, ← map_raySymbol]
  rfl

open scoped Classical in

theorem raySymbol_frobValue_span_eq_one (α : 𝓞 K) (hα : α ≠ 0)
    (h1 : α - 1 ∈ ArtinL.Abelian.conductor φ) (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    raySymbol K (frobValue K L φ)
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  have hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor φ) :=
    principalUnit_mem_coprimeToModulus K hα h1
  have hS := ArtinL.Abelian.apply_artinSymbol_eq_prod_sign_of_sub_one_mem_conductor_u0 K L φ
    (ArtinL.Abelian.conductor φ) α hα hc h1
  have hprod : (∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
      ¬ ArtinL.Abelian.IsPlusAt φ w.1),
        ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [sign_pos (hpos _)]
    simp
  rw [hprod, Units.val_eq_one, apply_artinSymbol, raySymbolHom_apply] at hS
  rwa [principalUnit_val] at hS

def chi : NarrowRayClassGroup K (ArtinL.Abelian.conductor φ) →* ℂ :=
  (Units.coeHom ℂ).comp
    (raySymbolDescend K (frobValue K L φ)
      (fun α hα h1 hpos => raySymbol_frobValue_span_eq_one K L φ α hα h1 hpos))

theorem chi_mk (y : ↥(coprimeToModulus K (ArtinL.Abelian.conductor φ))) :
    chi K L φ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor φ) y) =
      ((raySymbolHom K (ArtinL.Abelian.conductor φ) (frobValue K L φ) y : ℂˣ) : ℂ) := by
  rw [chi, MonoidHom.comp_apply, raySymbolDescend_mk]
  rfl

theorem chi_primeClass (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor φ) :
    chi K L φ (primeClass K (ArtinL.Abelian.conductor φ) v hv) =
      ((φ (artinFrob K L v) : ℂˣ) : ℂ) := by
  rw [chi, MonoidHom.comp_apply, raySymbolDescend_primeClass]
  rfl

theorem chi_mk_principalUnit (α : 𝓞 K) (hα : α ≠ 0)
    (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor φ)) :
    chi K L φ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor φ) ⟨principalUnit K α hα, hc⟩) =
      ((φ (artinSymbol K L (ArtinL.Abelian.conductor φ) ⟨principalUnit K α hα, hc⟩) : ℂˣ) : ℂ) := by
  rw [chi_mk, apply_artinSymbol]

omit [IsMulCommutative (L ≃ₐ[K] L)] in

theorem isUnramifiedAt_of_not_dvd (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor φ) : ArtinL.Abelian.IsUnramifiedAt φ v := by
  by_contra h
  exact hv ((ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt K L φ v).2 h)

theorem chi_primeClass_eq_localValue (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor φ) :
    chi K L φ (primeClass K (ArtinL.Abelian.conductor φ) v hv) = ArtinL.Abelian.localValue φ v := by
  rw [chi_primeClass, ArtinL.Abelian.localValue, if_pos (isUnramifiedAt_of_not_dvd K L φ v hv)]

open scoped Classical in

theorem chi_mk_principalUnit_eq_prod_sign (α : 𝓞 K) (hα : α ≠ 0)
    (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor φ))
    (h1 : α - 1 ∈ ArtinL.Abelian.conductor φ) :
    chi K L φ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor φ) ⟨principalUnit K α hα, hc⟩) =
      ∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
          ¬ ArtinL.Abelian.IsPlusAt φ w.1),
        ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ) := by
  rw [chi_mk_principalUnit]
  exact ArtinL.Abelian.apply_artinSymbol_eq_prod_sign_of_sub_one_mem_conductor_u0 K L φ
    (ArtinL.Abelian.conductor φ) α hα hc h1

theorem chi_primitive (𝔣' : Ideal (𝓞 K)) (hle : ArtinL.Abelian.conductor φ ≤ 𝔣')
    (hne : 𝔣' ≠ ArtinL.Abelian.conductor φ) :
    ∃ (α : 𝓞 K) (hα : α ≠ 0)
      (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor φ)),
      α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
        chi K L φ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor φ)
          ⟨principalUnit K α hα, hc⟩) ≠ 1 := by
  obtain ⟨α, hα, hc, h1, hpos, hne1⟩ :=
    ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_conductor_lt_u0 K L φ 𝔣' hle hne
  refine ⟨α, hα, hc, h1, hpos, ?_⟩
  rwa [chi_mk_principalUnit, Ne, Units.val_eq_one]

theorem chi_eq_one_of_eq_one (h : φ = 1) : chi K L φ = 1 := by
  subst h
  refine MonoidHom.ext fun x => QuotientGroup.induction_on x fun y => ?_
  change chi K L 1 (NarrowRayClassGroup.mk K _ y) = 1
  rw [chi_mk, raySymbolHom_apply, raySymbol]
  simp

omit [NumberField K] in

theorem admissibleExpOfDegree_ne_zero (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.NormIndex.admissibleExpOfDegree K n v ≠ 0 := by
  unfold NumberField.NormIndex.admissibleExpOfDegree
  omega

omit [IsMulCommutative (L ≃ₐ[K] L)] in

theorem dvd_conductor_of_inertia_ne_bot (hφ : Function.Injective φ) (v : HeightOneSpectrum (𝓞 K))
    (hv : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥) :
    v.asIdeal ∣ ArtinL.Abelian.conductor φ := by
  rw [ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt K L φ v]
  obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hv
  intro hun
  apply hσ1
  have h1 : φ σ = 1 := hun σ hσ
  exact Subtype.ext (hφ (h1.trans (map_one φ).symm))

theorem eq_one_of_forall_frob (hφ : Function.Injective φ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)), ¬ v.asIdeal ∣ ArtinL.Abelian.conductor φ →
      φ (artinFrob K L v) = 1) : φ = 1 := by
  classical
  set 𝔣 := ArtinL.Abelian.conductor φ with h𝔣def
  have h𝔣 : 𝔣 ≠ ⊥ := ArtinL.Abelian.conductor_ne_bot φ
  set n := Module.finrank K L with hndef
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  have hexp : ∀ x : L ≃ₐ[K] L, x ^ n = 1 := fun x => by
    rw [hndef, ← IsGalois.card_aut_eq_finrank K L]
    exact pow_card_eq_one'
  set T : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors h𝔣).toFinset with hTdef
  have hT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ T ↔ v.asIdeal ∣ 𝔣 := fun v => by
    rw [hTdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  set 𝔪 : Ideal (𝓞 K) := ∏ v ∈ T, v.asIdeal ^ NumberField.NormIndex.admissibleExpOfDegree K n v
    with h𝔪def
  have h𝔪0 : 𝔪 ≠ ⊥ := by
    rw [h𝔪def, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ideal.zero_eq_bot]
    exact pow_ne_zero _ v.ne_bot
  have hdvd𝔪 : ∀ v ∈ T, v.asIdeal ∣ 𝔪 := fun v hv =>
    (dvd_pow_self v.asIdeal (admissibleExpOfDegree_ne_zero K n v)).trans
      (Finset.dvd_prod_of_mem _ hv)
  have hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L n 𝔪 := by
    refine ⟨h𝔪0, fun v hv => ?_⟩
    have hvT : v ∈ T := (hT v).2 (dvd_conductor_of_inertia_ne_bot K L φ hφ v hv)
    exact Finset.dvd_prod_of_mem _ hvT
  obtain ⟨hsurj, -⟩ :=
    LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
      K L n hn hexp 𝔪 hadm
  refine MonoidHom.ext fun σ => ?_
  obtain ⟨y, rfl⟩ := hsurj σ
  rw [MonoidHom.one_apply, apply_artinSymbol, raySymbolHom_apply, raySymbol]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔪
  · rw [(mem_coprimeToModulus_iff K).1 y.2 v hv, zpow_zero]
  · have hv' : ¬ v.asIdeal ∣ 𝔣 := fun h' => hv (hdvd𝔪 v ((hT v).2 h'))
    rw [frobValue_apply, h v hv', one_zpow]

theorem eq_one_of_chi_eq_one (hφ : Function.Injective φ) (h : chi K L φ = 1) : φ = 1 := by
  refine eq_one_of_forall_frob K L φ hφ fun v hv => ?_
  have h' := congrArg (fun χ : NarrowRayClassGroup K (ArtinL.Abelian.conductor φ) →* ℂ =>
    χ (primeClass K (ArtinL.Abelian.conductor φ) v hv)) h
  simp only [MonoidHom.one_apply] at h'
  rwa [chi_primeClass, Units.val_eq_one] at h'

open scoped Classical in

theorem clauses_of_injective (hφ : Function.Injective φ) :
    ∃ χ, Clauses K (ArtinL.Abelian.conductor φ) (ArtinL.Abelian.localValue φ)
      (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
        ¬ ArtinL.Abelian.IsPlusAt φ w.1) (φ = 1) χ := by
  refine ⟨chi K L φ, fun v hv => chi_primeClass_eq_localValue K L φ v hv,
    ⟨eq_one_of_chi_eq_one K L φ hφ, chi_eq_one_of_eq_one K L φ⟩,
    fun α hα hc h1 => chi_mk_principalUnit_eq_prod_sign K L φ α hα hc h1,
    fun 𝔣' hle hne => chi_primitive K L φ 𝔣' hle hne⟩

end Abelian

section Descent

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

def descend :
    ((IntermediateField.fixedField ψ.ker) ≃ₐ[K] (IntermediateField.fixedField ψ.ker)) →* ℂˣ :=
  (QuotientGroup.kerLift ψ).comp (IsGalois.normalAutEquivQuotient ψ.ker).symm.toMonoidHom

theorem descend_restrictNormalHom (σ : M ≃ₐ[K] M) :
    descend K M ψ (AlgEquiv.restrictNormalHom (K₁ := M) (IntermediateField.fixedField ψ.ker) σ) =
      ψ σ := by
  rw [descend, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← IsGalois.normalAutEquivQuotient_apply, MulEquiv.symm_apply_apply, QuotientGroup.kerLift_mk]

theorem descend_comp :
    (descend K M ψ).comp (AlgEquiv.restrictNormalHom (K₁ := M) (IntermediateField.fixedField ψ.ker)) =
      ψ :=
  MonoidHom.ext (descend_restrictNormalHom K M ψ)

theorem descend_injective : Function.Injective (descend K M ψ) :=
  (QuotientGroup.kerLift_injective ψ).comp (MulEquiv.injective _)

theorem isMulCommutative_fixedField :
    IsMulCommutative
      ((IntermediateField.fixedField ψ.ker) ≃ₐ[K] (IntermediateField.fixedField ψ.ker)) :=
  ⟨⟨fun a b => descend_injective K M ψ (by rw [map_mul, map_mul, mul_comm])⟩⟩

theorem descend_eq_one_iff : descend K M ψ = 1 ↔ ψ = 1 := by
  constructor
  · intro h
    rw [← descend_comp K M ψ, h, MonoidHom.one_comp]
  · intro h
    refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M x
    rw [descend_restrictNormalHom, h, MonoidHom.one_apply, MonoidHom.one_apply]

end Descent

section Main

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

open scoped Classical in
theorem main :
    ∃ χ : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ) →* ℂ,
      (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor ψ),
        χ (primeClass K (ArtinL.Abelian.conductor ψ) v hv) = ArtinL.Abelian.localValue ψ v) ∧
      (χ = 1 ↔ ψ = 1) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0)
        (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
        α - 1 ∈ ArtinL.Abelian.conductor ψ →
          χ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ) ⟨principalUnit K α hα, hc⟩) =
            ∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
                ¬ ArtinL.Abelian.IsPlusAt ψ w.1),
              ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) ∧
      (∀ 𝔣' : Ideal (𝓞 K), ArtinL.Abelian.conductor ψ ≤ 𝔣' → 𝔣' ≠ ArtinL.Abelian.conductor ψ →
        ∃ (α : 𝓞 K) (hα : α ≠ 0)
          (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
          α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
            χ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ)
              ⟨principalUnit K α hα, hc⟩) ≠ 1) := by

  haveI := isMulCommutative_fixedField K M ψ
  have hcomp := descend_comp K M ψ
  obtain ⟨h1, h2, h3⟩ := ArtinL.Abelian.conductor_comp_restrictNormalHom K
    (IntermediateField.fixedField ψ.ker) M (descend K M ψ)
  rw [hcomp] at h1 h2 h3
  change ∃ χ, Clauses K (ArtinL.Abelian.conductor ψ) (ArtinL.Abelian.localValue ψ) _ (ψ = 1) χ
  refine Clauses.transfer K h1 h2 (Finset.filter_congr fun w _ => not_congr (h3 w.1))
    (descend_eq_one_iff K M ψ).symm ?_
  exact clauses_of_injective K _ (descend K M ψ) (descend_injective K M ψ)

end Main

end ArtinCharAssembly
p2m_reactivate "P2MW.S_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0.ArtinCharAssembly"

end
p2m_reactivate "P2MW.S_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0.ArtinCharAssembly"

open scoped Classical in

theorem solution
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    ∃ χ : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ) →* ℂ,
      (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor ψ),
        χ (primeClass K (ArtinL.Abelian.conductor ψ) v hv) = ArtinL.Abelian.localValue ψ v) ∧
      (χ = 1 ↔ ψ = 1) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0)
        (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
        α - 1 ∈ ArtinL.Abelian.conductor ψ →
          χ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ) ⟨principalUnit K α hα, hc⟩) =
            ∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
                ¬ ArtinL.Abelian.IsPlusAt ψ w.1),
              ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) ∧
      (∀ 𝔣' : Ideal (𝓞 K), ArtinL.Abelian.conductor ψ ≤ 𝔣' → 𝔣' ≠ ArtinL.Abelian.conductor ψ →
        ∃ (α : 𝓞 K) (hα : α ≠ 0)
          (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
          α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
            χ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ)
              ⟨principalUnit K α hα, hc⟩) ≠ 1) :=
  ArtinCharAssembly.main K M ψ

end S_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0
end P2MW
export P2MW.S_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0 (solution)
