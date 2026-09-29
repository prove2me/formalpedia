-- Prove2me | solution 1 for ArtinL.Abelian.exists_completedLSeries_functionalEquation_u0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b5ce2ed4-861d-5ded-8d5e-b17ea809207b

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_NumberField_CompletedRayL
import Theorems.Thm_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0
import Theorems.Thm_NumberField_exists_completedRayL_functionalEquation_of_primitive
import Theorems.Thm_ArtinL_Abelian_lSeries_eq_rayClassLSeries_of_eq_localValue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_exists_completedLSeries_functionalEquation_u0
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension"
p2m_attr_erase "instance" "NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top"
p2m_attr_erase "simp" "ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one"
p2m_attr_erase "simp" "groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace ArtinRecipAssembly

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply ArtinL.Abelian
open scoped Classical

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

omit [NumberField M] [IsGalois K M] in
theorem ramificationGroup_succ_le (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    ramificationGroup K M v (i + 1) ≤ inertiaGroup K M v := by
  intro σ hσ x
  have h := hσ x
  exact Ideal.pow_le_self (Nat.succ_ne_zero _) h

omit [IsGalois K M] in
theorem swanConductor_eq_zero_of_isUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (h : IsUnramifiedAt ψ v) : swanConductor ψ v = 0 := by
  unfold swanConductor
  refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
  rw [if_pos, mul_zero]
  intro σ hσ
  exact h σ (ramificationGroup_succ_le v i hσ)

omit [IsGalois K M] in
theorem conductorExponent_eq_zero_of_isUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (h : IsUnramifiedAt ψ v) : conductorExponent ψ v = 0 := by
  rw [conductorExponent, if_pos h, swanConductor_eq_zero_of_isUnramifiedAt ψ v h]
  simp

omit [IsGalois K M] in

theorem not_isUnramifiedAt_of_dvd_conductor (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ conductor ψ) : ¬ IsUnramifiedAt ψ v := by
  intro hunr
  have hf0 := conductorExponent_eq_zero_of_isUnramifiedAt ψ v hunr
  unfold ArtinL.Abelian.conductor at hv
  by_cases hfin : Function.HasFiniteMulSupport
      fun w : HeightOneSpectrum (𝓞 K) ↦ w.asIdeal ^ conductorExponent ψ w
  · rw [finprod_eq_prod _ hfin] at hv
    have hprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    obtain ⟨w, hw, hvw⟩ := (Prime.dvd_finsetProd_iff hprime _).1 hv
    have hvw' : v.asIdeal ∣ w.asIdeal := hprime.dvd_of_dvd_pow hvw
    have heq : v = w := by
      have hle : w.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd hvw'
      exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hle).symm
    subst heq
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, hf0, pow_zero] at hw
    exact hw rfl
  · rw [finprod_of_infinite_mulSupport hfin, Ideal.one_eq_top] at hv
    exact v.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hv))

omit [NumberField M] [IsGalois K M] in
theorem card_filter_not_isPlusAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} ↦ ¬ IsPlusAt ψ w.1).card =
      nMinus ψ := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}))
    (fun w : {w : InfinitePlace K // w.IsReal} ↦ IsPlusAt ψ w.1)
  have h2 : (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} ↦ IsPlusAt ψ w.1).card =
      nPlus ψ := by
    rw [nPlus, Nat.card_eq_fintype_card, ← Fintype.card_subtype,
      Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)]
  rw [Finset.card_univ, h2] at h1
  rw [nMinus, nrRealPlaces, ← h1, Nat.add_sub_cancel_left]

theorem completedLSeries_eq (ψ φ : (M ≃ₐ[K] M) →* ℂˣ) (hcond : conductor φ = conductor ψ)
    (hplus : nPlus φ = nPlus ψ) (hminus : nMinus φ = nMinus ψ)
    (χ : NarrowRayClassGroup K (conductor ψ) →* ℂ)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (hS : S.card = nMinus ψ) {s : ℂ}
    (hL : ArtinL.Abelian.LSeries φ s = M4aTorus.rayClassLSeries K (conductor ψ) χ s) :
    completedLSeries φ s = M4aTorus.completedRayL K (conductor ψ) χ S s := by
  rw [completedLSeries, M4aTorus.completedRayL, hL, hcond, hplus, hminus, hS,
    ← nPlus_add_nMinus ψ, Nat.add_sub_cancel]

theorem main (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = (if ψ = 1 then s * (s - 1) else 1) * completedLSeries ψ s ∧
        Λ' s = (if ψ = 1 then s * (s - 1) else 1) * completedLSeries ψ⁻¹ s) ∧
      (∀ s : ℂ, Λ (1 - s) = W * Λ' s) := by
  obtain ⟨χ, hχ, h1, hpar, hprim⟩ :=
    ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ
  have h𝔣 : conductor ψ ≠ ⊥ := conductor_ne_bot ψ
  have hram : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ conductor ψ → ¬ IsUnramifiedAt ψ v :=
    fun v hv ↦ not_isUnramifiedAt_of_dvd_conductor ψ v hv
  have hL : ∀ s : ℂ, 1 < s.re →
      ArtinL.Abelian.LSeries ψ s = M4aTorus.rayClassLSeries K (conductor ψ) χ s :=
    fun s hs ↦ ArtinL.Abelian.lSeries_eq_rayClassLSeries_of_eq_localValue K M ψ (conductor ψ)
      h𝔣 χ hχ hram hs

  set χ' : NarrowRayClassGroup K (conductor ψ) →* ℂ := (starRingEnd ℂ).toMonoidHom.comp χ
    with hχ'def
  have hχ' : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ conductor ψ),
      χ' (primeClass K (conductor ψ) v hv) = localValue ψ⁻¹ v := by
    intro v hv
    rw [hχ'def, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hχ v hv,
      localValue_inv]
  have hram' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ conductor ψ →
      ¬ IsUnramifiedAt ψ⁻¹ v := by
    intro v hv
    rw [isUnramifiedAt_inv_iff]
    exact hram v hv
  have hL' : ∀ s : ℂ, 1 < s.re →
      ArtinL.Abelian.LSeries ψ⁻¹ s = M4aTorus.rayClassLSeries K (conductor ψ) χ' s :=
    fun s hs ↦ ArtinL.Abelian.lSeries_eq_rayClassLSeries_of_eq_localValue K M ψ⁻¹ (conductor ψ)
      h𝔣 χ' hχ' hram' hs

  obtain ⟨W, Λ, Λ', hW, hΛ, hΛ', heq, hFE⟩ :=
    NumberField.exists_completedRayL_functionalEquation_of_primitive K (conductor ψ) h𝔣 χ _
      hpar hprim
  have hS := card_filter_not_isPlusAt (K := K) ψ
  refine ⟨W, Λ, Λ', hW, hΛ, hΛ', fun s hs ↦ ?_, hFE⟩
  obtain ⟨e1, e2⟩ := heq s hs
  have hP : (if χ = 1 then s * (s - 1) else (1 : ℂ)) = (if ψ = 1 then s * (s - 1) else 1) := by
    by_cases hψ : ψ = 1
    · rw [if_pos hψ, if_pos (h1.2 hψ)]
    · rw [if_neg hψ, if_neg (fun h ↦ hψ (h1.1 h))]
  refine ⟨?_, ?_⟩
  · rw [e1, hP, completedLSeries_eq ψ ψ rfl rfl rfl χ _ hS (hL s hs)]
  · rw [e2, hP, completedLSeries_eq ψ ψ⁻¹ (conductor_inv ψ) (nPlus_inv ψ) (nMinus_inv ψ) χ' _ hS
      (hL' s hs)]

end ArtinRecipAssembly

end

theorem solution
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = (if ψ = 1 then s * (s - 1) else 1) * ArtinL.Abelian.completedLSeries ψ s ∧
        Λ' s = (if ψ = 1 then s * (s - 1) else 1) * ArtinL.Abelian.completedLSeries ψ⁻¹ s) ∧
      (∀ s : ℂ, Λ (1 - s) = W * Λ' s) :=
  ArtinRecipAssembly.main ψ

end S_ArtinL_Abelian_exists_completedLSeries_functionalEquation_u0
end P2MW
export P2MW.S_ArtinL_Abelian_exists_completedLSeries_functionalEquation_u0 (solution)
