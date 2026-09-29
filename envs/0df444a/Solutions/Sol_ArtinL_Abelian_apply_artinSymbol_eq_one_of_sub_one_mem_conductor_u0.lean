-- Prove2me | solution 1 for ArtinL.Abelian.apply_artinSymbol_eq_one_of_sub_one_mem_conductor_u0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8f75a3e7-6cd2-5f6c-a3e0-c6a876447bf5

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0
import Theorems.Thm_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_conductor_u0
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top"
p2m_attr_erase "simp" "ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one"
p2m_attr_erase "simp" "groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin

open scoped IsMulCommutative

noncomputable section

namespace ArtinSigns

open NumberField.ComplexEmbedding

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def toC (τ : K →+* ℝ) : K →+* ℂ := (algebraMap ℝ ℂ).comp τ

@[scoped simp] theorem toC_apply (τ : K →+* ℝ) (x : K) : toC τ x = (τ x : ℂ) := rfl

theorem isReal_toC (τ : K →+* ℝ) : ComplexEmbedding.IsReal (toC τ) := by
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq, toC_apply, Complex.conj_ofReal]

theorem conjugate_toC (τ : K →+* ℝ) : conjugate (toC τ) = toC τ := (isReal_toC τ)

def realEquiv : (K →+* ℝ) ≃ {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} where
  toFun τ := ⟨toC τ, isReal_toC τ⟩
  invFun φ := φ.2.embedding
  left_inv τ := by
    ext x
    apply Complex.ofReal_injective
    rw [ComplexEmbedding.IsReal.coe_embedding_apply]
    rfl
  right_inv φ := by
    apply Subtype.ext
    ext x
    show (((φ.2.embedding x : ℝ)) : ℂ) = φ.1 x
    exact ComplexEmbedding.IsReal.coe_embedding_apply φ.2 x

def placeEquiv : (K →+* ℝ) ≃ {w : InfinitePlace K // w.IsReal} := realEquiv.trans InfinitePlace.mkReal

theorem placeEquiv_coe (τ : K →+* ℝ) : ((placeEquiv τ : {w : InfinitePlace K // w.IsReal}) : InfinitePlace K) =
    InfinitePlace.mk (toC τ) := by
  simp [placeEquiv, realEquiv, InfinitePlace.mkReal_coe]

theorem embedding_placeEquiv (τ : K →+* ℝ) :
    ((placeEquiv τ : {w : InfinitePlace K // w.IsReal}) : InfinitePlace K).embedding = toC τ := by
  rw [placeEquiv_coe]
  exact InfinitePlace.embedding_mk_eq_of_isReal (isReal_toC τ)

theorem embedding_of_isReal_placeEquiv (τ : K →+* ℝ) (x : K) :
    (embedding_of_isReal (placeEquiv τ).2 x : ℝ) = τ x := by
  have h := embedding_of_isReal_apply (placeEquiv τ).2 x
  rw [embedding_placeEquiv, toC_apply] at h
  exact_mod_cast h

section galois
variable [IsGalois K L]

theorem exists_above (τ : K →+* ℝ) : ∃ φ : L →+* ℂ, φ.comp (algebraMap K L) = toC τ := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) (InfinitePlace.mk (toC τ))
  have h := hw
  simp only at h
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.mk_eq_iff] at h
  rcases h with h | h
  · exact ⟨w.embedding, h⟩
  · refine ⟨conjugate w.embedding, ?_⟩
    rw [← h]; rfl

theorem exists_isConj (τ : K →+* ℝ) (φ : L →+* ℂ) (hφ : φ.comp (algebraMap K L) = toC τ) :
    ∃ σ : L ≃ₐ[K] L, ComplexEmbedding.IsConj φ σ := by
  obtain ⟨σ, hσ⟩ := exists_comp_symm_eq_of_comp_eq (conjugate φ) φ (by
    rw [show (conjugate φ).comp (algebraMap K L) = conjugate (φ.comp (algebraMap K L)) from rfl, hφ, conjugate_toC])
  refine ⟨σ, ?_⟩

  ext x
  have := congrArg (fun f : L →+* ℂ => f (σ x)) hσ
  simpa [ComplexEmbedding.IsConj, RingHom.comp_apply] using this

noncomputable def phiτ (τ : K →+* ℝ) : L →+* ℂ := (exists_above (L := L) τ).choose
theorem phiτ_spec (τ : K →+* ℝ) : (phiτ (L := L) τ).comp (algebraMap K L) = toC τ := (exists_above (L := L) τ).choose_spec
noncomputable def cτ (τ : K →+* ℝ) : L ≃ₐ[K] L := (exists_isConj τ (phiτ τ) (phiτ_spec τ)).choose
theorem isConj_cτ (τ : K →+* ℝ) : ComplexEmbedding.IsConj (phiτ (L := L) τ) (cτ τ) := (exists_isConj τ (phiτ τ) (phiτ_spec τ)).choose_spec

end galois

end ArtinSigns
p2m_reactivate "P2MW.S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_conductor_u0.ArtinSigns"

end
p2m_reactivate "P2MW.S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_conductor_u0.ArtinSigns"

namespace ArtinCond

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem inertia_mono {I J : Ideal (𝓞 L)} (h : I ≤ J) : I.inertia (L ≃ₐ[K] L) ≤ J.inertia (L ≃ₐ[K] L) :=
  fun _ hσ x => h (hσ x)

theorem conductorExponent_eq_zero [IsGalois K L] (ψ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : (LanglandsTunnell.P2.Artin.primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥) :
    ArtinL.Abelian.conductorExponent ψ v = 0 := by
  have h0 : ArtinL.Abelian.inertiaGroup K L v = ⊥ := h
  have hG : ∀ i : ℕ, ArtinL.Abelian.ramificationGroup K L v i = ⊥ := fun i => by
    rw [eq_bot_iff, ← h0, ArtinL.Abelian.ramificationGroup, ArtinL.Abelian.inertiaGroup]
    exact inertia_mono (Ideal.pow_le_self (Nat.succ_ne_zero i))
  have hunr : ArtinL.Abelian.IsUnramifiedAt ψ v := fun σ hσ => by
    rw [h0, Subgroup.mem_bot] at hσ
    rw [hσ, map_one]
  have hswan : ArtinL.Abelian.swanConductor ψ v = 0 := by
    unfold ArtinL.Abelian.swanConductor
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    rw [if_pos (fun σ hσ => by rw [hG, Subgroup.mem_bot] at hσ; rw [hσ, map_one]), mul_zero]
  rw [ArtinL.Abelian.conductorExponent, if_pos hunr, hswan, Nat.ceil_zero]

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def Adm (ψ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) : Prop :=
  ∀ (β : 𝓞 K) (hβ : β ≠ 0) (𝔪 : Ideal (𝓞 K)) (hc : principalUnit K β hβ ∈ coprimeToModulus K 𝔪),
    (∀ τ : K →+* ℝ, 0 < τ (β : K)) → β - 1 ∈ 𝔞 → ψ (artinSymbol K L 𝔪 ⟨principalUnit K β hβ, hc⟩) = 1

theorem Adm.anti {ψ : (L ≃ₐ[K] L) →* ℂˣ} {𝔞 𝔟 : Ideal (𝓞 K)} (h : Adm ψ 𝔞) (hle : 𝔟 ≤ 𝔞) : Adm ψ 𝔟 :=
  fun β hβ 𝔪 hc hpos h1 => h β hβ 𝔪 hc hpos (hle h1)

theorem Adm.step {ψ : (L ≃ₐ[K] L) →* ℂˣ}
    (v : HeightOneSpectrum (𝓞 K)) {𝔪' : Ideal (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪') {N : ℕ}
    (h : Adm ψ (v.asIdeal ^ N * 𝔪')) {n : ℕ} (hn : ArtinL.Abelian.conductorExponent ψ v ≤ n) :
    Adm ψ (v.asIdeal ^ n * 𝔪') :=
  fun β hβ 𝔪 hc hpos h1 =>
    ArtinL.Abelian.apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0 K L ψ v 𝔪' hv N
      (fun β' hβ' 𝔪'' hc' hp' h1' => h β' hβ' 𝔪'' hc' hp' h1') n hn 𝔪 β hβ hc hpos h1

theorem not_dvd_prod_pow (v : HeightOneSpectrum (𝓞 K)) (W : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ W)
    (e : HeightOneSpectrum (𝓞 K) → ℕ) : ¬ v.asIdeal ∣ ∏ u ∈ W, u.asIdeal ^ e u := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Ideal.one_eq_top, Ideal.dvd_iff_le, top_le_iff]
    exact v.isPrime.ne_top
  | insert u W hu ih =>
    rw [Finset.prod_insert hu]
    intro hdvd
    rcases v.prime.dvd_or_dvd hdvd with h | h
    · have huv : v.asIdeal ∣ u.asIdeal := v.prime.dvd_of_dvd_pow h
      rw [Ideal.dvd_iff_le] at huv
      have : u = v := HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top huv)
      exact hv (this ▸ Finset.mem_insert_self u W)
    · exact ih (fun h' => hv (Finset.mem_insert_of_mem h')) h

end ArtinCond
p2m_reactivate "P2MW.S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_conductor_u0.ArtinSigns"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔪 : Ideal (𝓞 K)) (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔪)
    (h1 : α - 1 ∈ ArtinL.Abelian.conductor ψ) (hpos : ∀ τ : K →+* ℝ, 0 < τ (α : K)) :
    ψ (artinSymbol K L 𝔪 ⟨principalUnit K α hα, hc⟩) = 1 := by
  classical

  obtain ⟨𝔣₀, h𝔣₀, hunr, hrec⟩ := NumberField.exists_artinSymbol_principalUnit_eq_prod_of_isConj K L
  have hAdm0 : ArtinCond.Adm (K := K) (L := L) ψ 𝔣₀ := by
    intro β hβ 𝔪' hc' hpos' hβ1
    rw [hrec β hβ 𝔪' hc' (fun τ => ArtinSigns.cτ (L := L) τ) hβ1
      (fun τ => ⟨ArtinSigns.phiτ (L := L) τ, fun x => by
        simpa using congrArg (fun f : K →+* ℂ => f x) (ArtinSigns.phiτ_spec (L := L) τ), ArtinSigns.isConj_cτ τ⟩)]
    rw [Finset.filter_false_of_mem (fun τ _ => not_lt.2 (hpos' τ).le), Finset.prod_empty, map_one]

  set S₀ : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors h𝔣₀).toFinset with hS₀
  have hmemS₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S₀ ↔ v.asIdeal ∣ 𝔣₀ := fun v => by
    rw [hS₀, Set.Finite.mem_toFinset]; rfl
  have hexp0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ → ArtinL.Abelian.conductorExponent ψ v = 0 := fun v hv =>
    ArtinCond.conductorExponent_eq_zero ψ v (hunr v ((hmemS₀ v).not.1 hv) _
      (LanglandsTunnell.P2.Artin.primeAbove_isMaximal K L v).isPrime (LanglandsTunnell.P2.Artin.under_primeAbove K L v))
  set fv : HeightOneSpectrum (𝓞 K) → ℕ := fun v => ArtinL.Abelian.conductorExponent ψ v with hfv
  have hcond : ArtinL.Abelian.conductor ψ = ∏ v ∈ S₀, v.asIdeal ^ fv v := by
    unfold ArtinL.Abelian.conductor
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Function.mem_mulSupport] at hv
    by_contra hvS
    exact hv (by rw [hexp0 v (by simpa using hvS), pow_zero])

  set Nv : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (Associates.mk v.asIdeal).count (Associates.mk 𝔣₀).factors with hNv
  have hfact : 𝔣₀ = ∏ v ∈ S₀, v.asIdeal ^ Nv v := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization h𝔣₀]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Finset.mem_coe, hmemS₀]
    by_contra hvd
    apply hv
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
    have : (Associates.mk v.asIdeal).count (Associates.mk 𝔣₀).factors = 0 := by
      by_contra hne
      exact hvd ((Associates.count_ne_zero_iff_dvd h𝔣₀ v.irreducible).1 hne)
    rw [this, pow_zero]

  have key : ∀ U : Finset (HeightOneSpectrum (𝓞 K)), U ⊆ S₀ →
      ArtinCond.Adm (K := K) (L := L) ψ ((∏ v ∈ U, v.asIdeal ^ fv v) * ∏ v ∈ S₀ \ U, v.asIdeal ^ Nv v) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.prod_empty, one_mul, Finset.sdiff_empty, ← hfact]
      exact hAdm0
    | insert v U hvU ih =>
      intro hsub
      have hvS : v ∈ S₀ := hsub (Finset.mem_insert_self v U)
      have hU : U ⊆ S₀ := fun u hu => hsub (Finset.mem_insert_of_mem hu)
      have hih := ih hU

      have hvmem : v ∈ S₀ \ U := Finset.mem_sdiff.2 ⟨hvS, hvU⟩
      have herase : (S₀ \ U).erase v = S₀ \ insert v U := by
        ext u
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, not_or]
        tauto
      set 𝔪' : Ideal (𝓞 K) := (∏ u ∈ U, u.asIdeal ^ fv u) * ∏ u ∈ S₀ \ insert v U, u.asIdeal ^ Nv u with h𝔪'
      have hold : (∏ u ∈ U, u.asIdeal ^ fv u) * ∏ u ∈ S₀ \ U, u.asIdeal ^ Nv u = v.asIdeal ^ Nv v * 𝔪' := by
        rw [← Finset.mul_prod_erase _ _ hvmem, herase, h𝔪']
        ring
      have hnew : (∏ u ∈ insert v U, u.asIdeal ^ fv u) * ∏ u ∈ S₀ \ insert v U, u.asIdeal ^ Nv u =
          v.asIdeal ^ fv v * 𝔪' := by
        rw [Finset.prod_insert hvU, h𝔪']
        ring
      have hv𝔪' : ¬ v.asIdeal ∣ 𝔪' := by
        rw [h𝔪']
        intro hdvd
        rcases v.prime.dvd_or_dvd hdvd with h | h
        · exact ArtinCond.not_dvd_prod_pow v U hvU fv h
        · exact ArtinCond.not_dvd_prod_pow v (S₀ \ insert v U) (by simp) Nv h
      rw [hnew]
      rw [hold] at hih
      exact ArtinCond.Adm.step v hv𝔪' hih le_rfl

  have hfin := key S₀ subset_rfl
  rw [Finset.sdiff_self, Finset.prod_empty, mul_one, ← hcond] at hfin
  exact hfin α hα 𝔪 hc hpos h1

end S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_conductor_u0
end P2MW
export P2MW.S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_conductor_u0 (solution)
