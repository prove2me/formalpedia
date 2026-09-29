-- Prove2me | solution 1 for AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/725b0872-5b63-5407-a540-c1ceee992b13

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_exists_finset_forall_slope_eq_sum_twistedClassIntegral_and_intercept_eq_sum_weightedTwistedClassIntegral_haarQuotient_of_eq_affine
import Theorems.Thm_AutomorphicForm_exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
import Theorems.Thm_M4aHerbrand_GenuineDescent_exists_ideleChar_comp_idelicNorm_eq_of_unitsAct_invariant
import Theorems.Thm_AutomorphicForm_exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport
import Theorems.Thm_NumberField_exists_pos_forall_lintegral_comp_idelicNorm_haarQuotient_ker_eq_mul_setLIntegral_range
import Theorems.Thm_AutomorphicForm_forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_isSectionFnOn_adeleRing_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
import Theorems.Thm_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
import Theorems.Thm_AutomorphicForm_exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_AutomorphicForm_continuous_injective_norm_pow_principal_range_eq_fixed_unitsMap_genuineBaseChange
import Theorems.Thm_AutomorphicForm_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
import Theorems.Thm_AutomorphicForm_exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
import Theorems.Thm_AutomorphicForm_exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Theorems.Thm_AutomorphicForm_exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses
import Theorems.Thm_AutomorphicForm_areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_prime
import Theorems.Thm_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm
import Theorems.Thm_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
import Theorems.Thm_AutomorphicForm_exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints
import Theorems.Thm_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
import Theorems.Thm_AutomorphicForm_centralEllipticConstant_eq_of_factorization_of_normFibre_of_exists_ne_zero
import Theorems.Thm_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff
import Theorems.Thm_AutomorphicForm_exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
import Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
import Theorems.Thm_AutomorphicForm_twistedWeightedClassIntegral_eq_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_of_coupled_of_isSemiLocalFactorization
import Theorems.Thm_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add
import Theorems.Thm_AutomorphicForm_exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_torusShell_const_eq_of_forall_lintegral_eq
import Theorems.Thm_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
import Theorems.Thm_AutomorphicForm_baseChangeGL_toTensorGL_self
import Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing
import Theorems.Thm_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal
import Theorems.Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
import Theorems.Thm_NumberField_isOpen_range_idelicNorm
import Theorems.Thm_AutomorphicForm_measurable_window_values_of_ne_one_of_prime
import Theorems.Thm_AutomorphicForm_isSemiLocalTestFn_sum_indicator_semiLocalIntegralSet_word
import Theorems.Thm_AutomorphicForm_areMatchingLocal_heckeWord_sum_coeff_univWord_mul_heckeWord_of_ramificationIdx_eq_one_of_prime
import Theorems.Thm_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
import Theorems.Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified
import Theorems.Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified
import Theorems.Thm_AutomorphicForm_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_eq_zero_of_mem_sup_of_not_mem_range_of_prime
import Theorems.Thm_AutomorphicForm_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_eq_zero_of_ratio_not_mem_range_norm_of_prime
import Theorems.Thm_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps
import Theorems.Thm_AutomorphicForm_isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_finset_forall_window_product_eq_zero_of_not_mem
import Theorems.Thm_AutomorphicForm_exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv
import Theorems.Thm_AutomorphicForm_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.preimage_mulLeft_smul"
p2m_attr_erase "simp" "AutomorphicForm.cpowChar_apply_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace H5ASMw47
theorem affine_combine {ι κ : Type*} (s : Finset ι) (t : Finset κ) (R AL BL c₀ : ℂ) (coeff : κ → ℂ)
    (AK BK : ι → κ → ℂ) :
    (R * AL + BL) - c₀ * ∑ i ∈ s, ∑ j ∈ t, coeff j * (R * AK i j + BK i j) =
      R * (AL - c₀ * ∑ i ∈ s, ∑ j ∈ t, coeff j * AK i j) + (BL - c₀ * ∑ i ∈ s, ∑ j ∈ t, coeff j * BK i j) := by
  have e1 : ∑ i ∈ s, ∑ j ∈ t, coeff j * (R * AK i j + BK i j) =
      R * (∑ i ∈ s, ∑ j ∈ t, coeff j * AK i j) + ∑ i ∈ s, ∑ j ∈ t, coeff j * BK i j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1]
  ring

theorem affine_unique {A B A' B' : ℂ} {R₀ : ℝ}
    (h : ∀ R : ℝ, R₀ ≤ R → (R : ℂ) * A + B = (R : ℂ) * A' + B') : A = A' ∧ B = B' := by
  have h0 := h R₀ le_rfl
  have h1 := h (R₀ + 1) (by linarith)
  have hA : A = A' := by
    have : ((R₀ + 1 : ℝ) : ℂ) * A + B - ((R₀ : ℂ) * A + B) = ((R₀ + 1 : ℝ) : ℂ) * A' + B' - ((R₀ : ℂ) * A' + B') := by
      rw [h1, h0]
    push_cast at this
    linear_combination this
  refine ⟨hA, ?_⟩
  rw [hA] at h0
  linear_combination h0

section Delta

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

include hgen in

theorem exists_Delta : ∃ Δ : Set (GL (Fin 2) L),
    (∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) ∧
    (∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
    ({δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) := by
  classical
  obtain ⟨-, h2, h3⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal (K := K) (L := L) hgen

  let cls : GL (Fin 2) L → Set (GL (Fin 2) L) := fun t => {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
    t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
  let good : GL (Fin 2) L → Prop := fun t =>
    ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1

  let S : Set (Set (GL (Fin 2) L)) := {s | ∃ t, good t ∧ cls t = s}
  have hS : ∀ s : S, ∃ t, good t ∧ cls t = s := fun s => s.2
  choose pick hpick using hS
  refine ⟨Set.range pick, ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(hpick s).1.1.1, (hpick s).1.1.2, (hpick s).1.2⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ hne
    have hss : (s : Set (GL (Fin 2) L)) ≠ s' := fun h => hne (by rw [Subtype.ext h])
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne'
    have h := ((h3 (pick s') (pick s) (hpick s').1.1 (hpick s).1.1).1).mp hne'
    exact hss (by rw [← (hpick s).2, ← (hpick s').2]; exact h)
  · intro δ hδ
    obtain ⟨t, htd, htN, ht⟩ := h2 δ hδ
    have hs : cls t ∈ S := ⟨t, ⟨htd, htN⟩, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨pick ⟨_, hs⟩, ⟨⟨_, hs⟩, rfl⟩, ?_⟩
    have hct : cls (pick ⟨cls t, hs⟩) = cls t := (hpick ⟨_, hs⟩).2
    show δ ∈ cls (pick ⟨cls t, hs⟩)
    rw [hct]
    exact ht

end Delta

section Lambda0

theorem exists_Lambda0 (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ∃ Λ₀ : Subgroup (GL (Fin 2) L), ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔
      (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L) := by
  classical

  have hnz : ∀ γ : GL (Fin 2) L, (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 →
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
    intro γ h10
    have hdet : (γ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := γ.isUnit.map Matrix.detMonoidHom |>.ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩
  let S : Set (GL (Fin 2) L) := setOf fun γ : GL (Fin 2) L =>
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)
  refine ⟨{ carrier := S, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun γ => Iff.rfl⟩
  · rintro a b ⟨ha10, ha01, ka, hka⟩ ⟨hb10, hb01, kb, hkb⟩
    obtain ⟨ha00, ha11⟩ := hnz a ha10
    obtain ⟨hb00, hb11⟩ := hnz b hb10
    refine ⟨?_, ?_, ka * kb, ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_two, ha10, hb10]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, ha01, hb01]
    · have h00 : ((a * b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
          (a : Matrix (Fin 2) (Fin 2) L) 0 0 * (b : Matrix (Fin 2) (Fin 2) L) 0 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two, ha01, hb10]
      have h11 : ((a * b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
          (a : Matrix (Fin 2) (Fin 2) L) 1 1 * (b : Matrix (Fin 2) (Fin 2) L) 1 1 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two, ha10, hb01]
      rw [h00, h11, map_mul, hka, hkb]
      field_simp
  · refine ⟨by simp, by simp, 1, by simp⟩
  · rintro a ⟨ha10, ha01, ka, hka⟩
    obtain ⟨ha00, ha11⟩ := hnz a ha10
    have hdet : (a : Matrix (Fin 2) (Fin 2) L).det = (a : Matrix (Fin 2) (Fin 2) L) 0 0 * (a : Matrix (Fin 2) (Fin 2) L) 1 1 := by
      rw [Matrix.det_fin_two, ha10, mul_zero, sub_zero]
    have hinv : ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = (a : Matrix (Fin 2) (Fin 2) L)⁻¹ := by
      rw [Matrix.coe_units_inv]
    have hka0 : algebraMap K L ka ≠ 0 := by rw [hka]; exact div_ne_zero ha00 ha11
    have hka0' : ka ≠ 0 := fun h => hka0 (by rw [h, map_zero])
    refine ⟨?_, ?_, ka⁻¹, ?_⟩
    · rw [hinv, Matrix.inv_def, Matrix.adjugate_fin_two]; simp [ha10]
    · rw [hinv, Matrix.inv_def, Matrix.adjugate_fin_two]; simp [ha01]
    · rw [hinv, Matrix.inv_def, Matrix.adjugate_fin_two]
      simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', smul_eq_mul, Ring.inverse_eq_inv']
      rw [map_inv₀, hka]
      have hd : (a : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by rw [hdet]; exact mul_ne_zero ha00 ha11
      field_simp
end Lambda0

end H5ASMw47

namespace H5ASMw47

theorem isRegularSemisimple_map_of_diagonal {K A : Type*} [Field K] [CommRing A] (f : K →+* A)
    (γ : GL (Fin 2) K) (h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hne : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map f γ) := by
  unfold AutomorphicForm.IsRegularSemisimple
  have hdet : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := γ.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have h11 : (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    exact right_ne_zero_of_mul hdet
  have hdiff : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 - (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero] at h
    rw [h, div_self h11]
  have key : ((Matrix.GeneralLinearGroup.map f γ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).trace ^ 2 -
      4 * ((Matrix.GeneralLinearGroup.map f γ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).det =
      f (((γ : Matrix (Fin 2) (Fin 2) K) 0 0 - (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2) := by
    simp only [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two, Matrix.diag_apply, Matrix.GeneralLinearGroup.map_apply,
      h10, h01, map_zero, mul_zero, sub_zero, map_pow, map_sub]
    ring
  rw [key]
  exact (IsUnit.pow 2 (isUnit_iff_ne_zero.mpr hdiff)).map f
end H5ASMw47

namespace H5ASMw47
theorem isHaarMeasure_archHaarK' (K : Type) [Field K] [NumberField K] :
    @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) (AutomorphicForm.archHaarK K) := by
  letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (InfiniteAdeleRing K)
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  unfold AutomorphicForm.archHaarK
  infer_instance

open scoped TensorProduct.RightActions in
theorem isHaarMeasure_archHaarL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.archHaarL K L) := by
  letI := AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  unfold AutomorphicForm.archHaarL
  infer_instance
end H5ASMw47

namespace H5ASMw47
open scoped Pointwise in

theorem absNorm_pointwise_smul_algEquiv (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (I : Ideal (𝓞 L)) : Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  classical
  have h : σ • I = I.map (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ) := rfl
  rw [h, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine Nat.card_congr ?_
  refine (Ideal.quotientEquiv I _ (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ) rfl).symm.toEquiv
end H5ASMw47

namespace H5ASMw47

noncomputable def windingDatumZero_w47 (r d c : ℕ) (hd : d ≠ 0) : AutomorphicForm.WindingDatum r d c where
  Λ := ⊥
  hΛ := Subsingleton.discreteTopology
  s := 0
  ω := fun _ => 1
  hω := by
    intro h
    obtain ⟨i⟩ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
    exact one_ne_zero (congr_fun h i)
  hpf := by
    intro x hx
    rw [AddSubgroup.mem_bot] at hx
    subst hx
    simp
  χ := 0
  sub := fun _ => ⊥
  hsub := fun _ => le_rfl
  Ψ := fun _ _ => 0
  hΨc := fun _ => continuous_const
  hΨi := fun _ => integrable_zero _ _ _
  C := fun _ => 0
  hΨd := fun _ _ => by simp
  hΨhatd := fun _ _ => by simp
  m := fun _ _ => 0
  θ₀ := fun _ _ => 0
  x₀ := fun _ _ => 0
  n₀ := fun _ _ => 0
  lam := fun _ => 0
  hsum := by simpa using summable_zero

theorem coeff_windingDatumZero_w47 (r d c : ℕ) (hd : d ≠ 0) (n : Fin d → ℤ) :
    (windingDatumZero_w47 r d c hd).coeff n = 0 := by
  unfold AutomorphicForm.WindingDatum.coeff
  simp [windingDatumZero_w47]

theorem map_satakePow_w47 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    ∀ (n : ℕ) (s e : R), φ (AutomorphicForm.satakePow n s e) = AutomorphicForm.satakePow n (φ s) (φ e)
  | 0, s, e => by rw [AutomorphicForm.satakePow_zero, AutomorphicForm.satakePow_zero]; exact map_ofNat φ 2
  | 1, s, e => by simp [AutomorphicForm.satakePow]
  | n + 2, s, e => by
    rw [AutomorphicForm.satakePow_add_two, AutomorphicForm.satakePow_add_two, map_sub, map_mul, map_mul,
      map_satakePow_w47 φ (n + 1), map_satakePow_w47 φ n]

theorem satakePow_two_one_w47 : ∀ n : ℕ, AutomorphicForm.satakePow n (2 : ℂ) 1 = 2
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [AutomorphicForm.satakePow_add_two, satakePow_two_one_w47 (n + 1), satakePow_two_one_w47 n]
    norm_num

theorem univWord_ne_zero_w47 (n k j : ℕ) : AutomorphicForm.SatakeCombination.univWord n k j ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (![2, 1] : Fin 2 → ℂ)) h
  rw [AutomorphicForm.SatakeCombination.univWord, map_mul, map_pow, map_pow, map_pow, map_satakePow_w47,
    MvPolynomial.eval_X, MvPolynomial.eval_X, map_zero] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, satakePow_two_one_w47, one_pow, mul_one] at h2
  exact absurd h2 (pow_ne_zero _ two_ne_zero)

theorem slotIndex_nonempty_w47 (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)) (k j : HeightOneSpectrum (𝓞 K) → ℕ)
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (AutomorphicForm.SatakeCombination.slotIndex K L ws k j T).Nonempty :=
  Finset.pi_nonempty.mpr fun v _ => MvPolynomial.support_nonempty.mpr (univWord_ne_zero_w47 _ _ _)
end H5ASMw47

namespace H5ASMw47

theorem norm_div_w47 (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (x y : L) :
    Algebra.norm K (x / y) = Algebra.norm K x / Algebra.norm K y := by
  by_cases hy : y = 0
  · subst hy
    simp [Algebra.norm_zero]
  · have hny : Algebra.norm K y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
    rw [eq_div_iff hny, ← map_mul, div_mul_cancel₀ _ hy]

theorem centralScalar_apply_w47 (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((AutomorphicForm.centralScalar (𝓞 K) K z : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = if i = j then (z : AdeleRing (𝓞 K) K) else 0 := by
  simp only [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem centralScalar_mul_apply_w47 (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : AutomorphicForm.AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    ((AutomorphicForm.centralScalar (𝓞 K) K z * h : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = (z : AdeleRing (𝓞 K) K) * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, centralScalar_apply_w47, centralScalar_apply_w47]
  fin_cases i <;> simp

theorem mul_centralScalar_apply_w47 (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : AutomorphicForm.AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    ((h * AutomorphicForm.centralScalar (𝓞 K) K z : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = (z : AdeleRing (𝓞 K) K) * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, centralScalar_apply_w47, centralScalar_apply_w47]
  fin_cases j <;> simp [mul_comm]

theorem centralScalar_comm_w47 (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.centralScalar (𝓞 K) K z * h = h * AutomorphicForm.centralScalar (𝓞 K) K z := by
  refine Units.ext ?_
  ext i j
  rw [centralScalar_mul_apply_w47, mul_centralScalar_apply_w47]

theorem isRegularSemisimple_centralScalar_mul_w47 (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.centralScalar (𝓞 K) K z * g) := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  have key : ((AutomorphicForm.centralScalar (𝓞 K) K z * g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).trace ^ 2 -
      4 * ((AutomorphicForm.centralScalar (𝓞 K) K z * g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det =
      (z : AdeleRing (𝓞 K) K) ^ 2 * ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).trace ^ 2 -
        4 * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) := by
    simp only [Matrix.trace_fin_two, Matrix.det_fin_two, centralScalar_mul_apply_w47]
    ring
  rw [key]
  exact ((Units.isUnit z).pow 2).mul hg

theorem centralizer_centralScalar_mul_w47 (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ)
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) =
      Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K z * γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) := by
  have hcomm : ∀ h : AutomorphicForm.AdelicGL2 (𝓞 K) K, AutomorphicForm.centralScalar (𝓞 K) K z * h =
      h * AutomorphicForm.centralScalar (𝓞 K) K z := centralScalar_comm_w47 K z
  ext h
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hh
    calc AutomorphicForm.centralScalar (𝓞 K) K z * γ * h = AutomorphicForm.centralScalar (𝓞 K) K z * (γ * h) := mul_assoc _ _ _
      _ = AutomorphicForm.centralScalar (𝓞 K) K z * (h * γ) := by rw [hh]
      _ = (AutomorphicForm.centralScalar (𝓞 K) K z * h) * γ := (mul_assoc _ _ _).symm
      _ = (h * AutomorphicForm.centralScalar (𝓞 K) K z) * γ := by rw [hcomm h]
      _ = h * (AutomorphicForm.centralScalar (𝓞 K) K z * γ) := mul_assoc _ _ _
  · intro hh
    have h1 : AutomorphicForm.centralScalar (𝓞 K) K z * (γ * h) = AutomorphicForm.centralScalar (𝓞 K) K z * (h * γ) := by
      calc AutomorphicForm.centralScalar (𝓞 K) K z * (γ * h) = AutomorphicForm.centralScalar (𝓞 K) K z * γ * h := (mul_assoc _ _ _).symm
        _ = h * (AutomorphicForm.centralScalar (𝓞 K) K z * γ) := hh
        _ = (h * AutomorphicForm.centralScalar (𝓞 K) K z) * γ := (mul_assoc _ _ _).symm
        _ = (AutomorphicForm.centralScalar (𝓞 K) K z * h) * γ := by rw [hcomm h]
        _ = AutomorphicForm.centralScalar (𝓞 K) K z * (h * γ) := mul_assoc _ _ _
    exact mul_left_cancel h1

theorem conj_centralScalar_mul_w47 (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ)
    (γ x : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z * γ) * x = AutomorphicForm.centralScalar (𝓞 K) K z * (x⁻¹ * γ * x) := by
  have hcomm := centralScalar_comm_w47 K z x⁻¹
  calc x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z * γ) * x = (x⁻¹ * AutomorphicForm.centralScalar (𝓞 K) K z) * γ * x := by
        rw [← mul_assoc]
    _ = (AutomorphicForm.centralScalar (𝓞 K) K z * x⁻¹) * γ * x := by rw [hcomm]
    _ = AutomorphicForm.centralScalar (𝓞 K) K z * (x⁻¹ * γ * x) := by
        rw [mul_assoc (AutomorphicForm.centralScalar (𝓞 K) K z), mul_assoc (AutomorphicForm.centralScalar (𝓞 K) K z), mul_assoc x⁻¹]

theorem exists_haar_congr_w47 {G : Type*} [Group G] [TopologicalSpace G]
    {H₁ H₂ : Subgroup G} (hH : H₁ = H₂) (τ : @Measure H₁ (borel H₁))
    (hτ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) τ) :
    ∃ τ' : @Measure H₂ (borel H₂), @Measure.IsHaarMeasure H₂ _ _ (borel H₂) τ' ∧
      ∀ w : G → ℝ, ∫ t, w (t : G) ∂τ' = ∫ t, w (t : G) ∂τ := by
  subst hH
  exact ⟨τ, hτ, fun _ => rfl⟩

theorem exists_isOrbitalIntegralOn_centralScalar_mul_w47 (K : Type) [Field K] [NumberField K]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) [τ.IsHaarMeasure]
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (I : ℂ)
    (h : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ
      (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) I) :
    ∃ τ' : Measure (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K z * γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      τ'.IsHaarMeasure ∧
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ (AutomorphicForm.centralScalar (𝓞 K) K z * γ) τ' f I := by
  obtain ⟨τ', hτ', hint⟩ := exists_haar_congr_w47 (centralizer_centralScalar_mul_w47 K z γ) τ inferInstance
  refine ⟨τ', hτ', ?_⟩
  obtain ⟨w, ⟨hw0, hwm, hwc, hw1⟩, hI⟩ := h
  refine ⟨w, ⟨hw0, hwm, hwc, ?_⟩, ?_⟩
  · intro x hx
    rw [conj_centralScalar_mul_w47] at hx
    rw [hint (fun g => w (g * x))]
    exact hw1 x hx
  · rw [hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f (AutomorphicForm.centralScalar (𝓞 K) K z * (x⁻¹ * γ * x)) * (w x : ℂ) =
      f (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z * γ) * x) * (w x : ℂ)
    rw [conj_centralScalar_mul_w47]

theorem isOrbitalIntegralOn_smul_w47 (K : Type) [Field K] [NumberField K]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 K) K)) (c : NNReal)
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (I : ℂ)
    (h : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ f I) :
    AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c • μ) γ τ f ((c : ℂ) * I) := by
  obtain ⟨w, hw, hI⟩ := h
  refine ⟨w, hw, ?_⟩
  rw [integral_smul_nnreal_measure, hI, NNReal.smul_def, Complex.real_smul]

end H5ASMw47

namespace H5ASMw47
open LanglandsTunnell.CubicInduction (diagUnits2) in
theorem eq_diagUnits2_of_entries_w47 {K : Type} [Field K] (g : GL (Fin 2) K) (a b : Kˣ)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = a) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = b) :
    g = diagUnits2 a b := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [diagUnits2] using h00
  · simpa [diagUnits2] using h01
  · simpa [diagUnits2] using h10
  · simpa [diagUnits2] using h11

theorem GL2_eq_of_entries_w47 {K : Type} [Field K] (g g' : GL (Fin 2) K)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = (g' : Matrix (Fin 2) (Fin 2) K) 0 0)
    (h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = (g' : Matrix (Fin 2) (Fin 2) K) 0 1)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = (g' : Matrix (Fin 2) (Fin 2) K) 1 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = (g' : Matrix (Fin 2) (Fin 2) K) 1 1) : g = g' := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem det_diag_ne_w47 {L : Type} [Field L] (t : GL (Fin 2) L) (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (t : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := t.isUnit.map Matrix.detMonoidHom |>.ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩
end H5ASMw47

namespace H5ASMw47
open LanglandsTunnell.CubicInduction (diagUnits2) in

theorem exists_DeltaKfin_w47 {M : Type*} (K : Type) [Field K] [NumberField K]
    (slot : Finset M) (fam : M → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hfamc : ∀ m ∈ slot, Continuous (fam m) ∧ HasCompactSupport (fam m)) :
    ∃ ΔKfin : Finset (GL (Fin 2) K),
      (∀ γ ∈ ΔKfin, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1) ∧
      (∀ γ ∈ ΔKfin, ∀ γ' ∈ ΔKfin,
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
          (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ') ∧
      (∀ m ∈ slot, ∀ u : Kˣ, (u : K) ≠ 1 →
        (∀ γ ∈ ΔKfin, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K)) →
          ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
            fam m (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
              diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0) ∧
      (∀ γ ∈ ΔKfin, ∃ u : Kˣ, (u : K) ≠ 1 ∧ γ = diagUnits2 u 1 ∧ diagUnits2 u⁻¹ 1 ∈ ΔKfin) := by
  classical
  have hU : ∀ m, ∃ U : Finset Kˣ, m ∈ slot → ∀ u : Kˣ, (u : K) ≠ 1 → u ∉ U →
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        fam m (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0 := by
    intro m
    by_cases hm : m ∈ slot
    · obtain ⟨U, hU⟩ := AutomorphicForm.exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport
        K (fam m) (hfamc m hm).1 (hfamc m hm).2
      exact ⟨U, fun _ => hU⟩
    · exact ⟨∅, fun h => absurd h hm⟩
  choose Um hUm using hU
  let U : Finset Kˣ := (slot.biUnion Um).filter (fun u => (u : K) ≠ 1)
  let U' : Finset Kˣ := U ∪ U.image (fun u => u⁻¹)
  have hU'ne : ∀ u ∈ U', (u : K) ≠ 1 := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact (Finset.mem_filter.mp h).2
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      have hw1 : (w : K) ≠ 1 := (Finset.mem_filter.mp hw).2
      intro h1
      apply hw1
      rw [Units.val_eq_one] at h1 ⊢
      exact inv_eq_one.mp h1
  have hU'inv : ∀ u ∈ U', u⁻¹ ∈ U' := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨u, h, rfl⟩))
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      rw [inv_inv]
      exact Finset.mem_union.mpr (Or.inl hw)
  have hrat : ∀ u : Kˣ, ((diagUnits2 u 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 /
      ((diagUnits2 u 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K) := by
    intro u
    simp [diagUnits2]
  refine ⟨U'.image (fun u => diagUnits2 u 1), ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hγ
    refine ⟨by simp [diagUnits2], by simp [diagUnits2], ?_⟩
    rw [hrat]
    exact hU'ne u hu
  · intro γ hγ γ' hγ' h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hγ'
    rw [hrat, hrat] at h
    rw [Units.ext h]
  · intro m hm u hu1 hmiss z x
    apply hUm m hm u hu1
    intro huU
    have hu' : u ∈ U' :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨m, hm, huU⟩, hu1⟩))
    exact hmiss (diagUnits2 u 1) (Finset.mem_image.mpr ⟨u, hu', rfl⟩) (hrat u)
  · intro γ hγ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hγ
    exact ⟨u, hU'ne u hu, rfl, Finset.mem_image.mpr ⟨u⁻¹, hU'inv u hu, rfl⟩⟩
end H5ASMw47

namespace H5ASMw47

theorem isRegularSemisimple_scalar_mul_diagUnits2_w47 {A : Type} [CommRing A] (z a b : Aˣ)
    (h : IsUnit ((a : A) - (b : A))) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 a b) := by
  unfold AutomorphicForm.IsRegularSemisimple
  have key : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).trace ^ 2 -
      4 * ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).det =
      ((z : A) * ((a : A) - (b : A))) ^ 2 := by
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, diagUnits2, Matrix.GeneralLinearGroup.scalar, Units.val_mul,
      Matrix.mul_apply, Matrix.diagonal]
    ring
  rw [key]
  exact ((Units.isUnit z).mul h).pow 2

theorem isUnit_adeleArch_algebraMap_sub_one_w47 (K : Type) [Field K] [NumberField K] (u : Kˣ) (hu : (u : K) ≠ 1) :
    IsUnit (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) - 1) := by
  refine (Pi.isUnit_iff (x := fun v : InfinitePlace K =>
    (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) - 1) v)).mpr (fun v => ?_)
  change IsUnit ((algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 v - 1)
  rw [NumberField.AdeleRing.algebraMap_fst_apply]
  refine isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ?_)
  intro h1
  apply hu
  apply (algebraMap K v.Completion).injective
  rw [map_one]
  exact h1

theorem isRegularSemisimple_glArch_centralScalar_mul_diagUnits2_w47 (K : Type) [Field K] [NumberField K]
    (z : (AdeleRing (𝓞 K) K)ˣ) (u : Kˣ) (hu : (u : K) ≠ 1) :
    AutomorphicForm.IsRegularSemisimple (AdelicLevel.glArch (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) := by
  rw [AutomorphicForm.glArch_centralScalar_mul_diagUnits2]
  refine isRegularSemisimple_scalar_mul_diagUnits2_w47 _ _ _ ?_
  simpa [Units.coe_map, MonoidHom.coe_coe] using isUnit_adeleArch_algebraMap_sub_one_w47 K u hu

end H5ASMw47

namespace H5ASMw47
theorem isRegularSemisimple_map_ringHom_w47 {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 2) A)
    (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  have key : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).trace ^ 2 -
      4 * ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).det =
      f ((g : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (g : Matrix (Fin 2) (Fin 2) A).det) := by
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_pow, map_ofNat]
  rw [key]
  exact hg.map f
theorem isRegularSemisimple_toTensorGL_w47 (K L : Type) [Field K] [Field L] [Algebra K L]
    (A : Type) [CommRing A] [Algebra K A] (g : GL (Fin 2) A) (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.toTensorGL K L A g) :=
  isRegularSemisimple_map_ringHom_w47 _ g hg
end H5ASMw47

namespace H5ASMw47

theorem isLocalTestFn_const_mul_w47 (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (c : ℂ) (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f) :
    AutomorphicForm.IsLocalTestFn K v (fun x => c * f x) :=
  ⟨(IsLocallyConstant.const c).mul hf.1, hf.2.mul_left⟩

theorem isLocalTestFn_finset_sum_w47 (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ι : Type} (s : Finset ι) (g : ι → GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hg : ∀ i ∈ s, AutomorphicForm.IsLocalTestFn K v (g i)) :
    AutomorphicForm.IsLocalTestFn K v (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact AutomorphicForm.isLocalTestFn_zero K v
  | insert a s ha ih =>
    have hga := hg a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have : (fun x => ∑ i ∈ insert a s, g i x) = (fun x => g a x + ∑ i ∈ s, g i x) := by
      funext x; rw [Finset.sum_insert ha]
    rw [this]
    exact ⟨hga.1.add ih'.1, hga.2.add ih'.2⟩

end H5ASMw47

namespace H5ASMw47

theorem isFinTestFactor_finset_sum_w47 (K : Type) [Field K] [NumberField K]
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (g : ι → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hg : ∀ i ∈ s, AutomorphicForm.IsFinTestFactor K (g i)) :
    AutomorphicForm.IsFinTestFactor K (fun x => ∑ i ∈ s, c i * g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  | insert a s ha ih =>
    have hga := hg a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have : (fun x => ∑ i ∈ insert a s, c i * g i x) = (fun x => c a * g a x + ∑ i ∈ s, c i * g i x) := by
      funext x; rw [Finset.sum_insert ha]
    rw [this]
    exact ⟨((IsLocallyConstant.const (c a)).mul hga.1).add ih'.1, (hga.2.mul_left).add ih'.2⟩

end H5ASMw47

namespace H5ASMw47

open scoped Classical in
theorem fold_inv_w47 (K : Type) [Field K] (A : Finset Kˣ) (G : Kˣ → ℂ)
    (hA1 : ∀ u ∈ A, (u : K) ≠ 1) (hsep : ∀ u ∈ A, u⁻¹ ∈ A → u⁻¹ = u) (hG : ∀ u ∈ A, G u⁻¹ = G u) :
    ∑ u ∈ A ∪ A.image (fun u => u⁻¹), G u = ∑ u ∈ A, 2 * (if (u : K) = -1 then (1 / 2 : ℂ) else 1) * G u := by
  classical
  have hdisj : Disjoint A ((A.image (fun u => u⁻¹)) \ A) := Finset.disjoint_sdiff
  have hunion : A ∪ A.image (fun u => u⁻¹) = A ∪ ((A.image (fun u => u⁻¹)) \ A) := by
    rw [Finset.union_sdiff_self_eq_union]
  rw [hunion, Finset.sum_union hdisj]

  have hnew : (A.image (fun u => u⁻¹)) \ A = (A.filter (fun u => u⁻¹ ∉ A)).image (fun u => u⁻¹) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hx⟩; exact ⟨u, ⟨hu, hx⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hx⟩, rfl⟩; exact ⟨⟨u, hu, rfl⟩, hx⟩
  rw [hnew, Finset.sum_image (fun u _ u' _ h => inv_injective h)]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hself : u⁻¹ ∈ A ↔ (u : K) = -1 := by
    constructor
    · intro h
      have he : u⁻¹ = u := hsep u hu h
      have hsq : (u : K) * (u : K) = 1 := by
        have : ((u * u : Kˣ) : K) = ((u * u⁻¹ : Kˣ) : K) := by rw [he]
        simpa using this
      have hne := hA1 u hu
      have : ((u : K) - 1) * ((u : K) + 1) = 0 := by ring_nf; linear_combination hsq
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hne
      · linear_combination h1
    · intro h
      have he : u⁻¹ = u := by
        apply Units.ext
        rw [Units.val_inv_eq_inv_val, h]; norm_num
      rw [he]; exact hu
  by_cases h : (u : K) = -1
  · have : u⁻¹ ∈ A := hself.mpr h
    simp only [this, not_true_eq_false, if_false, h, if_true]
    ring
  · have : u⁻¹ ∉ A := fun hh => h (hself.mp hh)
    simp only [this, not_false_eq_true, if_true, h, if_false, hG u hu]
    ring

end H5ASMw47

set_option maxHeartbeats 3200000 in
open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (c₀ : ℂ)
    (hgeo :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
        (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
        (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
        (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
        (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        c₀ * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

    (hξinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ.symm z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (hfaK : IsArchTestFactor K faK)
    (hfSK : ∀ v ∈ SK, IsLocalTestFn K v (fSK v))
    (hφa : IsArchTestFactor L φa)
    (hφS : ∀ v ∈ SK, IsSemiLocalTestFn K L v (φS v))
    (hmatchA : AreMatchingArch K L σ.symm φa faK)
    (hmatchS : ∀ v ∈ SK, AreMatchingLocal K L v σ.symm (φS v) (fSK v))
    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧
      ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous φ ∧ HasCompactSupport φ ∧
        AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧
        Continuous f ∧ HasCompactSupport f ∧
        AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧
        AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧
        (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) →
        (Module.finrank K L : ℂ) * lam = c₀) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K)))
      (hTdisj : Disjoint T SK)
      (hT2 : 2 ≤ T.card)
      (hTSL : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
      (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
      (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
      (hw' : ∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal)
      (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
      (hϖirr : ∀ v ∈ T, Irreducible (ϖs v))
      (hϖs0 : ∀ v ∈ T, algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
      (ns : HeightOneSpectrum (𝓞 K) → ℕ)
      (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
      (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
      (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
      (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
      (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
      (hϖKirr : ∀ v ∈ T, Irreducible (ϖKs v))
      (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
      (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
      (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
      (hrKs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
      (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
      (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
      (s : HeightOneSpectrum (𝓞 K) → ℂ)
      (hs : ∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)),
    ∃ (ℬ : AutomorphicForm.WindingDatum (Fintype.card (NumberField.InfinitePlace K)) T.card
        (Fintype.card (NumberField.InfinitePlace K) + T.card)),
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
        (hSLF : IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
        (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL)
        (harch : IsArchBiFinite L tysL φL)
        (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ)
        (hfam : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
        (hmatch : AreMatchingAt K L σ.symm (SK ∪ T) φL
          (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x)),
      ∀ (AL BL : ℂ) (AK BK : (((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → ℂ))) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
          (∫ x in AutomorphicForm.canonicalTruncationDomain L α β, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = (R : ℂ) * AL + BL ∧
          ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (R : ℂ) * AK ξK m + BK ξK m) →
      (BL - (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * BK ξK m =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * ℬ.coeff n) := by
  classical
  classical

  have hHex :=
    AutomorphicForm.exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
      K L D σ.symm
  let H : Subgroup (AdelicGL2 (𝓞 L) L) := hHex.choose
  have hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) := hHex.choose_spec.1
  have hH := hHex.choose_spec.2.1
  have hμHex := hHex.choose_spec.2.2
  let μH : Measure H := hμHex.choose
  haveI hμH1 : μH.IsHaarMeasure := hμHex.choose_spec.1
  haveI hμH2 : μH.IsMulRightInvariant := hμHex.choose_spec.2
  have hΛ := H5ASMw47.exists_Lambda0 K L
  let Λ₀ : Subgroup (GL (Fin 2) L) := hΛ.choose
  have hΛ₀ := hΛ.choose_spec
  have hTS0 :=
    AutomorphicForm.exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
      K L α β hα hαβ D σ.symm hgen H hHc hH μH Λ₀ hΛ₀
  let κ₀ : ℝ := hTS0.choose
  have hκ₀pos : 0 < κ₀ := hTS0.choose_spec.1
  have hΩex := hTS0.choose_spec.2
  let Ω : Set H := hΩex.choose
  have hΩ := hΩex.choose_spec.1
  have hTS := hΩex.choose_spec.2
  have hΔex := H5ASMw47.exists_Delta (K := K) (L := L) (σ := σ.symm) hgen
  let Δ : Set (GL (Fin 2) L) := hΔex.choose
  have hΔd := hΔex.choose_spec.1
  have hΔdisj := hΔex.choose_spec.2.1
  have hΔcov := hΔex.choose_spec.2.2

  have hθ₀ := AutomorphicForm.continuous_injective_norm_pow_principal_range_eq_fixed_unitsMap_genuineBaseChange K L D σ.symm hgen
  have hcHex :=
    AutomorphicForm.exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
      K L D σ.symm hgen H hHc hH μH νZL νZK (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom)
      hθ₀.1 hθ₀.2.1 hθ₀.2.2.1 hθ₀.2.2.2.1 hθ₀.2.2.2.2
  let cH : ℝ := hcHex.choose
  have hcH : 0 < cH := hcHex.choose_spec.1
  have hμHl := hcHex.choose_spec.2
  have hHμ := AutomorphicForm.forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange K L νZL νZK H hHc μH cH hcH hμHl
  obtain ⟨hc0, hTc, hΦ₀S, hΦ₀s, hΦ₀⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum L α β hα hαβ

  let DK : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K := M4aHerbrand.identityDescent (𝓞 K) K K
  have hgenK : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K) := fun τ => by
    rw [Subsingleton.elim τ 1]; exact Subgroup.one_mem _
  have hHKex := AutomorphicForm.exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure K K DK 1
  let HK : Subgroup (AdelicGL2 (𝓞 K) K) := hHKex.choose
  have hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)) := hHKex.choose_spec.1
  have hHK := hHKex.choose_spec.2.1
  have hμHKex := hHKex.choose_spec.2.2
  let μHK : Measure HK := hμHKex.choose
  haveI hμHK1 : μHK.IsHaarMeasure := hμHKex.choose_spec.1
  haveI hμHK2 : μHK.IsMulRightInvariant := hμHKex.choose_spec.2
  have hΛK := H5ASMw47.exists_Lambda0 K K
  let Λ₀K : Subgroup (GL (Fin 2) K) := hΛK.choose
  have hΛ₀K := hΛK.choose_spec
  have hTSK0 := AutomorphicForm.exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser K K α β hα hαβ DK 1 hgenK HK hHKc hHK μHK Λ₀K hΛ₀K
  let κ₀K : ℝ := hTSK0.choose
  have hκ₀Kpos : 0 < κ₀K := hTSK0.choose_spec.1
  have hΩKex := hTSK0.choose_spec.2
  let ΩK' : Set HK := hΩKex.choose
  have hΩK' := hΩKex.choose_spec.1
  have hTSK := hΩKex.choose_spec.2

  obtain ⟨ΔK, nK, hΔKd, hΔKdisj, hΔKcov, hnK, hnKinj, hnKsurj⟩ :=
    AutomorphicForm.exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses K L σ.symm hgen hgenK Δ hΔd hΔdisj hΔcov
  obtain ⟨hc0K, hTcK, hΦ₀SK, hΦ₀sK, hΦ₀K⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ

  let θ₀ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom
  have hθce : Topology.IsClosedEmbedding (θ₀ : (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) := M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange K L
  let AK : Subgroup (AdeleRing (𝓞 L) L)ˣ := θ₀.range
  have hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ) := by
    show IsClosed (θ₀.range : Set (AdeleRing (𝓞 L) L)ˣ)
    rw [MonoidHom.coe_range]
    exact hθce.isClosed_range
  have hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a := by
    intro z
    rw [MonoidHom.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  let eAK0 : (AdeleRing (𝓞 K) K)ˣ ≃* AK := MonoidHom.ofInjective hθce.injective
  have heAKc : Continuous eAK0 := hθce.continuous.subtype_mk _
  have heAKc' : Continuous eAK0.symm := by
    rw [hθce.isEmbedding.continuous_iff]
    have h : ((θ₀ : (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) ∘ eAK0.symm) = fun a : AK => (a : (AdeleRing (𝓞 L) L)ˣ) := by
      funext a
      exact MonoidHom.apply_ofInjective_symm hθce.injective a
    rw [h]
    exact continuous_subtype_val
  let eAK : (AdeleRing (𝓞 K) K)ˣ ≃ₜ* AK :=
    { eAK0 with continuous_toFun := heAKc, continuous_invFun := heAKc' }
  let μAK : Measure AK := Measure.map eAK νZK
  haveI hμAK1 : μAK.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map νZK eAK
  have hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νZK := by
    intro g
    show ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂(Measure.map eAK.toHomeomorph.toMeasurableEquiv νZK) = _
    rw [MeasureTheory.integral_map_equiv]
    rfl
  let N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.ker
  have hNcont : Continuous ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm :
      (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ) :=
    Units.continuous_map (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange K L)
  have hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ) := by
    show IsClosed ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.ker : Set (AdeleRing (𝓞 L) L)ˣ)
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hNcont
  have hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔ (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1 :=
    fun z => MonoidHom.mem_ker
  haveI : LocallyCompactSpace N1 := hN1c.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μN : Measure N1 := Measure.haar
  have hcNex := M4aHerbrand.IdeleGaloisDescent.exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv K L νZL D σ.symm hgen AK hAKc hAK μAK N1 hN1c hN1 μN
  let cN : ℝ := hcNex.choose
  have hcN : 0 < cN := hcNex.choose_spec.1
  have hNc := hcNex.choose_spec.2
  have hcτex := AutomorphicForm.exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2 K L σ.symm hgen νZK
  let cτ : ℝ := hcτex.choose
  have hcτ : 0 < cτ := hcτex.choose_spec.1
  have hτex := hcτex.choose_spec.2

  let cτK : ℝ := cτ
  have hcτK : 0 < cτK := hcτ
  have hτKex := AutomorphicForm.forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2 K νZK cτK hcτK

  have hθK := AutomorphicForm.continuous_injective_norm_pow_principal_range_eq_fixed_unitsMap_genuineBaseChange K K DK 1 hgenK
  have hcHKex :=
    AutomorphicForm.exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
      K K DK 1 hgenK HK hHKc hHK μHK νZK νZK (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K K).β.toMonoidHom)
      hθK.1 hθK.2.1 hθK.2.2.1 hθK.2.2.2.1 hθK.2.2.2.2
  let cHK : ℝ := hcHKex.choose
  have hcHK : 0 < cHK := hcHKex.choose_spec.1
  have hμHKl := hcHKex.choose_spec.2
  have hHKμ' := AutomorphicForm.forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
    K K νZK νZK HK hHKc μHK cHK hcHK hμHKl

  have BCKK : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K),
      AutomorphicForm.baseChangeGL K K (AutomorphicForm.toTensorGL K K (AdeleRing (𝓞 K) K) x) = x :=
    fun x => AutomorphicForm.baseChangeGL_toTensorGL_self K x
  have hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK) := by
    intro g
    have h := hHKμ' g
    simp only [BCKK] at h
    exact h

  have hκ₀eq := AutomorphicForm.torusShell_const_eq_of_forall_lintegral_eq K L α β hα hαβ νZL ΩL hΩL D σ.symm hgen H hHc hH μH Λ₀ hΛ₀ νZK ΩK hΩK
    (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom) hθ₀.1 hθ₀.2.1 hθ₀.2.2.1 hθ₀.2.2.2.1
    cH hcH hμHl κ₀ Ω hΩ (fun y R => (hTS y R).1)
  have hκ₀Keq := AutomorphicForm.torusShell_const_eq_of_forall_lintegral_eq K K α β hα hαβ νZK ΩK hΩK DK 1 hgenK HK hHKc hHK μHK Λ₀K hΛ₀K νZK ΩK hΩK
    (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K K).β.toMonoidHom) hθK.1 hθK.2.1 hθK.2.2.1 hθK.2.2.2.1
    cHK hcHK hμHKl κ₀K ΩK' hΩK' (fun y R => (hTSK y R).1)

  let goodK : GL (Fin 2) K → Prop := fun γ =>
    ((γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1
  let γ₀ : GL (Fin 2) K := diagUnits2 (Units.mk0 (2 : K) two_ne_zero) 1
  have hγ₀ : goodK γ₀ := by
    refine ⟨⟨by simp [γ₀, diagUnits2], by simp [γ₀, diagUnits2]⟩, ?_⟩
    simp [γ₀, diagUnits2]
  let repK : GL (Fin 2) K → {γ : GL (Fin 2) K // goodK γ} := fun γ => if h : goodK γ then ⟨γ, h⟩ else ⟨γ₀, hγ₀⟩
  have hrepK : ∀ γ, goodK γ → ((repK γ : {γ : GL (Fin 2) K // goodK γ}) : GL (Fin 2) K) = γ := by
    intro γ hγ
    simp only [repK, dif_pos hγ]
  have hregK : ∀ γ, goodK γ → AutomorphicForm.IsRegularSemisimple (AutomorphicForm.globalPoints (𝓞 K) K γ) :=
    fun γ hγ => H5ASMw47.isRegularSemisimple_map_of_diagonal (algebraMap K (AdeleRing (𝓞 K) K)) γ hγ.1.1 hγ.1.2 hγ.2
  have hcenK : ∀ γ : GL (Fin 2) K,
      IsClosed ((Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))) :
        Set (AdelicGL2 (𝓞 K) K)) := by
    intro γ
    have h : ((Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))) :
        Set (AdelicGL2 (𝓞 K) K)) = {h | h * AutomorphicForm.globalPoints (𝓞 K) K γ = AutomorphicForm.globalPoints (𝓞 K) K γ * h} := by
      ext h
      simp [Subgroup.mem_centralizer_iff, eq_comm]
    rw [h]
    exact isClosed_eq (continuous_mul_right _) (continuous_mul_left _)
  let τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))) := fun γ =>
    if h : goodK γ then (hτKex γ h.1.1 h.1.2 h.2).choose
    else
      haveI := (hcenK γ).isClosedEmbedding_subtypeVal.locallyCompactSpace
      haveI : BorelSpace (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
      Measure.haar
  have hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure := by
    intro γ
    by_cases h : goodK γ
    · simp only [τK, dif_pos h]
      exact (hτKex γ h.1.1 h.1.2 h.2).choose_spec.1
    · simp only [τK, dif_neg h]
      haveI := (hcenK γ).isClosedEmbedding_subtypeVal.locallyCompactSpace
      haveI : BorelSpace (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
      infer_instance
  have hτKc : ∀ γ : GL (Fin 2) K, goodK γ → ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
          g (s : AdelicGL2 (𝓞 K) K) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK) := by
    intro γ h
    simp only [τK, dif_pos h]
    exact (hτKex γ h.1.1 h.1.2 h.2).choose_spec.2

  letI mT : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  let eT : GL (Fin 2) (AdeleRing (𝓞 L) L) ≃ₜ* GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
    (AutomorphicForm.baseChangeGLEquiv K L).symm
  let μ : Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := Measure.map eT (adelicGLHaar (Fin 2) (𝓞 L) L)
  haveI hμ : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (adelicGLHaar (Fin 2) (𝓞 L) L) eT
  have hμc : ∀ F : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = (1 : ℝ) * ∫ g, F g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
    intro F
    rw [Complex.ofReal_one, one_mul]
    show ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂(Measure.map eT.toHomeomorph.toMeasurableEquiv (adelicGLHaar (Fin 2) (𝓞 L) L)) = _
    rw [MeasureTheory.integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show F (AutomorphicForm.baseChangeGL K L ((AutomorphicForm.baseChangeGLEquiv K L).symm g)) = F g
    congr 1
    exact (AutomorphicForm.baseChangeGLEquiv K L).apply_symm_apply g

  have hCex := NumberField.exists_pos_forall_lintegral_comp_idelicNorm_haarQuotient_ker_eq_mul_setLIntegral_range K L νZL νZK N1 hN1c hN1 μN
  let Cfib : ℝ := hCex.choose
  have hCfib : 0 < Cfib := hCex.choose_spec.1
  have hCl := hCex.choose_spec.2.1
  have hCi := hCex.choose_spec.2.2

  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hGex := AutomorphicForm.exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure K
    (adelicGLHaar (Fin 2) (𝓞 K) K) inferInstance (AutomorphicForm.archHaarK K) (H5ASMw47.isHaarMeasure_archHaarK' K)
  let cK : ℝ := hGex.choose
  have hcK : 0 < cK := hGex.choose_spec.1
  have hG := hGex.choose_spec.2
  have hG'ex := AutomorphicForm.exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure K L
    μ hμ (AutomorphicForm.archHaarL K L) (H5ASMw47.isHaarMeasure_archHaarL K L)
  let cL : ℝ := hG'ex.choose
  have hcL : 0 < cL := hG'ex.choose_spec.1
  have hG' := hG'ex.choose_spec.2

  let c₀' : NNReal := ⟨cL / cK, (div_pos hcL hcK).le⟩
  have hc₀' : (c₀' : ℝ) * cK = cL := by
    show cL / cK * cK = cL
    field_simp
  have hσne : σ.symm ≠ 1 := by
    intro h1
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      rw [← hk, h1, one_zpow]
    have hsub : Subsingleton (L ≃ₐ[K] L) := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have hcard : Nat.card (L ≃ₐ[K] L) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [IsGalois.card_aut_eq_finrank] at hcard
    exact (Nat.Prime.one_lt hdeg).ne' hcard
  have CM2 := AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
    K L hdeg σ.symm hσne SK hS μ hμ cK cL hcK hcL hG hG' c₀' hc₀'

  let good : GL (Fin 2) L → Prop := fun t =>
    ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1
  let t₀ : GL (Fin 2) L := diagUnits2 (Units.mk0 (2 : L) two_ne_zero) 1
  have ht₀ : good t₀ := by
    refine ⟨⟨by simp [t₀, diagUnits2], by simp [t₀, diagUnits2]⟩, ?_⟩
    have h2 : ((t₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 / ((t₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
        algebraMap K L 2 := by
      simp [t₀, diagUnits2, map_ofNat]
    rw [h2, Algebra.norm_algebraMap]
    have hℓ : 0 < Module.finrank K L := Module.finrank_pos
    intro h
    have h' : ((2 ^ Module.finrank K L : ℕ) : K) = 1 := by exact_mod_cast h
    rw [Nat.cast_eq_one] at h'
    exact absurd h' (Nat.one_lt_two_pow_iff.mpr hℓ.ne').ne'
  let rep : GL (Fin 2) L → {t : GL (Fin 2) L // good t} := fun t => if h : good t then ⟨t, h⟩ else ⟨t₀, ht₀⟩
  have hrep : ∀ t, good t → ((rep t : {t : GL (Fin 2) L // good t}) : GL (Fin 2) L) = t := by
    intro t ht
    simp only [rep, dif_pos ht]
  let δ : GL (Fin 2) L → GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) := fun t =>
    (AutomorphicForm.baseChangeGLEquiv K L).symm (AutomorphicForm.globalPoints (𝓞 L) L (rep t).1)
  have hδrep : ∀ t, AutomorphicForm.baseChangeGL K L (δ t) = AutomorphicForm.globalPoints (𝓞 L) L (rep t).1 :=
    fun t => (AutomorphicForm.baseChangeGLEquiv K L).apply_symm_apply _
  have hδgood : ∀ t, good t → AutomorphicForm.baseChangeGL K L (δ t) = AutomorphicForm.globalPoints (𝓞 L) L t := by
    intro t ht
    rw [hδrep, hrep t ht]
  have hτt : ∀ t : GL (Fin 2) L, ∃ (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (δ t))
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (δ t))),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (δ t)) τ ∧
      (∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (δ t),
            g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
          cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νZK.prod νZK)) :=
    fun t => hτex (rep t).1 (rep t).2.1.1 (rep t).2.1.2 (rep t).2.2 (δ t) (hδrep t)
  let τ : ∀ t : GL (Fin 2) L, @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (δ t))
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (δ t)) := fun t => (hτt t).choose
  have hτ : ∀ t : GL (Fin 2) L, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (δ t)) (τ t) := fun t => (hτt t).choose_spec.1
  have hτc : ∀ t : GL (Fin 2) L, ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
      ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (δ t),
          g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ t =
        cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νZK.prod νZK) :=
    fun t => (hτt t).choose_spec.2

  obtain ⟨ξ₀, hξ₀c, hξ₀t, hξ₀N⟩ :=
    M4aHerbrand.GenuineDescent.exists_ideleChar_comp_idelicNorm_eq_of_unitsAct_invariant K L D σ hgen ξL hξc hξt hξinv
  have hΞne : Ξ.Nonempty := ⟨ξ₀, (hΞ ξ₀).2 ⟨hξ₀c, hξ₀t, hξ₀N⟩⟩

  obtain ⟨νA, cG, τG, τA, τF, cT, IA, IF, hνA, hGs, hτG, hτGc, hτA, hτF, hτF1, hcT, hT, hIA, hIF⟩ :=
    AutomorphicForm.exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn K νZK SK faK hfaK fSK hfSK cτK hcτK
  subst hνA

  have hσpow : σ.symm ^ Module.finrank K L = 1 := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  obtain ⟨δL, τGL, τAL, τFL, hδL, hδLA, hδLF, hτGL, hτGLc, hτGLcpl, hτAL, hτALc, hτFL, hτFL1, hτFLc, hTL⟩ :=
    AutomorphicForm.exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
      K L σ.symm hgen hσpow νZK cτK hcτK τG τA τF cT hτG hτGc hτA hτF hτF1 hcT hT

  have hc₀ := fun (hex : ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧
      ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous φ ∧ HasCompactSupport φ ∧
        AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧
        Continuous f ∧ HasCompactSupport f ∧
        AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧
        AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧
        (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) => AutomorphicForm.centralEllipticConstant_eq_of_factorization_of_normFibre_of_exists_ne_zero
    K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX
    ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo hex cK cL hcK hcL hG hG' AK hAKc hAK μAK hμAK N1 hN1c hN1 μN cN hcN hNc
    Cfib hCfib hCl hCi

  let lam : ℂ := ((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) /
    ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ))
  have hΞcard : ((max 1 Ξ.card : ℕ) : ℝ) = (Ξ.card : ℝ) := by
    rw [max_eq_right (Finset.card_pos.mpr hΞne)]
  have hfrK : (Module.finrank K K : ℝ) = 1 := by rw [Module.finrank_self]; simp
  have hc₀'v : (c₀' : ℝ) = cL / cK := rfl
  have hcτKv : cτK = cτ := rfl
  have hlamR : lam = (((κ₀ * (cN * cτ / (cH * 1)) * Cfib * (cL / cK)) / (κ₀K * (cτ / cHK) * Ξ.card) : ℝ) : ℂ) := by
    have hcc : ((c₀' : ℝ) : ℂ) = ((cL : ℝ) : ℂ) / ((cK : ℝ) : ℂ) := by rw [hc₀'v, Complex.ofReal_div]
    simp only [lam, hcτKv, hcc]
    push_cast
    ring
  have CONST : (∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧
      ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous φ ∧ HasCompactSupport φ ∧
        AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧
        Continuous f ∧ HasCompactSupport f ∧
        AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧
        AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧
        (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) → (Module.finrank K L : ℂ) * lam = c₀ := by
    intro hex
    have hVK : (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal ≠ 0 := by
      intro h0
      have := hκ₀Kpos
      rw [hκ₀Keq, h0] at this
      simp at this
    have hlg : Real.log (β / α) ≠ 0 := by
      intro h0
      have := hκ₀Kpos
      rw [hκ₀Keq, h0] at this
      simp at this
    have hℓ : (Module.finrank K L : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne'
    have hcard : (Ξ.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hΞne).ne'
    have key : (Module.finrank K L : ℝ) * ((κ₀ * (cN * cτ / (cH * 1)) * Cfib * (cL / cK)) / (κ₀K * (cτ / cHK) * Ξ.card)) =
        (cL / cK) * cN * Cfib * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal /
          (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal / ((max 1 Ξ.card : ℕ) : ℝ) := by
      rw [hκ₀eq, hκ₀Keq, hΞcard, hfrK]
      field_simp
    rw [hc₀ hex, hlamR]
    exact_mod_cast key
  have hlam0 : lam ≠ 0 := by
    have hpos : (0 : ℝ) < (κ₀ * (cN * cτ / (cH * 1)) * Cfib * (cL / cK)) / (κ₀K * (cτ / cHK) * Ξ.card) := by
      have hcard : (0 : ℝ) < Ξ.card := by exact_mod_cast Finset.card_pos.mpr hΞne
      have h1 : (0 : ℝ) < cN * cτ / (cH * 1) := div_pos (mul_pos hcN hcτ) (by rw [mul_one]; exact hcH)
      exact div_pos (mul_pos (mul_pos (mul_pos hκ₀pos h1) hCfib) (div_pos hcL hcK))
        (mul_pos (mul_pos hκ₀Kpos (div_pos hcτ hcHK)) hcard)
    rw [hlamR]
    exact_mod_cast hpos.ne'
  refine ⟨lam, hlam0, CONST, ?_⟩
  intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs s hs

  have HNW1 : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm (w' v).asIdeal := by
    intro v hv
    rw [hw' v hv, H5ASMw47.absNorm_pointwise_smul_algEquiv]
  have HNW2 : ∀ v ∈ T, Ideal.absNorm (w' v).asIdeal =
      Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v := by
    intro v hv
    rw [← HNW1 v hv]
    have hws : HeightOneSpectrum.under (𝓞 K) (ws v).1 = v := (ws v).2
    haveI : (ws v).1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hws).symm⟩
    exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver _ _ v.isPrime v.ne_bot
  have HXK : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
    intro ξ hξ v hv
    obtain ⟨-, -, hN⟩ := (hΞ ξ).1 hξ
    have hvT : v ∉ SK := Finset.disjoint_left.mp hTdisj hv
    have hws : HeightOneSpectrum.under (𝓞 K) (ws v).1 = v := (ws v).2
    have hw'u : HeightOneSpectrum.under (𝓞 K) (w' v) = v := by
      have h := hw' v hv
      apply HeightOneSpectrum.ext
      show Ideal.under (𝓞 K) (w' v).asIdeal = v.asIdeal
      rw [h, Ideal.under_smul]
      exact congrArg HeightOneSpectrum.asIdeal hws
    have h1 := AutomorphicForm.apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified K L ξL ξ hN v (ws v).1 hws (hur ξ hξ v hvT)
    show _ ^ v.asIdeal.inertiaDeg' (ws v).1.asIdeal = _
    rw [h1]
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (hξσ (ws v).1 (w' v) (hTSL v hv _ hws) (hTSL v hv _ hw'u) (hws.trans hw'u.symm))

  have WJA : ∃ JA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ, ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (JA u z) := by
    have hsec : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∃ w : GL (Fin 2) (InfiniteAdeleRing K) → ℝ,
        AutomorphicForm.IsSectionFnOn (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))
          (τA u z) faK w := by
      intro u z hu
      haveI := hτA u z hu
      obtain ⟨w, hw, -⟩ :=
        AutomorphicForm.exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport K _
          (H5ASMw47.isRegularSemisimple_glArch_centralScalar_mul_diagUnits2_w47 K z u hu) (τA u z) faK hfaK.2
      exact ⟨w, hw⟩
    refine ⟨fun u z => if hu : (u : K) ≠ 1 then
      ∫ x, faK (x⁻¹ * AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) *
        ((-Real.log (AutomorphicForm.WindowedSiegel.archHeight K x)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * x)) : ℝ) : ℂ) *
        (((hsec u z hu).choose x : ℝ) : ℂ) ∂(AutomorphicForm.archHaarK K) else 0, ?_⟩
    intro u z hu
    simp only [dif_pos hu]
    exact ⟨(hsec u z hu).choose, (hsec u z hu).choose_spec, rfl⟩
  obtain ⟨JA, hJA⟩ := WJA
  have WJF : ∃ JF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ, ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsWeightedOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (JF u z v) := by
    have hsecF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ v ∈ SK, ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
        AutomorphicForm.IsSectionFn K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) w := by
      intro u z hu v hv
      haveI := hτF u z v hu
      obtain ⟨I, w, hw, -⟩ := AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one K u hu z v) (τF u z v) (fSK v) (hfSK v hv)
      exact ⟨w, hw⟩
    refine ⟨fun u z v => if hu : (u : K) ≠ 1 then (if hv : v ∈ SK then
      ∫ x, fSK v (x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) * x) * ((AutomorphicForm.LocalWeight.weight x : ℝ) : ℂ) *
        (((hsecF u z hu v hv).choose x : ℝ) : ℂ) ∂(AutomorphicForm.localHaar K v) else 0) else 0, ?_⟩
    intro u z hu v hv
    simp only [dif_pos hu, dif_pos hv]
    exact ⟨(hsecF u z hu v hv).choose, (hsecF u z hu v hv).choose_spec, rfl⟩
  obtain ⟨JF, hJF⟩ := WJF

  have WJA' : ∃ JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ, (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ.symm (AutomorphicForm.archHaarL K L)
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (AutomorphicForm.tensorArch K L (δL u z)) (τAL u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z)) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0) := by
    have hsecA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
        ∃ w : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ,
          AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ.symm (AutomorphicForm.tensorArch K L (δL u z)) (τAL u z)
            (φa ∘ AutomorphicForm.archIdentGL K L) w := by
      intro u z hu hN
      haveI := hτAL u z hu
      have hreg : AutomorphicForm.IsRegularSemisimple
          (AutomorphicForm.normString K L (InfiniteAdeleRing K) σ.symm (AutomorphicForm.tensorArch K L (δL u z))) := by
        rw [hδLA u z hu hN]
        exact H5ASMw47.isRegularSemisimple_toTensorGL_w47 K L _ _ (H5ASMw47.isRegularSemisimple_glArch_centralScalar_mul_diagUnits2_w47 K z u hu)
      have hcs : HasCompactSupport (φa ∘ AutomorphicForm.archIdentGL K L) := by
        have : (φa ∘ ⇑(AutomorphicForm.archIdentGL K L)) = φa ∘ ⇑(AutomorphicForm.archIdentGLEquiv K L).toHomeomorph := rfl
        rw [this]
        exact hφa.2.comp_homeomorph _
      obtain ⟨w, hw, -⟩ :=
        AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport K L σ.symm _ hreg (τAL u z) (φa ∘ AutomorphicForm.archIdentGL K L) hcs
      exact ⟨w, hw⟩
    refine ⟨fun u z => if hu : (u : K) ≠ 1 then (if hN : (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) then
      ∫ x, (φa ∘ AutomorphicForm.archIdentGL K L) (x⁻¹ * AutomorphicForm.tensorArch K L (δL u z) * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ.symm x) *
        ((-Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L x))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L x)) : ℝ) : ℂ) *
        (((hsecA' u z hu hN).choose x : ℝ) : ℂ) ∂(AutomorphicForm.archHaarL K L) else 0) else 0, ?_, ?_⟩
    · intro u z hu hN
      simp only [dif_pos hu, dif_pos hN]
      exact ⟨(hsecA' u z hu hN).choose, (hsecA' u z hu hN).choose_spec, rfl⟩
    · intro u z hu hN
      simp only [dif_pos hu, dif_neg hN]
  obtain ⟨JA', hJA', hJA'0⟩ := WJA'
  have WJF' : ∃ JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ, (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ.symm (AutomorphicForm.tensorPlace K L v (δL u z)) (τFL u z v) (φS v) (JF' u z v)) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0) := by
    have hsecF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
        ∃ w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
          AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ.symm (AutomorphicForm.tensorPlace K L v (δL u z)) (τFL u z v)
            (φS v) w := by
      intro u z hu v hv hN
      haveI : IsReduced (L ⊗[K] v.adicCompletion K) := Algebra.isReduced_tensorProduct_of_perfectField K (v.adicCompletion K) L
      have hreg : AutomorphicForm.IsRegularSemisimple
          (AutomorphicForm.normString K L (v.adicCompletion K) σ.symm (AutomorphicForm.tensorPlace K L v (δL u z))) := by
        rw [hδLF u z v hu hN]
        exact H5ASMw47.isRegularSemisimple_toTensorGL_w47 K L _ _ (AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one K u hu z v)
      obtain ⟨w, hw, -⟩ :=
        AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing K L (v.adicCompletion K) σ.symm _ hreg (τFL u z v) (hτFL u z v hu) (φS v) (hφS v hv).2
      exact ⟨w, hw⟩
    refine ⟨fun u z v => if hu : (u : K) ≠ 1 then (if hv : v ∈ SK then (if hN : (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) then
      ∫ x, φS v (x⁻¹ * AutomorphicForm.tensorPlace K L v (δL u z) * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ.symm x) *
        ((AutomorphicForm.semiLocalWeight K L v x : ℝ) : ℂ) *
        (((hsecF' u z hu v hv hN).choose x : ℝ) : ℂ) ∂(AutomorphicForm.semiLocalHaar K L v) else 0) else 0) else 0, ?_, ?_⟩
    · intro u z hu v hv hN
      simp only [dif_pos hu, dif_pos hv, dif_pos hN]
      exact ⟨(hsecF' u z hu v hv hN).choose, (hsecF' u z hu v hv hN).choose_spec, rfl⟩
    · intro u z hu v hv hN
      simp only [dif_pos hu, dif_pos hv, dif_neg hN]
  obtain ⟨JF', hJF', hJF'0⟩ := WJF'

  let κm : ℂ := (1 / 2 : ℂ)
  obtain ⟨ℬ, hPD⟩ :=
    AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX
      ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs
      ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs hur HNW1 HNW2 s hs HXK hfaK hfSK κ₀K (cτK / cHK) cτK hcτK (AutomorphicForm.archHaarK K) cG hGs
      τG hτG hτGc τA hτA τF hτF hτF1 cT hcT hT IA hIA IF hIF hφa hφS hmatchA hmatchS κ₀ (cN * cτ / (cH * 1)) cL cT Cfib
      hcL hcT hCfib JA hJA JF hJF (AutomorphicForm.archHaarL K L) rfl rfl
      (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
      (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
      JA' hJA' hJA'0 JF' hJF' hJF'0 κm
  refine ⟨ℬ, ?_⟩
  intro ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc AKc BKc R₀ hSP

  let φw : (AdeleRing (𝓞 L) L)ˣ → GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ := fun w =>
    (fun g : AdelicGL2 (𝓞 L) L => φL (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘ AutomorphicForm.baseChangeGL K L
  have hφwc : ∀ w, HasCompactSupport (φw w) := by
    intro w
    have h1 : HasCompactSupport (fun g : AdelicGL2 (𝓞 L) L => φL (AutomorphicForm.centralScalar (𝓞 L) L w * g)) :=
      hφLc.comp_homeomorph (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 L) L w))
    exact h1.comp_homeomorph (AutomorphicForm.baseChangeGLEquiv K L).toHomeomorph
  have hregt : ∀ t, AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm (δ t)) := fun t =>
    AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one K L σ.symm hgen
      (rep t).1 (rep t).2.1.1 (rep t).2.1.2 (rep t).2.2 (δ t) (hδrep t)
  have hsec : ∀ t w, ∃ s, AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ.symm (δ t) (τ t) (φw w) s :=
    fun t w => AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString K L σ.symm
      (δ t) (hregt t) (τ t) (hτ t) (φw w) (hφwc w)
  let wt : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ := fun x =>
    -Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.baseChangeGL K L x))
      - Real.log (NumberField.AdelicHeight.adelicHeight L
          (AutomorphicForm.adelicWeyl (𝓞 L) L * AutomorphicForm.baseChangeGL K L x))
  let IL : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun t w =>
    ∫ x, (φw w) (x⁻¹ * δ t * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ.symm x) * ((hsec t w).choose x : ℂ) ∂μ
  let JL : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun t w =>
    ∫ x, (φw w) (x⁻¹ * δ t * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ.symm x) * (wt x : ℂ) *
      ((hsec t w).choose x : ℂ) ∂μ
  have hIL : ∀ t ∈ Δ, ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ.symm μ (δ t) (τ t) (φw w) (IL t w) :=
    fun t _ w => ⟨(hsec t w).choose, (hsec t w).choose_spec, rfl⟩
  have hJL : ∀ t ∈ Δ, ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ.symm μ wt (δ t) (τ t) (φw w) (JL t w) :=
    fun t _ w => ⟨(hsec t w).choose, (hsec t w).choose_spec, rfl⟩

  have LC0 := AutomorphicForm.exists_finset_forall_slope_eq_sum_twistedClassIntegral_and_intercept_eq_sum_weightedTwistedClassIntegral_haarQuotient_of_eq_affine K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
    T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
    ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc R₀ (fun R hR => (hSP R hR).1)
  have LC1 := LC0 H hHc hH μH Λ₀ hΛ₀ κ₀ hκ₀pos Ω hΩ (fun y R => (hTS y R).1) (fun y R => (hTS y R).2)
  have LC2 := LC1 Δ hΔd hΔdisj hΔcov hξinv
  have LC3 := LC2 μ hμ 1 one_pos hμc cH hcH hHμ cτ hcτ AK hAKc hAK μAK hμAK N1 hN1c hN1 μN cN hcN hNc
  have LC4 := LC3 δ (fun t ht => hδgood t ⟨⟨(hΔd t ht).1, (hΔd t ht).2.1⟩, (hΔd t ht).2.2⟩) τ hτ (fun t _ => hτc t)
  have LC := LC4 IL JL hIL hJL

  have hfamc : ∀ m, m ∈ SatakeCombination.slotIndex K L ws ks js T → Continuous (fam m) ∧ HasCompactSupport (fam m) := by
    intro m hm
    obtain ⟨-, -, hfaK, -, ff, hffin, -, -, hfeq⟩ := hfam m hm
    exact AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K (fam m) ⟨faK, ff, hfaK, hffin, hfeq⟩
  let fz : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) → (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K → ℂ :=
    fun m z g => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)
  have hfzc : ∀ m, m ∈ SatakeCombination.slotIndex K L ws ks js T → ∀ z, HasCompactSupport (fz m z) := fun m hm z =>
    (hfamc m hm).2.comp_homeomorph (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 K) K z))
  have hsecK : ∀ m, m ∈ SatakeCombination.slotIndex K L ws ks js T → ∀ γ, goodK γ → ∀ z, ∃ w,
      AutomorphicForm.IsSectionFnOn (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ) (fz m z) w := by
    intro m hm γ hγ z
    haveI := hτK γ
    exact AutomorphicForm.exists_isSectionFnOn_adeleRing_of_isRegularSemisimple K _ (hregK γ hγ) (τK γ) (fz m z) (hfzc m hm z)
  let wtK : AdelicGL2 (𝓞 K) K → ℝ := fun x =>
    -Real.log (NumberField.AdelicHeight.adelicHeight K x)
      - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x))
  let IK : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) → GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    fun m γ z => if h : m ∈ SatakeCombination.slotIndex K L ws ks js T ∧ goodK γ then
      ∫ x, fz m z (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * x) * ((hsecK m h.1 γ h.2 z).choose x : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) else 0
  let JK : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) → GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    fun m γ z => if h : m ∈ SatakeCombination.slotIndex K L ws ks js T ∧ goodK γ then
      ∫ x, fz m z (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * x) * (wtK x : ℂ) * ((hsecK m h.1 γ h.2 z).choose x : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) else 0
  have hIK : ∀ m (hm : m ∈ SatakeCombination.slotIndex K L ws ks js T) γ (hγ : goodK γ) (z : (AdeleRing (𝓞 K) K)ˣ),
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ) (fz m z) (IK m γ z) := by
    intro m hm γ hγ z
    refine ⟨(hsecK m hm γ hγ z).choose, (hsecK m hm γ hγ z).choose_spec, ?_⟩
    simp only [IK, dif_pos (And.intro hm hγ)]
  have hJK : ∀ m (hm : m ∈ SatakeCombination.slotIndex K L ws ks js T) γ (hγ : goodK γ) (z : (AdeleRing (𝓞 K) K)ˣ),
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) wtK
        (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ) (fz m z) (JK m γ z) := by
    intro m hm γ hγ z
    refine ⟨(hsecK m hm γ hγ z).choose, (hsecK m hm γ hγ z).choose_spec, ?_⟩
    simp only [JK, dif_pos (And.intro hm hγ)]
  have goodK_of_mem : ∀ γ, γ ∈ ΔK → goodK γ := by
    intro γ hγ
    refine ⟨⟨(hΔKd γ hγ).1, (hΔKd γ hγ).2.1⟩, ?_⟩
    have h := (hΔKd γ hγ).2.2
    simpa only [Algebra.norm_self, MonoidHom.id_apply] using h

  have KC := fun (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (hξK : ξK ∈ Ξ)
      (m : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) (hm : m ∈ SatakeCombination.slotIndex K L ws ks js T) =>
    AutomorphicForm.exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
      T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
      ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ξK hξK m hm (AKc ξK m) (BKc ξK m) R₀ (fun R hR => (hSP R hR).2 ξK hξK m hm)
      DK hgenK HK hHKc hHK μHK Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK' (fun y R => (hTSK y R).1) (fun y R => (hTSK y R).2)
      ΔK hΔKd hΔKdisj hΔKcov cHK hcHK hHKμ cτK hcτK τK hτK (fun γ hγ => hτKc γ (goodK_of_mem γ hγ))
      (IK m) (JK m) (fun γ hγ z => hIK m hm γ (goodK_of_mem γ hγ) z) (fun γ hγ z => hJK m hm γ (goodK_of_mem γ hγ) z)

  have hAMO := (CM2 (SK ∪ T) Finset.subset_union_left φL
    (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x)
    hmatch (fun v _ hv => AutomorphicForm.areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_prime
      K L hdeg σ.symm hσne v hv)).1

  obtain ⟨Δφ, hΔφ, hLCS⟩ := LC

  have OCW : ∀ γ, goodK γ →
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) wtK
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
            ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
              (SatakeCombination.slotFamilyCoeff K L ws ks js T m : ℂ) * fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g))
          (∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
              (SatakeCombination.slotFamilyCoeff K L ws ks js T m : ℂ) * JK m γ z)) ∧
      (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, Measurable (JK m γ)) := by
    intro γ hγ
    haveI := hτK γ
    exact AutomorphicForm.isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal K
      (SatakeCombination.slotIndex K L ws ks js T) (fun m => (SatakeCombination.slotFamilyCoeff K L ws ks js T m : ℂ))
      γ ⟨hγ.1.1, hγ.1.2, hγ.2⟩ (τK γ) fam (fun m hm => hfamc m hm)
      (fun m => JK m γ) (fun m hm z => hJK m hm γ hγ z)
  let JKF : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun γ z =>
    ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * JK m γ z

  let fT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ := fun v x =>
    if hv : v ∈ T then
      ∑ e ∈ (SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
        (SatakeCombination.slotCoeff K L ws v (ks v) (js v) e : ℂ) *
          ∑ ι : Fin (e 0) → Fin (nKs v),
            (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (e 1))⁻¹ * x)
    else 0
  let F : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ := fun x =>
    ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x
  have hfT : ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (fT v) := by
    intro v hv
    have : (fT v) = fun x => ∑ e ∈ (SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
        (SatakeCombination.slotCoeff K L ws v (ks v) (js v) e : ℂ) *
          ∑ ι : Fin (e 0) → Fin (nKs v),
            (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (e 1))⁻¹ * x) := by
      funext x; simp only [fT, dif_pos hv]
    rw [this]
    exact H5ASMw47.isLocalTestFn_finset_sum_w47 K v _ _ (fun e _ =>
      H5ASMw47.isLocalTestFn_const_mul_w47 K v _ _
        (AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v (nKs v) (rKs v) (zKs v) (e 0) (e 1)))
  have FUF : ∃ ffF : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
      AutomorphicForm.IsUnitFactorization K (SK ∪ T) F faK ffF (fun v => if v ∈ T then fT v else fSK v) := by
    classical
    let ffm : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ :=
      fun m => if hm : m ∈ SatakeCombination.slotIndex K L ws ks js T then (hfam m hm).2.2.2.2.choose else 0
    have hffm : ∀ m (hm : m ∈ SatakeCombination.slotIndex K L ws ks js T),
        AutomorphicForm.IsFinTestFactor K (ffm m) ∧
        (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
          (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ AutomorphicForm.localIntegralSet K v) →
            ffm m h = ∏ v ∈ SK ∪ T,
              (if hv : v ∈ T then (fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x))
                else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
        (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
          (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ AutomorphicForm.localIntegralSet K v) → ffm m h = 0) ∧
        (∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ffm m (AdelicLevel.glFin (𝓞 K) K g)) := by
      intro m hm
      have h := (hfam m hm).2.2.2.2.choose_spec
      simp only [ffm, dif_pos hm]
      exact h
    refine ⟨fun h => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * ffm m h,
      hfaK, ?_, ?_, ?_, ?_, ?_⟩
    · exact H5ASMw47.isFinTestFactor_finset_sum_w47 K _ _ _ (fun m hm => (hffm m hm).1)
    · intro v hv
      by_cases hvT : v ∈ T
      · simp only [if_pos hvT]; exact hfT v hvT
      · simp only [if_neg hvT]
        rcases Finset.mem_union.mp hv with h | h
        · exact hfSK v h
        · exact absurd h hvT
    · intro h hint
      have hdisj : Disjoint SK T := hTdisj.symm

      have hm_eq : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ffm m h =
          (∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v h)) *
            ∏ v ∈ T.attach, (fun x : GL (Fin 2) (v.1.adicCompletion K) =>
                      ∑ ι : Fin ((m v.1 v.2) 0) → Fin (nKs v.1),
                        (AutomorphicForm.localIntegralSet K v.1).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v.1 (ι m)).prod * zKs v.1 ^ (m v.1 v.2) 1)⁻¹ * x)) (AdelicLevel.finComponent (𝓞 K) K v.1 h) := by
        intro m hm
        rw [(hffm m hm).2.1 h hint, Finset.prod_union hdisj]
        congr 1
        · refine Finset.prod_congr rfl fun v hv => ?_
          rw [dif_neg (Finset.disjoint_left.mp hdisj hv)]
        · rw [← Finset.prod_attach T]
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [dif_pos v.2]

      have hT_eq : ∀ v ∈ T, (if v ∈ T then fT v else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h) =
          ∑ e ∈ (SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
            (SatakeCombination.slotCoeff K L ws v (ks v) (js v) e : ℂ) *
              ∑ ι : Fin (e 0) → Fin (nKs v),
                (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (e 1))⁻¹ * AdelicLevel.finComponent (𝓞 K) K v h) := by
        intro v hv
        simp only [if_pos hv, fT, dif_pos hv]
      have hSK_eq : ∀ v ∈ SK, (if v ∈ T then fT v else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h) =
          fSK v (AdelicLevel.finComponent (𝓞 K) K v h) := by
        intro v hv; rw [if_neg (Finset.disjoint_left.mp hdisj hv)]
      have RHS : ∏ v ∈ SK ∪ T, (if v ∈ T then fT v else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h) =
          (∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v h)) *
            ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∏ v ∈ T.attach,
              (SatakeCombination.slotCoeff K L ws v.1 (ks v.1) (js v.1) (m v.1 v.2) : ℂ) * (∑ ι : Fin ((m v.1 v.2) 0) → Fin (nKs v.1),
                (AutomorphicForm.localIntegralSet K v.1).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rKs v.1 (ι m)).prod * zKs v.1 ^ (m v.1 v.2) 1)⁻¹ * AdelicLevel.finComponent (𝓞 K) K v.1 h)) := by
        rw [Finset.prod_union hdisj, Finset.prod_congr rfl hSK_eq, Finset.prod_congr rfl hT_eq, Finset.prod_sum]
        rfl
      have LHS : ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * ffm m h =
          (∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v h)) *
            ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∏ v ∈ T.attach,
              (SatakeCombination.slotCoeff K L ws v.1 (ks v.1) (js v.1) (m v.1 v.2) : ℂ) * (∑ ι : Fin ((m v.1 v.2) 0) → Fin (nKs v.1),
                (AutomorphicForm.localIntegralSet K v.1).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rKs v.1 (ι m)).prod * zKs v.1 ^ (m v.1 v.2) 1)⁻¹ * AdelicLevel.finComponent (𝓞 K) K v.1 h)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [hm_eq m hm, Finset.prod_mul_distrib]
        simp only [SatakeCombination.slotFamilyCoeff]
        ring
      beta_reduce
      rw [LHS, RHS]
    · intro h hbad
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [(hffm m hm).2.2.1 h hbad, mul_zero]
    · intro g
      simp only [F, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [(hffm m hm).2.2.2 g]
      ring
  obtain ⟨ffF, hFUF⟩ := FUF

  have hwordT : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      AutomorphicForm.IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ ((m v hv) 1))⁻¹ * x)) := by
    intro m hm v hv
    exact AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v (nKs v) (rKs v) (zKs v) ((m v hv) 0) ((m v hv) 1)
  have hITex : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ v ∈ T, ∃ I : ℂ,
      AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fT v) I := by
    intro u z hu v hv
    haveI := hτF u z v hu
    exact AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn K v _ (AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one K u hu z v) (τF u z v) (fT v) (hfT v hv)
  let IT : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ := fun u z v =>
    if hu : (u : K) ≠ 1 then (if hv : v ∈ T then (hITex u z hu v hv).choose else 0) else 0
  have hIT : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fT v) (IT u z v) := by
    intro u z hu v hv
    simp only [IT, dif_pos hu, dif_pos hv]
    exact (hITex u z hu v hv).choose_spec
  have hIWex : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 →
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T), ∃ I : ℂ,
        AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ ((m v hv) 1))⁻¹ * x)) I := by
    intro m hm u z hu v hv
    haveI := hτF u z v hu
    exact AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn K v _ (AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one K u hu z v) (τF u z v) _ (hwordT m hm v hv)
  let IW : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ :=
    fun m u z v => if hm : m ∈ SatakeCombination.slotIndex K L ws ks js T then (if hu : (u : K) ≠ 1 then
      (if hv : v ∈ T then (hIWex m hm u z hu v hv).choose else 0) else 0) else 0
  have hIW : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ u z, ((u : Kˣ) : K) ≠ 1 →
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
        AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ ((m v hv) 1))⁻¹ * x)) (IW m u z v) := by
    intro m hm u z hu v hv
    simp only [IW, dif_pos hm, dif_pos hu, dif_pos hv]
    exact (hIWex m hm u z hu v hv).choose_spec
  have hindT : ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.IsLocalTestFn K v ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) := by
    intro v
    have h := (AutomorphicForm.isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence K v 1).1
    simpa using h
  have hIUex : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ v : HeightOneSpectrum (𝓞 K), ∃ I : ℂ,
      AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) I := by
    intro u z hu v
    haveI := hτF u z v hu
    exact AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn K v _ (AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one K u hu z v) (τF u z v) _ (hindT v)
  let IU : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ := fun u z v =>
    if hu : (u : K) ≠ 1 then (hIUex u z hu v).choose else 0
  have hIU : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∉ SK ∪ T, AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v)
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (IU u z v) := by
    intro u z hu v _
    simp only [IU, dif_pos hu]
    exact (hIUex u z hu v).choose_spec

  let Δf : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) →
      Finset (GL (Fin 2) K) := fun ξ m =>
    if h : ξ ∈ Ξ ∧ m ∈ SatakeCombination.slotIndex K L ws ks js T then (KC ξ h.1 m h.2).choose else ∅
  have hΔf : ∀ ξ ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, (↑(Δf ξ m) : Set (GL (Fin 2) K)) ⊆ ΔK := by
    intro ξ hξ m hm
    simp only [Δf, dif_pos (And.intro hξ hm)]
    exact (KC ξ hξ m hm).choose_spec.1

  have WFFT := And.intro (AutomorphicForm.isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS fT hfT
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 IT hIT IU hIU)
    (AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS fT hfT
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 IT hIT IU hIU)
  let gm : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ :=
    fun m v x => if hv : v ∈ T then (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) x else 0
  have hgm : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (gm m v) := by
    intro m hm v hv
    have : gm m v = (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) := by funext x; simp only [gm, dif_pos hv]
    rw [this]; exact hwordT m hm v hv
  have hIWg : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      AutomorphicForm.IsOrbitalIntegral K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
        (τF u z v) (gm m v) (IW m u z v) := by
    intro m hm u z hu v hv
    have : gm m v = (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) := by funext x; simp only [gm, dif_pos hv]
    rw [this]; exact hIW m hm u z hu v hv
  have WFFm := fun m (hm : m ∈ SatakeCombination.slotIndex K L ws ks js T) => And.intro
    (AutomorphicForm.isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS (gm m) (hgm m hm)
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 (IW m) (hIWg m hm) IU hIU)
    (AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS (gm m) (hgm m hm)
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 (IW m) (hIWg m hm) IU hIU)
  let UT : Finset Kˣ := WFFT.2.choose
  have hUT := WFFT.2.choose_spec
  let Um : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → Finset Kˣ :=
    fun m => if hm : m ∈ SatakeCombination.slotIndex K L ws ks js T then (WFFm m hm).2.choose else ∅
  have hUm : ∀ m (hm : m ∈ SatakeCombination.slotIndex K L ws ks js T), ∀ u : Kˣ, u ∉ Um m → (u : K) ≠ 1 →
      ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        (∏ v ∈ T, IW m u z v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u z v) *
          ((JA' u z - (Module.finrank K L : ℂ) * JA u z) * ∏ v ∈ SK, IF u z v +
            IA u z * ∑ v ∈ SK, (JF' u z v - (Module.finrank K L : ℂ) * JF u z v) *
              ∏ v' ∈ SK.erase v, IF u z v') = 0 := by
    intro m hm u hu
    simp only [Um, dif_pos hm] at hu
    exact (WFFm m hm).2.choose_spec u hu
  let Uall : Finset Kˣ := UT ∪ (SatakeCombination.slotIndex K L ws ks js T).biUnion Um

  have hΔKrat : ∀ u : Kˣ, (u : K) ≠ 1 → ∃ t ∈ ΔK,
      (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K) ∨
      (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K)⁻¹ := by
    exact fun u hu => (AutomorphicForm.exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps K hgenK ΔK hΔKd hΔKdisj hΔKcov).1 u hu
  let rep : Kˣ → Finset (GL (Fin 2) K) := fun u => if h : (u : K) ≠ 1 then {(hΔKrat u h).choose} else ∅
  have hrep : ∀ u : Kˣ, (↑(rep u) : Set (GL (Fin 2) K)) ⊆ ΔK := by
    intro u γ hγ
    by_cases h : (u : K) ≠ 1
    · simp only [rep, dif_pos h, Finset.coe_singleton, Set.mem_singleton_iff] at hγ
      rw [hγ]; exact (hΔKrat u h).choose_spec.1
    · simp only [rep, dif_neg h, Finset.coe_empty, Set.mem_empty_iff_false] at hγ
  let SK0 : Finset (GL (Fin 2) K) := ((Ξ ×ˢ SatakeCombination.slotIndex K L ws ks js T).biUnion (fun p => Δf p.1 p.2) ∪ Δφ.image nK) ∪ Uall.biUnion rep

  let pre : GL (Fin 2) K → Finset (GL (Fin 2) L) := fun γ => if h : ∃ t ∈ Δ, nK t = γ then {h.choose} else ∅
  let SL : Finset (GL (Fin 2) L) := Δφ ∪ SK0.biUnion pre
  have hSL : (↑SL : Set (GL (Fin 2) L)) ⊆ Δ := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact hΔφ h
    · obtain ⟨γ, -, hγ⟩ := Finset.mem_biUnion.mp h
      by_cases hex : ∃ t ∈ Δ, nK t = γ
      · simp only [pre, dif_pos hex, Finset.mem_singleton] at hγ
        rw [hγ]; exact hex.choose_spec.1
      · simp [pre, dif_neg hex] at hγ
  let SKf : Finset (GL (Fin 2) K) := SK0 ∪ SL.image nK
  have hSKf : (↑SKf : Set (GL (Fin 2) K)) ⊆ ΔK := by
    intro γ hγ
    rcases Finset.mem_union.mp hγ with h | h
    · rcases Finset.mem_union.mp h with h0 | h0
      · rcases Finset.mem_union.mp h0 with h1 | h1
        · obtain ⟨p, hp, hγp⟩ := Finset.mem_biUnion.mp h1
          obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
          exact hΔf p.1 hp1 p.2 hp2 hγp
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h1
          exact (hnK t (hΔφ ht)).1
      · obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.mp h0
        exact hrep u hu
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (hnK t (hSL ht)).1
  have hnSL : ∀ t ∈ SL, nK t ∈ SKf := fun t ht =>
    Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨t, ht, rfl⟩))
  have hninjSL : ∀ t ∈ SL, ∀ t' ∈ SL, nK t = nK t' → t = t' := fun t ht t' ht' h =>
    hnKinj t (hSL ht) t' (hSL ht') h
  have hnr : ∀ t ∈ SL, ((nK t : Matrix (Fin 2) (Fin 2) K) 0 0 / (nK t : Matrix (Fin 2) (Fin 2) K) 1 1) =
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    intro t ht
    obtain ⟨-, -, -, h00, h11⟩ := hnK t (hSL ht)
    rw [h00, h11, H5ASMw47.norm_div_w47]

  have hmiss : ∀ γ ∈ SKf, (∀ t ∈ SL, nK t ≠ γ) →
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∉ Set.range (Algebra.norm K : L → K) := by
    intro γ hγ hnot hnormic
    obtain ⟨t, htΔ, ht⟩ := hnKsurj γ (hSKf hγ) hnormic
    have hex : ∃ t ∈ Δ, nK t = γ := ⟨t, htΔ, ht⟩
    rcases Finset.mem_union.mp hγ with h | h
    · have hmem : hex.choose ∈ SL := by
        refine Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨γ, h, ?_⟩))
        simp only [pre, dif_pos hex, Finset.mem_singleton]
      exact hnot _ hmem hex.choose_spec.2
    · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h
      exact hnot t' ht' rfl

  have hnKgood : ∀ t ∈ Δ, goodK (nK t) := by
    intro t ht
    obtain ⟨-, h10, h01, h00, h11⟩ := hnK t ht
    refine ⟨⟨h10, h01⟩, ?_⟩
    rw [h00, h11, ← H5ASMw47.norm_div_w47]
    exact (hΔd t ht).2.2
  have hγδ : ∀ t ∈ Δ, AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm (δ t) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K (nK t)) := by
    intro t ht
    obtain ⟨γ', h10, h01, h00, h11, hns⟩ :=
      AutomorphicForm.exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints K L σ.symm hgen
        t (hΔd t ht).1 (hΔd t ht).2.1 (δ t) (hδgood t ⟨⟨(hΔd t ht).1, (hΔd t ht).2.1⟩, (hΔd t ht).2.2⟩)
    obtain ⟨-, k10, k01, k00, k11⟩ := hnK t ht
    have hγ' : γ' = nK t := H5ASMw47.GL2_eq_of_entries_w47 γ' (nK t) (h00.trans k00.symm) (h01.trans k01.symm)
      (h10.trans k10.symm) (h11.trans k11.symm)
    rw [hns, hγ']
  have hc₀'ne : (c₀' : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (c₀' : ℝ) := div_pos hcL hcK
    exact_mod_cast this.ne'
  have hBL := (hLCS SL Finset.subset_union_left hSL).2.2.2
  have hBK : ∀ ξ ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      BKc ξ m = ∑ t ∈ SKf, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK m t z ∂νZK) := by
    intro ξ hξ m hm
    have hsub : Δf ξ m ⊆ SKf := by
      intro γ hγ
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨(ξ, m), Finset.mem_product.mpr ⟨hξ, hm⟩, hγ⟩))))))
    have hΔfeq : Δf ξ m = (KC ξ hξ m hm).choose := by simp only [Δf, dif_pos (And.intro hξ hm)]
    exact ((KC ξ hξ m hm).choose_spec.2 SKf (hΔfeq ▸ hsub) hSKf).2.2.2

  let φT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ := fun v x =>
    ∑ ι : Fin (ks v) → Fin (ns v),
      (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
        ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
          ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
  have hφT : ∀ v ∈ T, AutomorphicForm.IsSemiLocalTestFn K L v (φT v) := by
    intro v _
    exact AutomorphicForm.isSemiLocalTestFn_sum_indicator_semiLocalIntegralSet_word K L ws ns rTs zs ks js v
  have hmatchTφ : ∀ v ∈ T, AutomorphicForm.AreMatchingLocal K L v σ.symm (φT v) (fT v) := by
    intro v hv
    have hvS : v ∉ SK := Finset.disjoint_left.mp hTdisj hv
    have h := AutomorphicForm.areMatchingLocal_heckeWord_sum_coeff_univWord_mul_heckeWord_of_ramificationIdx_eq_one_of_prime
      K L hdeg σ.symm hσne v (fun w hw => hS w (hw ▸ hvS)) (ws v) (ϖs v) (hϖirr v hv) (hϖs0 v hv) (ns v) (rTs v) (hrTs v hv)
      (zs v) (hzs v hv) (ϖKs v) (hϖKirr v hv) (hϖKs0 v hv) (nKs v) (rKs v) (hrKs v hv) (zKs v) (hzKs v hv) (ks v) (js v)
    have e1 : (fT v) = fun x => ∑ e ∈ (SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
        (SatakeCombination.slotCoeff K L ws v (ks v) (js v) e : ℂ) *
          ∑ ι : Fin (e 0) → Fin (nKs v),
            (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (e 1))⁻¹ * x) := by
      funext x; simp only [fT, dif_pos hv]
    rw [e1]
    exact h
  have hmatchT' : ∀ v ∈ T, ∃ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv ∧ AutomorphicForm.AreMatchingLocal K L v σ.symm φv (fT v) :=
    fun v hv => ⟨φT v, hφT v hv, hmatchTφ v hv⟩
  have hJT : ∀ v ∈ T, ∀ (a b : (v.adicCompletion K)ˣ), a ≠ b → ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ),
      AutomorphicForm.normString K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (LanglandsTunnell.CubicInduction.diagUnits2 a b) →
      ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (LanglandsTunnell.CubicInduction.diagUnits2 a b))
          (AutomorphicForm.localCentralizerBorel K v (LanglandsTunnell.CubicInduction.diagUnits2 a b))),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (LanglandsTunnell.CubicInduction.diagUnits2 a b)) τ →
        τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 →
      ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β))),
        @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β)) τ' →
        τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
      ∀ J J' : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v (LanglandsTunnell.CubicInduction.diagUnits2 a b) τ (fT v) J →
        AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β) τ' (φT v) J' →
        J' = (Module.finrank K L : ℂ) * J := by
    intro v hv a b hab α' β' hN τ' hτ' hτ'1 τ'' hτ'' hτ''1 J J' hJ hJ'
    have hvS : v ∉ SK := Finset.disjoint_left.mp hTdisj hv
    have e1 : (fT v) = fun x => ∑ e ∈ (SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
        (SatakeCombination.slotCoeff K L ws v (ks v) (js v) e : ℂ) *
          ∑ ι : Fin (e 0) → Fin (nKs v),
            (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (e 1))⁻¹ * x) := by
      funext x; simp only [fT, dif_pos hv]
    rw [e1] at hJ
    exact AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified K L hdeg σ.symm hσne v
      (fun w hw => hS w (hw ▸ hvS)) ws (ϖs v) (hϖirr v hv) (hϖs0 v hv) (ns v) (rTs v) (hrTs v hv) (zs v) (hzs v hv)
      (ϖKs v) (hϖKirr v hv) (hϖKs0 v hv) (nKs v) (rKs v) (hrKs v hv) (zKs v) (hzKs v hv) (ks v) (js v)
      a b hab α' β' hN τ' hτ' hτ'1 τ'' hτ'' hτ''1 J J' hJ hJ'
  have hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T →
      AutomorphicForm.AreMatchingLocal K L v σ.symm
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) := by
    intro v hv _
    exact AutomorphicForm.areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_prime K L hdeg σ.symm hσne v (fun w hw => hS w (hw ▸ hv))
  have hunitW : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T →
      ∀ (a b : (v.adicCompletion K)ˣ), a ≠ b → ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ),
      AutomorphicForm.normString K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (LanglandsTunnell.CubicInduction.diagUnits2 a b) →
      ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (LanglandsTunnell.CubicInduction.diagUnits2 a b))
          (AutomorphicForm.localCentralizerBorel K v (LanglandsTunnell.CubicInduction.diagUnits2 a b))),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (LanglandsTunnell.CubicInduction.diagUnits2 a b)) τ →
        τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 →
      ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β))),
        @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β)) τ' →
        τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
      ∀ J J' : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v (LanglandsTunnell.CubicInduction.diagUnits2 a b) τ
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) J →
        AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ.symm (LanglandsTunnell.CubicInduction.diagUnits2 α β) τ'
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) J' →
        J' = (Module.finrank K L : ℂ) * J := by
    intro v hvS _ a b hab α' β' hN τ' hτ' hτ'1 τ'' hτ'' hτ''1 J J' hJ hJ'
    exact AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified K L hdeg σ.symm hσne v
      (fun w hw => hS w (hw ▸ hvS)) a b hab α' β' hN τ' hτ' hτ'1 τ'' hτ'' hτ''1 J J' hJ hJ'
  have hSLF' : AutomorphicForm.IsSemiLocalFactorization K L (SK ∪ T) φL φa φf (fun v => if v ∈ T then φT v else φS v) := hSLF

  have huKt : ∀ t ∈ SL, ((nK t : Matrix (Fin 2) (Fin 2) K) 0 0 / (nK t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 0 := by
    intro t ht
    obtain ⟨h0, h1⟩ := H5ASMw47.det_diag_ne_w47 (nK t) (hnKgood t (hSL ht)).1.1
    exact div_ne_zero h0 h1
  have hdKt : ∀ t ∈ SL, (nK t : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 :=
    fun t ht => (H5ASMw47.det_diag_ne_w47 (nK t) (hnKgood t (hSL ht)).1.1).2
  let uKg : GL (Fin 2) K → Kˣ := fun γ =>
    if h : ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 0 then Units.mk0 _ h else 1
  let dKg : GL (Fin 2) K → Kˣ := fun γ =>
    if h : (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 then Units.mk0 _ h else 1
  let uKf : GL (Fin 2) L → Kˣ := fun t => uKg (nK t)
  let dKf : GL (Fin 2) L → Kˣ := fun t => dKg (nK t)
  have huKf : ∀ t ∈ SL, (uKf t : K) = (nK t : Matrix (Fin 2) (Fin 2) K) 0 0 / (nK t : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro t ht; simp only [uKf, uKg, dif_pos (huKt t ht), Units.val_mk0]
  have hdKf : ∀ t ∈ SL, (dKf t : K) = (nK t : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro t ht; simp only [dKf, dKg, dif_pos (hdKt t ht), Units.val_mk0]
  have hwin := fun (t : GL (Fin 2) L) (ht : t ∈ SL) (w : (AdeleRing (𝓞 L) L)ˣ) => by
    have htΔ := hSL ht
    obtain ⟨hn10, hn01, hn00, hn11⟩ := (hnK t htΔ).2
    exact AutomorphicForm.twistedWeightedClassIntegral_eq_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_of_coupled_of_isSemiLocalFactorization
      K L σ.symm hgen νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS hmatchA hmatchS fT hfT hmatchT' hunit F ffF hFUF
      (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
      (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
      (AutomorphicForm.archHaarL K L) rfl rfl
      (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
      (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
      JA' hJA' hJA'0 JF' hJF' hJF'0 IT hIT IU hIU
      (nK t) ⟨(hnKgood t htΔ).1.1, (hnKgood t htΔ).1.2, (hnKgood t htΔ).2⟩
      ⟨⟨(t : Matrix (Fin 2) (Fin 2) L) 0 0, hn00.symm⟩, ⟨(t : Matrix (Fin 2) (Fin 2) L) 1 1, hn11.symm⟩⟩
      (uKf t) (dKf t) (huKf t ht) (hdKf t ht)
      (τK (nK t)) (hτK (nK t)) (hτKc (nK t) (hnKgood t htΔ)) cL cT hcK hcL hcT
      δL τGL τAL τFL hδL hδLA hδLF hτGL hτGLc hτGLcpl hτAL hτALc hτFL hτFL1 hτFLc hTL
      μ hμ 1 one_pos hμc hG' φT hφT hmatchTφ hJT hunitW φL φf hSLF' t (hΔd t htΔ) ⟨hn00, hn11⟩ (δ t)
      (hδgood t ⟨⟨(hΔd t htΔ).1, (hΔd t htΔ).2.1⟩, (hΔd t htΔ).2.2⟩) (τ t) (hτ t) (hτc t) w (JL t w) (hJL t htΔ w)
      (JKF (nK t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w))
      ((OCW (nK t) (hnKgood t htΔ)).1 _)

  have hNopen : IsOpen (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)) := by
    have h := NumberField.isOpen_range_idelicNorm K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L)
    rwa [MonoidHom.coe_range] at h
  have hNmeas : MeasurableSet (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)) := hNopen.measurableSet
  let Win : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun t w =>
    (∏ v ∈ T, IT (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) v) *
      (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) v) *
      ((JA' (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) - (Module.finrank K L : ℂ) * JA (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t)))) * ∏ v ∈ SK, IF (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) v +
        IA (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) * ∑ v ∈ SK, (JF' (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) v - (Module.finrank K L : ℂ) * JF (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) v) *
          ∏ v' ∈ SK.erase v, IF (uKf t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKf t))) v')
  let JKc : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun γ z =>
    if γ ∈ SL.image nK then (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)).indicator (JKF γ) z else 0
  have hJKFm : ∀ γ ∈ SKf, Measurable (JKF γ) := by
    intro γ hγ
    have hγg := goodK_of_mem γ (hSKf hγ)
    refine Finset.measurable_sum _ (fun m hm => ?_)
    exact (measurable_const.mul ((OCW γ hγg).2 m hm))
  have hJKcm : ∀ γ ∈ SKf, Measurable (JKc γ) := by
    intro γ hγ
    by_cases h : γ ∈ SL.image nK
    · simp only [JKc, if_pos h]
      exact (hJKFm γ hγ).indicator hNmeas
    · simp only [JKc, if_neg h]
      exact measurable_const
  have hJKFi : ∀ γ ∈ SKf, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z) νZK := by
    intro γ hγ ξ hξ
    have h : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z) =
        fun z => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK m γ z) := by
      funext z
      simp only [JKF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [h]
    refine integrable_finsetSum _ fun m hm => Integrable.const_mul ?_ _
    have hsub : Δf ξ m ⊆ SKf := by
      intro γ' hγ'
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨(ξ, m), Finset.mem_product.mpr ⟨hξ, hm⟩, hγ'⟩))))))
    have hΔfeq : Δf ξ m = (KC ξ hξ m hm).choose := by simp only [Δf, dif_pos (And.intro hξ hm)]
    exact ((KC ξ hξ m hm).choose_spec.2 SKf (hΔfeq ▸ hsub) hSKf).2.1 γ hγ
  have hJKci : ∀ γ ∈ SKf, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z) νZK := by
    intro γ hγ ξ hξ
    by_cases h : γ ∈ SL.image nK
    · have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z) =
          (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)).indicator
            (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z) := by
        funext z
        simp only [JKc, if_pos h, Set.indicator_apply]
        split_ifs <;> simp
      rw [this]
      exact (hJKFi γ hγ ξ hξ).indicator hNmeas
    · have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z) = fun _ => 0 := by
        funext z; simp only [JKc, if_neg h, mul_zero]
      rw [this]
      exact integrable_zero _ _ _
  have hJKc0 : ∀ γ ∈ SKf, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ) → JKc γ z = 0 := by
    intro γ _ z hz
    by_cases h : γ ∈ SL.image nK
    · simp only [JKc, if_pos h, Set.indicator_of_notMem hz]
    · simp only [JKc, if_neg h]
  have hvanc : ∀ γ ∈ SKf, (∀ t ∈ SL, nK t ≠ γ) →
      ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z ∂νZK = 0 := by
    intro γ _ hnot
    have h : γ ∉ SL.image nK := by
      intro hm
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
      exact hnot t ht rfl
    simp only [JKc, if_neg h, mul_zero, integral_zero, Finset.sum_const_zero]
  have hρ : (cL * cT) / (cK * cT) = (c₀' : ℝ) := by
    rw [hc₀'v]
    field_simp
  have hwinc : ∀ t ∈ SL, ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      JL t w = (Module.finrank K L : ℂ) * (((cL * cT) / (cK * cT) : ℝ) : ℂ) * JKc (nK t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) +
        ((cL * cT⁻¹ : ℝ) : ℂ) * Win t w := by
    intro t ht w
    have hmem : nK t ∈ SL.image nK := Finset.mem_image_of_mem nK ht
    have hval : JKc (nK t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) = JKF (nK t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) := by
      simp only [JKc, if_pos hmem, Set.indicator_of_mem (Set.mem_range_self w)]
    rw [hval]
    exact hwin t ht w
  have C4C := AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add
    K L νZL νZK N1 hN1c hN1 μN Cfib hCfib hCl hCi ξL hξc Ξ hΞ hΞne SL SKf nK hnSL hninjSL hnr JL JKc Win
    (hLCS SL Finset.subset_union_left hSL).2.1 hJKcm hJKci hJKc0 cK cT cL cT hcK hcT hcL hcT c₀' hρ hwinc hvanc
    κ₀ (cN * cτ / (cH * 1)) κ₀K (cτK / cHK) hκ₀Kpos (div_pos hcτK hcHK)

  let WKg : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun γ z =>
    (∏ v ∈ T, IT (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) v) *
      (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) v) *
      ((JA' (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) - (Module.finrank K L : ℂ) * JA (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ)))) * ∏ v ∈ SK, IF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) v +
        IA (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) * ∑ v ∈ SK, (JF' (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) v - (Module.finrank K L : ℂ) * JF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) v) *
          ∏ v' ∈ SK.erase v, IF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) v')
  have hWinWK : ∀ t (w : (AdeleRing (𝓞 L) L)ˣ), Win t w = WKg (nK t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) := fun _ _ => rfl
  have huKg1 : ∀ γ ∈ SKf, ((uKg γ : Kˣ) : K) ≠ 1 := by
    intro γ hγ
    have hg := goodK_of_mem γ (hSKf hγ)
    obtain ⟨h0, h1⟩ := H5ASMw47.det_diag_ne_w47 γ hg.1.1
    simp only [uKg, dif_pos (div_ne_zero h0 h1), Units.val_mk0]
    exact hg.2
  have FMEAS := AutomorphicForm.measurable_window_values_of_ne_one_of_prime
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS hmatchA hmatchS fT hfT hmatchT' hunit F ffF hFUF
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 IT hIT IU hIU
  have WMEAS : ∀ γ ∈ SKf, Measurable (WKg γ) := by
    intro γ hγ
    obtain ⟨mIA, mJA, mJA', mF, mT, mU⟩ := FMEAS (uKg γ) (huKg1 γ hγ)
    have hlc := (WFFT.1 (uKg γ) (huKg1 γ hγ)).1

    have hsh : Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dKg γ))) :=
      measurable_mul_const _
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact Finset.measurable_prod _ (fun v hv => (mT v hv).comp hsh)
    · exact (hlc.continuous.measurable).comp hsh
    · refine Measurable.add ?_ ?_
      · refine Measurable.mul (Measurable.sub (mJA'.comp hsh) (measurable_const.mul (mJA.comp hsh))) ?_
        exact Finset.measurable_prod _ (fun v hv => ((mF v hv).1).comp hsh)
      · refine Measurable.mul (mIA.comp hsh) (Finset.measurable_sum _ (fun v hv => ?_))
        refine Measurable.mul (Measurable.sub (((mF v hv).2.2).comp hsh) (measurable_const.mul (((mF v hv).2.1).comp hsh))) ?_
        exact Finset.measurable_prod _ (fun v' hv' => ((mF v' (Finset.mem_of_mem_erase hv')).1).comp hsh)
  have WINT : ∀ γ ∈ SKf, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z) νZK := by
    intro γ hγ ξ hξ
    exact (WFFT.1 (uKg γ) (huKg1 γ hγ)).2 _ ξ ((hΞ ξ).1 hξ).1
  let IKw : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun γ z =>
    if γ ∈ SL.image nK then (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)).indicator
      (fun z => ((c₀' : ℝ) : ℂ)⁻¹ * WKg γ z) z else 0
  have hc₀'ne : ((c₀' : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (c₀' : ℝ) := div_pos hcL hcK
    exact_mod_cast this.ne'
  have hIKwm : ∀ γ ∈ SKf, Measurable (IKw γ) := by
    intro γ hγ
    by_cases h : γ ∈ SL.image nK
    · simp only [IKw, if_pos h]
      exact ((measurable_const.mul (WMEAS γ hγ))).indicator hNmeas
    · simp only [IKw, if_neg h]
      exact measurable_const
  have hIKwi : ∀ γ ∈ SKf, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z) νZK := by
    intro γ hγ ξ hξ
    by_cases h : γ ∈ SL.image nK
    · have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z) =
          (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)).indicator
            (fun z => ((c₀' : ℝ) : ℂ)⁻¹ * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z)) := by
        funext z
        simp only [IKw, if_pos h, Set.indicator_apply]
        split_ifs <;> ring
      rw [this]
      exact ((WINT γ hγ ξ hξ).const_mul _).indicator hNmeas
    · have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z) = fun _ => 0 := by
        funext z; simp only [IKw, if_neg h, mul_zero]
      rw [this]
      exact integrable_zero _ _ _
  have hIKw0 : ∀ γ ∈ SKf, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ) → IKw γ z = 0 := by
    intro γ _ z hz
    by_cases h : γ ∈ SL.image nK
    · simp only [IKw, if_pos h, Set.indicator_of_notMem hz]
    · simp only [IKw, if_neg h]
  have hvanw : ∀ γ ∈ SKf, (∀ t ∈ SL, nK t ≠ γ) →
      ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z ∂νZK = 0 := by
    intro γ _ hnot
    have h : γ ∉ SL.image nK := by
      intro hm
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
      exact hnot t ht rfl
    simp only [IKw, if_neg h, mul_zero, integral_zero, Finset.sum_const_zero]
  have hmatchw : ∀ t ∈ SL, ∀ w : (AdeleRing (𝓞 L) L)ˣ, Win t w = (c₀' : ℂ) * IKw (nK t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) := by
    intro t ht w
    have hmem : nK t ∈ SL.image nK := Finset.mem_image_of_mem nK ht
    rw [hWinWK]
    simp only [IKw, if_pos hmem, Set.indicator_of_mem (Set.mem_range_self w)]
    rw [← mul_assoc]
    have : (c₀' : ℂ) * ((c₀' : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hc₀'ne
    rw [this, one_mul]
  have C3W := AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm
    K L νZL νZK N1 hN1c hN1 μN Cfib hCfib hCl hCi ξL hξc Ξ hΞ hΞne SL SKf nK hnSL hninjSL hnr Win IKw hIKwm hIKwi hIKw0 c₀'
    hmatchw hvanw κ₀ (cN * cτ / (cH * 1)) κ₀K (cτK / cHK) hκ₀Kpos (div_pos hcτK hcHK)

  let Hc : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun γ z =>
    (Module.finrank K L : ℂ) * (((cL * cT) / (cK * cT) : ℝ) : ℂ) * JKF γ z + ((cL * cT⁻¹ : ℝ) : ℂ) * WKg γ z
  have hgoodSKf : ∀ γ ∈ SKf, ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro γ hγ
    obtain ⟨h0, h1⟩ := H5ASMw47.det_diag_ne_w47 γ (goodK_of_mem γ (hSKf hγ)).1.1
    exact ⟨div_ne_zero h0 h1, h1⟩
  have huKg : ∀ γ ∈ SKf, (uKg γ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro γ hγ; simp only [uKg, dif_pos (hgoodSKf γ hγ).1, Units.val_mk0]
  have hdKg : ∀ γ ∈ SKf, (dKg γ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro γ hγ; simp only [dKg, dif_pos (hgoodSKf γ hγ).2, Units.val_mk0]
  have WC : ∀ γ ∈ SKf, γ ∈ SL.image nK → ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊔ ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm).range :
        Subgroup (AdeleRing (𝓞 K) K)ˣ) → z ∉ (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)) → Hc γ z = 0 := by
    intro γ hγ hhit z hzK hzN
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hhit
    have htΔ := hSL ht
    obtain ⟨hn10, hn01, hn00, hn11⟩ := (hnK t htΔ).2
    have hg := goodK_of_mem (nK t) (hSKf hγ)
    exact AutomorphicForm.finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_eq_zero_of_mem_sup_of_not_mem_range_of_prime
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS hmatchA hmatchS fT hfT hmatchT' hunit F ffF hFUF
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 IT hIT IU hIU
        (nK t) ⟨hg.1.1, hg.1.2, hg.2⟩
        ⟨⟨(t : Matrix (Fin 2) (Fin 2) L) 0 0, hn00.symm⟩, ⟨(t : Matrix (Fin 2) (Fin 2) L) 1 1, hn11.symm⟩⟩
        (uKg (nK t)) (dKg (nK t)) (huKg _ hγ) (hdKg _ hγ)
        (τK (nK t)) (hτK (nK t)) (hτKc (nK t) hg) cL cT hcK hcL hcT z hzK hzN (JKF (nK t) z) ((OCW (nK t) hg).1 z)
  have NC : ∀ γ ∈ SKf, γ ∉ SL.image nK → ∀ z : (AdeleRing (𝓞 K) K)ˣ, Hc γ z = 0 := by
    intro γ hγ hmissed z
    have hg := goodK_of_mem γ (hSKf hγ)
    have hnn : (uKg γ : K) ∉ Set.range (Algebra.norm K : L → K) := by
      rw [huKg γ hγ]
      exact hmiss γ hγ (fun t ht heq => hmissed (Finset.mem_image.mpr ⟨t, ht, heq⟩))
    exact AutomorphicForm.finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_eq_zero_of_ratio_not_mem_range_norm_of_prime
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS hmatchA hmatchS fT hfT hmatchT' hunit F ffF hFUF
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 IT hIT IU hIU
        γ ⟨hg.1.1, hg.1.2, hg.2⟩ (uKg γ) (dKg γ) (huKg _ hγ) (hdKg _ hγ) hnn
        (τK γ) (hτK γ) (hτKc γ hg) cL cT hcK hcL hcT z (JKF γ z) ((OCW γ hg).1 z)
  have UNTR : ∀ γ ∈ SKf,
      ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((Module.finrank K L : ℂ) * (c₀' : ℂ) * JKc γ z + ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℂ) * IKw γ z)) ∂νZK =
        ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z ∂νZK := by
    intro γ hγ
    have hρc : (((cL * cT) / (cK * cT) : ℝ) : ℂ) = ((c₀' : ℝ) : ℂ) := by exact_mod_cast hρ
    have hcc : (c₀' : ℂ) = ((c₀' : ℝ) : ℂ) := rfl
    by_cases hhit : γ ∈ SL.image nK
    swap
    ·
      have hL : ∀ ξ ∈ Ξ, (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((Module.finrank K L : ℂ) * (c₀' : ℂ) * JKc γ z + ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℂ) * IKw γ z))) = fun _ => 0 := by
        intro ξ _; funext z; simp only [JKc, IKw, if_neg hhit, mul_zero, add_zero]
      have hR : ∀ ξ ∈ Ξ, (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) = fun _ => 0 := by
        intro ξ _; funext z; rw [NC γ hγ hhit z, mul_zero]
      have eL : ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((Module.finrank K L : ℂ) * (c₀' : ℂ) * JKc γ z + ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℂ) * IKw γ z)) ∂νZK = 0 :=
        Finset.sum_eq_zero fun ξ hξ => by rw [hL ξ hξ, integral_zero]
      have eR : ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z ∂νZK = 0 :=
        Finset.sum_eq_zero fun ξ hξ => by rw [hR ξ hξ, integral_zero]
      rw [eL, eR]

    let KN : Subgroup (AdeleRing (𝓞 K) K)ˣ := M4aHerbrand.principalIdeles (𝓞 K) K ⊔ ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm).range
    have hKNopen : IsOpen (KN : Set (AdeleRing (𝓞 K) K)ˣ) := by
      apply Subgroup.isOpen_mono (le_sup_right : ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm).range ≤ KN)
      have h := NumberField.isOpen_range_idelicNorm K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L)
      exact h
    have hKNmeas : MeasurableSet ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ) := hKNopen.measurableSet.compl
    have hNsub : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ)) → z ∈ (KN : Set (AdeleRing (𝓞 K) K)ˣ) := by
      intro z hz
      obtain ⟨w, rfl⟩ := hz
      exact (le_sup_right : ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm).range ≤ KN) ⟨w, rfl⟩
    have hHci : ∀ ξ ∈ Ξ, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) νZK := by
      intro ξ hξ
      have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) =
          fun z => (Module.finrank K L : ℂ) * (((cL * cT) / (cK * cT) : ℝ) : ℂ) * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z) +
            ((cL * cT⁻¹ : ℝ) : ℂ) * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z) := by
        funext z; simp only [Hc]; ring
      rw [this]
      exact ((hJKFi γ hγ ξ hξ).const_mul _).add ((WINT γ hγ ξ hξ).const_mul _)

    have hpt : ∀ ξ ∈ Ξ, (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((Module.finrank K L : ℂ) * (c₀' : ℂ) * JKc γ z + ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℂ) * IKw γ z))) =
        fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z - ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ).indicator (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) z := by
      intro ξ hξ
      funext z
      by_cases hzN : z ∈ (Set.range ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ))
      · have hzKN : z ∉ ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ) := fun h => h (hNsub z hzN)
        rw [Set.indicator_of_notMem hzKN, sub_zero]
        simp only [JKc, IKw, if_pos hhit, Set.indicator_of_mem hzN, Hc]
        rw [hρc, ← hcc]
        have hc0 : (c₀' : ℂ) ≠ 0 := by rw [hcc]; exact hc₀'ne
        field_simp
      · have h0J : JKc γ z = 0 := by simp only [JKc, if_pos hhit, Set.indicator_of_notMem hzN]
        have h0I : IKw γ z = 0 := by simp only [IKw, if_pos hhit, Set.indicator_of_notMem hzN]
        rw [h0J, h0I]
        by_cases hzK : z ∈ (KN : Set (AdeleRing (𝓞 K) K)ˣ)
        · have hzKN : z ∉ ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ) := fun h => h hzK
          rw [Set.indicator_of_notMem hzKN, WC γ hγ hhit z hzK hzN]
          simp
        · rw [Set.indicator_of_mem (Set.mem_compl hzK)]
          simp
    rw [Finset.sum_congr rfl (fun ξ hξ => by rw [hpt ξ hξ])]
    have hsplit : ∀ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z -
          ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ).indicator (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) z) ∂νZK =
        (∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z ∂νZK) -
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ).indicator (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) z ∂νZK := by
      intro ξ hξ
      exact integral_sub (hHci ξ hξ) ((hHci ξ hξ).indicator hKNmeas)
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]

    have hXI := (NumberField.sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
      K L ξL Ξ hΞ).1
    have hzero : ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ,
        ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ).indicator (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) z ∂νZK = 0 := by
      rw [← integral_finsetSum _ (fun ξ hξ => (hHci ξ hξ).indicator hKNmeas)]
      have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ∑ ξ ∈ Ξ,
          ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ).indicator (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) z) = fun _ => 0 := by
        funext z
        by_cases hzK : z ∈ (KN : Set (AdeleRing (𝓞 K) K)ˣ)
        · have hzKN : z ∉ ((KN : Set (AdeleRing (𝓞 K) K)ˣ)ᶜ) := fun h => h hzK
          simp only [Set.indicator_of_notMem hzKN, Finset.sum_const_zero]
        · simp only [Set.indicator_of_mem (Set.mem_compl hzK), ← Finset.sum_mul]
          rw [hXI z hzK, zero_mul]
      rw [this, integral_zero]
    rw [hzero, sub_zero]

  have hε : ∀ r : K, Algebra.norm K r = r := fun r => by
    simp only [Algebra.norm_self, MonoidHom.id_apply]
  have BKSWAP : ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        SatakeCombination.slotFamilyCoeff K L ws ks js T m * BKc ξK m =
      ∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z ∂νZK) := by
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    have hlin : ∀ γ ∈ SKf, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z ∂νZK =
        ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK m γ z ∂νZK := by
      intro γ hγ
      have h : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z) =
          fun z => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK m γ z) := by
        funext z
        simp only [JKF, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
      have hint : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK m γ z) νZK := by
        intro m hm
        have hsub : Δf ξ m ⊆ SKf := by
          intro γ' hγ'
          refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨(ξ, m), Finset.mem_product.mpr ⟨hξ, hm⟩, hγ'⟩))))))
        have hΔfeq : Δf ξ m = (KC ξ hξ m hm).choose := by simp only [Δf, dif_pos (And.intro hξ hm)]
        exact ((KC ξ hξ m hm).choose_spec.2 SKf (hΔfeq ▸ hsub) hSKf).2.1 γ hγ
      rw [h, integral_finsetSum _ (fun m hm => (hint m hm).const_mul _)]
      refine Finset.sum_congr rfl fun m _ => ?_
      exact integral_const_mul _ _
    calc ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * BKc ξ m
        = ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            ∑ t ∈ SKf, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK m t z ∂νZK) :=
          Finset.sum_congr rfl fun m hm => by rw [hBK ξ hξ m hm]
      _ = ∑ γ ∈ SKf, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            (((κ₀K : ℂ) * (if Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK m γ z ∂νZK)) := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun γ hγ => ?_
          rw [hlin γ hγ, hε, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring

  have PERG : ∀ γ ∈ SKf,
      (Module.finrank K L : ℂ) * (∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z ∂νZK) +
        ((cL * cT⁻¹ : ℝ) : ℂ) * (∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z ∂νZK) =
      (Module.finrank K L : ℂ) * (∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z ∂νZK) +
        ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℝ) : ℂ)⁻¹ * (∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z ∂νZK) := by
    intro γ hγ
    have hU := UNTR γ hγ
    have hρc : (((cL * cT) / (cK * cT) : ℝ) : ℂ) = ((c₀' : ℝ) : ℂ) := by exact_mod_cast hρ

    have hL : ∀ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((Module.finrank K L : ℂ) * (c₀' : ℂ) * JKc γ z + ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℂ) * IKw γ z)) ∂νZK =
        (Module.finrank K L : ℂ) * (c₀' : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z ∂νZK +
          ((cL * cT⁻¹ : ℝ) : ℂ) * (c₀' : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z ∂νZK := by
      intro ξ hξ
      have h1 := hJKci γ hγ ξ hξ
      have h2 := hIKwi γ hγ ξ hξ
      have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((Module.finrank K L : ℂ) * (c₀' : ℂ) * JKc γ z + ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℂ) * IKw γ z))) =
          fun z => (Module.finrank K L : ℂ) * (c₀' : ℂ) * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z) +
            ((cL * cT⁻¹ : ℝ) : ℂ) * (c₀' : ℂ) * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z) := by
        funext z; ring
      rw [this, integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
    have hR : ∀ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z ∂νZK =
        (Module.finrank K L : ℂ) * ((c₀' : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z ∂νZK +
          ((cL * cT⁻¹ : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z ∂νZK := by
      intro ξ hξ
      have h1 := hJKFi γ hγ ξ hξ
      have h2 := WINT γ hγ ξ hξ
      have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Hc γ z) =
          fun z => (Module.finrank K L : ℂ) * ((c₀' : ℝ) : ℂ) * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z) +
            ((cL * cT⁻¹ : ℝ) : ℂ) * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z) := by
        funext z; simp only [Hc]; rw [hρc]; ring
      rw [this, integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at hU
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hU
    have hc0 : ((c₀' : ℝ) : ℂ) ≠ 0 := hc₀'ne
    have hcc : (c₀' : ℂ) = ((c₀' : ℝ) : ℂ) := rfl
    rw [hcc] at hU

    have hinv : ((c₀' : ℝ) : ℂ) * ((c₀' : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hc0
    apply mul_left_cancel₀ hc0
    linear_combination hU - (((cL * cT⁻¹ : ℝ) : ℂ) * ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z ∂νZK) * hinv

  have hswap : ∀ X : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ,
      (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * X γ z ∂νZK)) = ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * (((cτK / cHK : ℝ)) : ℂ) * (∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * X γ z ∂νZK) := by
    intro X
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    ring
  have COMB : (Module.finrank K L : ℂ) * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z ∂νZK)) + ((cL * cT⁻¹ : ℝ) : ℂ) * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z ∂νZK)) =
      (Module.finrank K L : ℂ) * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKF γ z ∂νZK)) + ((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℝ) : ℂ)⁻¹ * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z ∂νZK)) := by
    rw [hswap JKc, hswap IKw, hswap JKF, hswap WKg, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have h := PERG γ hγ
    linear_combination (((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * (((cτK / cHK : ℝ)) : ℂ)) * h
  have C3W' : (∑ t ∈ SL, ((κ₀ : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
            then (1 / 2 : ℂ) else 1)) *
          ((((cN * cτ / (cH * 1)) : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * Win t wq.out ∂(HaarQuotient.measure νZL N1 μN))) =
      ((((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ)))) * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z ∂νZK)) := by
    have h := C3W
    simp only [show ∀ (a b : ℂ), 2 * a * b = 2 * (a * b) from fun a b => by ring, ← Finset.mul_sum] at h
    linear_combination (1 / 2 : ℂ) * h
  have EQ1 : BLc = (Module.finrank K L : ℂ) * ((((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ)))) * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JKc γ z ∂νZK)) +
      ((cL * cT⁻¹ : ℝ) : ℂ) * (((((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ)))) * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IKw γ z ∂νZK))) := by
    have h := hBL.trans C4C
    rw [C3W'] at h
    exact h
  have hlamdef : lam = ((((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ)))) := rfl
  have I8 : ((((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ)))) * (((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℝ) : ℂ)⁻¹ * (∑ ξ ∈ Ξ, ∑ γ ∈ SKf, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) * ((((cτK / cHK : ℝ)) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z ∂νZK))) =
      ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * ℬ.coeff n := by

    let Wprod : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun u z => ((∏ v ∈ T, IT u z v) *
        (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u z v) *
        ((JA' u z - (Module.finrank K L : ℂ) * JA u z) * ∏ v ∈ SK, IF u z v +
          IA u z * ∑ v ∈ SK, (JF' u z v - (Module.finrank K L : ℂ) * JF u z v) *
            ∏ v' ∈ SK.erase v, IF u z v'))
    have hWKgW : ∀ γ (z : (AdeleRing (𝓞 K) K)ˣ), WKg γ z = Wprod (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) := fun _ _ => rfl
    let G : Kˣ → ℂ := fun u => ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wprod u z ∂νZK

    have TRANS : ∀ ξ ∈ Ξ, ∀ (u d : Kˣ),
        ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wprod u (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) d) ∂νZK =
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wprod u z ∂νZK := by
      intro ξ hξ u d
      obtain ⟨-, hprin, -⟩ := (hΞ ξ).1 hξ
      have h1 : ξ ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) d, Subgroup.mem_top _⟩ = 1 := hprin _ ⟨d, rfl⟩
      have key : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wprod u (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) d)) =
          fun z => (fun x : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ) * Wprod u x) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) d) := by
        funext z
        simp only
        congr 1
        have : (⟨z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) d, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
            ⟨z, Subgroup.mem_top z⟩ * ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) d, Subgroup.mem_top _⟩ := rfl
        rw [this, map_mul, h1, mul_one]
      rw [key]
      exact MeasureTheory.integral_mul_right_eq_self (μ := νZK) (fun x : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ) * Wprod u x) _

    let A : Finset Kˣ := SKf.image uKg
    let R : Finset Kˣ := A ∪ A.image (fun u => u⁻¹)
    let Dg : Kˣ → GL (Fin 2) K := fun u => LanglandsTunnell.CubicInduction.diagUnits2 u 1
    let ΔKpd : Finset (GL (Fin 2) K) := R.image Dg
    have hDg_rat : ∀ u : Kˣ, ((Dg u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 / ((Dg u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K) := by
      intro u; simp [Dg, LanglandsTunnell.CubicInduction.diagUnits2]
    have hDg_10 : ∀ u : Kˣ, ((Dg u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      intro u; simp [Dg, LanglandsTunnell.CubicInduction.diagUnits2]
    have hDg_01 : ∀ u : Kˣ, ((Dg u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      intro u; simp [Dg, LanglandsTunnell.CubicInduction.diagUnits2]
    have hDg_11 : ∀ u : Kˣ, ((Dg u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      intro u; simp [Dg, LanglandsTunnell.CubicInduction.diagUnits2]
    have hR1 : ∀ u ∈ R, (u : K) ≠ 1 := by
      intro u hu
      rcases Finset.mem_union.mp hu with h | h
      · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp h
        exact huKg1 γ hγ
      · obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp h
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hu'
        intro h1
        apply huKg1 γ hγ
        have : ((uKg γ)⁻¹ : Kˣ) = 1 := Units.ext h1
        simpa using this
    have RSEP := (AutomorphicForm.exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps K hgenK ΔK hΔKd hΔKdisj hΔKcov).2
    have huKg_of : ∀ γ : GL (Fin 2) K, ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 0 → ((uKg γ : Kˣ) : K) = ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) := by
      intro γ h; simp only [uKg, dif_pos h, Units.val_mk0]
    have hdKg_of : ∀ γ : GL (Fin 2) K, (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 → ((dKg γ : Kˣ) : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      intro γ h; simp only [dKg, dif_pos h, Units.val_mk0]
    have hΔKpd_d : ∀ γ ∈ ΔKpd, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1 := by
      intro γ hγ
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hγ
      exact ⟨hDg_10 u, hDg_01 u, by rw [hDg_rat]; exact hR1 u hu⟩
    have hΔKpd_inj : ∀ γ ∈ ΔKpd, ∀ γ' ∈ ΔKpd, ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) = ((γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1) → γ = γ' := by
      intro γ hγ γ' hγ' h
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hγ
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hγ'
      rw [hDg_rat, hDg_rat] at h
      rw [Units.ext h]
    have huKpd : ∀ γ ∈ ΔKpd, ((uKg γ : Kˣ) : K) = ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) := by
      intro γ hγ
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hγ
      exact huKg_of _ (by rw [hDg_rat]; exact u.ne_zero)
    have hdKpd : ∀ γ ∈ ΔKpd, ((dKg γ : Kˣ) : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      intro γ hγ
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hγ
      exact hdKg_of _ (by rw [hDg_11]; exact one_ne_zero)
    have huKDg : ∀ u : Kˣ, uKg (Dg u) = u := fun u => Units.ext (by rw [huKg_of _ (by rw [hDg_rat]; exact u.ne_zero), hDg_rat])
    have hdKDg : ∀ u : Kˣ, dKg (Dg u) = 1 := fun u => Units.ext (by rw [hdKg_of _ (by rw [hDg_11]; exact one_ne_zero), hDg_11]; rfl)
    let WKm : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ :=
      fun m γ z => ((∏ v ∈ T, IW m (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v) *
        (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v) *
        ((JA' (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) - (Module.finrank K L : ℂ) * JA (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ))) * ∏ v ∈ SK, IF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v +
          IA (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) * ∑ v ∈ SK, (JF' (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v - (Module.finrank K L : ℂ) * JF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v) *
            ∏ v' ∈ SK.erase v, IF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v'))
    have hΔKc' : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ u : Kˣ, (u : K) ≠ 1 →
        (∀ γ ∈ ΔKpd, ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ (u : K)) → ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((∏ v ∈ T, IW m u z v) *
        (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u z v) *
        ((JA' u z - (Module.finrank K L : ℂ) * JA u z) * ∏ v ∈ SK, IF u z v +
          IA u z * ∑ v ∈ SK, (JF' u z v - (Module.finrank K L : ℂ) * JF u z v) *
            ∏ v' ∈ SK.erase v, IF u z v')) = 0 := by
      intro m hm u hu hnot z
      refine hUm m hm u ?_ hu z
      intro huU
      have hUall : u ∈ Uall := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m, hm, huU⟩)
      have hrepu : (hΔKrat u hu).choose ∈ SKf := by
        refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, hUall, ?_⟩))
        simp only [rep, dif_pos hu, Finset.mem_singleton]
      have hγ₀ := (hΔKrat u hu).choose_spec
      have hu0 : uKg (hΔKrat u hu).choose ∈ A := Finset.mem_image_of_mem _ hrepu
      have hratio := huKg _ hrepu
      rcases hγ₀.2 with h | h
      · have he : uKg (hΔKrat u hu).choose = u := Units.ext (hratio.trans h)
        rw [he] at hu0
        exact hnot (Dg u) (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hu0)) (hDg_rat u)
      · have he : uKg (hΔKrat u hu).choose = u⁻¹ := Units.ext (by rw [hratio, h, Units.val_inv_eq_inv_val])
        rw [he] at hu0
        have : u ∈ R := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u⁻¹, hu0, inv_inv u⟩)
        exact hnot (Dg u) (Finset.mem_image_of_mem _ this) (hDg_rat u)
    have HPD := hPD ks js ΔKpd hΔKpd_d hΔKpd_inj IW hIW IU hIU uKg dKg huKpd hdKpd WKm (fun m _ γ _ z => rfl) hΔKc'

    have hupd1 : ∀ γ ∈ ΔKpd, ((uKg γ : Kˣ) : K) ≠ 1 := fun γ hγ => by rw [huKpd γ hγ]; exact (hΔKpd_d γ hγ).2.2
    have hIntm : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ γ ∈ ΔKpd, ∀ ξ ∈ Ξ,
        Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKm m γ z) νZK := by
      intro m hm γ hγ ξ hξ
      exact ((WFFm m hm).1 (uKg γ) (hupd1 γ hγ)).2 _ ξ ((hΞ ξ).1 hξ).1

    have SLOT : ∀ (u : Kˣ) (hu : (u : K) ≠ 1) (z' : (AdeleRing (𝓞 K) K)ˣ),
        ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∏ v ∈ T, IW m u z' v = ∏ v ∈ T, IT u z' v := by
      intro u hu z'
      have hIT' : ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z' v)
          (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
              (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
                  (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
                ∑ ι : Fin (r 0) → Fin (nKs v),
                  (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                    (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) (IT u z' v) := by
        intro v hv
        have h := hIT u z' hu v hv
        have e1 : (fT v) = fun x => ∑ e ∈ (SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
            (SatakeCombination.slotCoeff K L ws v (ks v) (js v) e : ℂ) *
              ∑ ι : Fin (e 0) → Fin (nKs v),
                (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (e 1))⁻¹ * x) := by
          funext x; simp only [fT, dif_pos hv]
        rw [e1] at h
        exact h
      exact AutomorphicForm.sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
        K L ws T nKs rKs zKs ks js (fun v => AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (fun v _ => AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one K u hu z' v)
        (fun v => τF u z' v) (fun v _ => hτF u z' v hu) (fun v _ => hτF1 u z' v hu)
        (fun m v => IW m u z' v) (fun m hm v hv => hIW m hm u z' hu v hv) (fun v => IT u z' v) hIT'
    have SLOTW : ∀ γ ∈ ΔKpd, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * WKm m γ z =
          Wprod (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) := by
      intro γ hγ z
      have key : ∀ m, SatakeCombination.slotFamilyCoeff K L ws ks js T m * WKm m γ z =
          (SatakeCombination.slotFamilyCoeff K L ws ks js T m * ∏ v ∈ T, IW m (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v) *
            ((∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v) *
        ((JA' (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) - (Module.finrank K L : ℂ) * JA (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ))) * ∏ v ∈ SK, IF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v +
          IA (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) * ∑ v ∈ SK, (JF' (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v - (Module.finrank K L : ℂ) * JF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v) *
            ∏ v' ∈ SK.erase v, IF (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) v')) := by
        intro m; simp only [WKm]; ring
      rw [Finset.sum_congr rfl (fun m _ => key m), ← Finset.sum_mul, SLOT (uKg γ) (hupd1 γ hγ)]
      simp only [Wprod]; ring

    have SUMPD : ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔKpd, ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKm m γ z ∂νZK = ∑ u ∈ R, G u := by
      have step1 : ∀ γ ∈ ΔKpd, ∀ ξ ∈ Ξ,
          ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKm m γ z ∂νZK =
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wprod (uKg γ) z ∂νZK := by
        intro γ hγ ξ hξ
        have hpt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
            ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKm m γ z) =
              ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wprod (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) := by
          intro z
          rw [← SLOTW γ hγ z, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun m _ => by ring)
        calc _ = ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
              ∫ z : (AdeleRing (𝓞 K) K)ˣ, SatakeCombination.slotFamilyCoeff K L ws ks js T m * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKm m γ z) ∂νZK :=
              Finset.sum_congr rfl (fun m _ => (integral_const_mul _ _).symm)
          _ = ∫ z : (AdeleRing (𝓞 K) K)ˣ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
              SatakeCombination.slotFamilyCoeff K L ws ks js T m * (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKm m γ z) ∂νZK :=
              (integral_finsetSum _ (fun m hm => (hIntm m hm γ hγ ξ hξ).const_mul _)).symm
          _ = ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wprod (uKg γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (dKg γ)) ∂νZK := by
              congr 1; funext z; exact hpt z
          _ = _ := TRANS ξ hξ (uKg γ) (dKg γ)
      calc _ = ∑ γ ∈ ΔKpd, ∑ ξ ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
              SatakeCombination.slotFamilyCoeff K L ws ks js T m * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKm m γ z ∂νZK := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun γ _ => ?_
            rw [Finset.sum_comm]
        _ = ∑ γ ∈ ΔKpd, G (uKg γ) := by
            refine Finset.sum_congr rfl fun γ hγ => ?_
            simp only [G]
            exact Finset.sum_congr rfl fun ξ hξ => step1 γ hγ ξ hξ
        _ = ∑ u ∈ R, G (uKg (Dg u)) := by
            rw [Finset.sum_image]
            intro u _ u' _ h
            have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 1) h
            simp only [hDg_rat] at this
            exact Units.ext this
        _ = ∑ u ∈ R, G u := Finset.sum_congr rfl fun u _ => by rw [huKDg]

    have INV := AutomorphicForm.window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
        K L σ.symm hgen hdeg νZK SK T hTdisj faK hfaK fSK hfSK φa hφa φS hφS hmatchA hmatchS fT hfT hmatchT' hunit F ffF hFUF
        (AutomorphicForm.archHaarK K) cK hG cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
        (fun u z S W Wa WS hu => hT u z hu S W Wa WS) IA hIA IF hIF JA hJA JF hJF
        (AutomorphicForm.archHaarL K L) rfl rfl
        (fun u z => AutomorphicForm.tensorArch K L (δL u z)) hδLA τAL hτAL hτALc
        (fun u z v => AutomorphicForm.tensorPlace K L v (δL u z)) (fun u z hu v _ => hδLF u z v hu) τFL hτFL hτFL1
        JA' hJA' hJA'0 JF' hJF' hJF'0 IT hIT IU hIU
    have WSYM : ∀ u : Kˣ, (u : K) ≠ 1 → ∀ z : (AdeleRing (𝓞 K) K)ˣ, Wprod u⁻¹ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) u) = Wprod u z := by
      intro u hu z
      obtain ⟨hIA', hJA_, hJA'_, hF, hT_, hU⟩ := INV u z hu
      have GS := AutomorphicForm.exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv K L σ.symm u z
      have hu' : ((u⁻¹ : Kˣ) : K) ≠ 1 := by
        intro h; apply hu
        have : u⁻¹ = 1 := Units.ext h
        simpa using this
      have eJA' : JA' u⁻¹ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) u) = JA' u z := by
        by_cases hN : ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm
            (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ
        · exact hJA'_ hN
        · rw [hJA'0 u z hu hN, hJA'0 u⁻¹ _ hu' (fun h => hN (GS.1.mpr h))]
      have eJF' : ∀ v ∈ SK, JF' u⁻¹ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) u) v = JF' u z v := by
        intro v hv
        by_cases hN : ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * LanglandsTunnell.CubicInduction.diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ
        · exact (hF v hv).2.2 hN
        · rw [hJF'0 u z hu v hv hN, hJF'0 u⁻¹ _ hu' v hv (fun h => hN ((GS.2 v).mpr h))]
      simp only [Wprod]
      rw [hIA', hJA_, eJA']
      rw [Finset.prod_congr rfl (fun v hv => hT_ v hv), Finset.prod_congr rfl (fun v hv => (hF v hv).1)]
      rw [finprod_congr (fun v => finprod_congr (fun (hv : v ∉ SK ∪ T) =>
        hU v (fun h => hv (Finset.mem_union_left _ h)) (fun h => hv (Finset.mem_union_right _ h))))]
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [eJF' v hv, (hF v hv).2.1, Finset.prod_congr rfl (fun v' hv' => (hF v' (Finset.mem_of_mem_erase hv')).1)])]
    have GSYM : ∀ u : Kˣ, (u : K) ≠ 1 → G u⁻¹ = G u := by
      intro u hu
      simp only [G]
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      rw [← TRANS ξ hξ u⁻¹ u]
      congr 1; funext z; rw [WSYM u hu z]
    have INJ : ∀ γ ∈ SKf, ∀ γ' ∈ SKf, uKg γ = uKg γ' → γ = γ' := by
      intro γ hγ γ' hγ' h
      by_contra hne
      have := (RSEP γ (hSKf hγ) γ' (hSKf hγ') hne).1
      rw [← huKg γ hγ, ← huKg γ' hγ', h] at this
      exact this rfl
    have SEP : ∀ u ∈ A, u⁻¹ ∈ A → u⁻¹ = u := by
      intro u hu hui
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨γ', hγ', hγ'eq⟩ := Finset.mem_image.mp hui
      by_cases hne : γ = γ'
      · subst hne; exact hγ'eq.symm
      · have := (RSEP γ (hSKf hγ) γ' (hSKf hγ') hne).2
        exfalso; apply this
        rw [← huKg γ hγ, ← huKg γ' hγ', hγ'eq, Units.val_inv_eq_inv_val, inv_inv]
    have hA1 : ∀ u ∈ A, (u : K) ≠ 1 := fun u hu => hR1 u (Finset.mem_union_left _ hu)
    have FOLD : ∑ u ∈ R, G u = ∑ γ ∈ SKf, 2 * (if ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) = -1 then (1 / 2 : ℂ) else 1) * G (uKg γ) := by
      have h := H5ASMw47.fold_inv_w47 K A G hA1 SEP (fun u hu => GSYM u (hA1 u hu))
      rw [show R = A ∪ A.image (fun u => u⁻¹) from rfl, h, Finset.sum_image (fun γ hγ γ' hγ' h => INJ γ hγ γ' hγ' h)]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [huKg γ hγ]

    have hGW : ∀ γ ∈ SKf, ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WKg γ z ∂νZK = G (uKg γ) := by
      intro γ _
      simp only [G]
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      rw [← TRANS ξ hξ (uKg γ) (dKg γ)]
    have E : ((((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ)))) * (((cL * cT⁻¹ : ℝ) : ℂ) * ((c₀' : ℝ) : ℂ)⁻¹) * ((κ₀K : ℂ) * (((cτK / cHK : ℝ)) : ℂ)) =
        (1 / 2 : ℂ) * (((cL * cT⁻¹ : ℝ) : ℂ) * (κ₀ : ℂ) * (((cN * cτ / (cH * 1)) : ℝ) : ℂ) * ((Cfib : ℝ) : ℂ) / (Ξ.card : ℂ)) * 2 := by
      have h1 : (κ₀K : ℂ) ≠ 0 := by exact_mod_cast hκ₀Kpos.ne'
      have h2 : (((cτK / cHK : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hcτK hcHK).ne'
      have h3 : (Ξ.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hΞne).ne'
      have h4 : ((c₀' : ℝ) : ℂ) ≠ 0 := hc₀'ne
      have hcc : (c₀' : ℂ) = ((c₀' : ℝ) : ℂ) := rfl
      rw [hcc]
      field_simp
    rw [← HPD, SUMPD, FOLD, hswap WKg, Finset.sum_congr rfl (fun γ hγ => by rw [hGW γ hγ])]
    simp only [κm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    linear_combination ((if ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) = -1 then (1 / 2 : ℂ) else 1) * G (uKg γ)) * E
  rw [BKSWAP, EQ1, hlamdef, ← I8]
  linear_combination (((((κ₀ : ℂ) * ((cN * cτ / (cH * 1) : ℝ) : ℂ) * (Cfib : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * ((cτK / cHK : ℝ) : ℂ) * (Ξ.card : ℂ))))) * COMB

end S_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal (solution)
