-- Prove2me | solution 1 for AutomorphicForm.exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a18c4274-6b45-5535-be8d-1acff7fed0a2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_AutomorphicForm_exists_twistedCutTrace_heckeWordShift_eq_pow_mul_pow_mul
import Theorems.Thm_AutomorphicForm_exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace
import Theorems.Thm_AutomorphicForm_summable_norm_twistedCutTrace_of_isFactorizableTestFn_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
import Theorems.Thm_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder
import Theorems.Thm_AutomorphicForm_exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq
import Theorems.Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton
import Theorems.Thm_AutomorphicForm_integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_satakeData_eq_of_under_eq_of_twistedCutTrace_ne_zero_of_heckeWordShift
import Theorems.Thm_AutomorphicForm_formalBaseChange_a_b_eq_of_under_eq
import Theorems.Thm_AutomorphicForm_areMatchingAt_union_heckeWord_sum_slotFamilyCoeff_mul_of_areMatchingAt
import Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_pow_mul_pow_eq_prod_eval_slotWord_div
import Theorems.Thm_AutomorphicForm_heckeWordSum_twistedCutTrace_sub_const_mul_heckeWordSum_cutTrace_add_atoms_eq_of_remainder_rows_of_comparison
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi
import Theorems.Thm_AutomorphicForm_finite_preimage_satakePow_pow
import Theorems.Thm_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul"
p2m_attr_erase "simp" "NumberField.SUnits.val_add AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk"
p2m_attr_erase "simp" "LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace W1d

theorem continuous_satakePow (n : ℕ) : Continuous fun p : ℂ × ℂ => satakePow n p.1 p.2 := by
  suffices h : ∀ n, Continuous (fun p : ℂ × ℂ => satakePow n p.1 p.2) ∧
      Continuous (fun p : ℂ × ℂ => satakePow (n + 1) p.1 p.2) from (h n).1
  intro n
  induction n with
  | zero =>
    exact ⟨continuous_const.congr fun p => (satakePow_zero p.1 p.2).symm,
      continuous_fst.congr fun p => (satakePow_one p.1 p.2).symm⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : (fun p : ℂ × ℂ => satakePow (n + 1 + 1) p.1 p.2) =
        fun p : ℂ × ℂ => p.1 * satakePow (n + 1) p.1 p.2 - p.2 * satakePow n p.1 p.2 := by
      funext p; exact satakePow_add_two n p.1 p.2
    rw [e]
    exact (continuous_fst.mul ih.2).sub (continuous_snd.mul ih.1)

theorem continuous_satakePow_pow (n : ℕ) :
    Continuous fun p : ℂ × ℂ => (satakePow n p.1 p.2, p.2 ^ n) :=
  (continuous_satakePow n).prodMk (continuous_snd.pow n)

def NoAtom {ιK ιL : Type*} (X : Set (ιL → ℂ × ℂ)) (T : Finset ιK) (w' : ιK → ιL)
    (Λ : C(X, ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
    ∀ g : C(X, ℂ), (∀ y : X, (∃ v ∈ T, (y : ιL → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
      ‖Λ g‖ < ε

section
variable {ιK ιL : Type*} {X : Set (ιL → ℂ × ℂ)} {T : Finset ιK} {w' : ιK → ιL}

theorem NoAtom.zero : NoAtom X T w' 0 := by
  intro τ ε hε
  exact ⟨fun _ => Set.univ, fun v _ => ⟨isOpen_univ, Set.mem_univ _⟩, fun g _ _ => by simpa using hε⟩

theorem NoAtom.neg {Λ : C(X, ℂ) →L[ℂ] ℂ} (h : NoAtom X T w' Λ) : NoAtom X T w' (-Λ) := by
  intro τ ε hε
  obtain ⟨U, hU, hΛ⟩ := h τ ε hε
  refine ⟨U, hU, fun g hg hg1 => ?_⟩
  rw [ContinuousLinearMap.neg_apply, norm_neg]
  exact hΛ g hg hg1

theorem NoAtom.add {Λ₁ Λ₂ : C(X, ℂ) →L[ℂ] ℂ} (h₁ : NoAtom X T w' Λ₁) (h₂ : NoAtom X T w' Λ₂) :
    NoAtom X T w' (Λ₁ + Λ₂) := by
  intro τ ε hε
  obtain ⟨U₁, hU₁, hΛ₁⟩ := h₁ τ (ε / 2) (half_pos hε)
  obtain ⟨U₂, hU₂, hΛ₂⟩ := h₂ τ (ε / 2) (half_pos hε)
  refine ⟨fun v => U₁ v ∩ U₂ v,
    fun v hv => ⟨(hU₁ v hv).1.inter (hU₂ v hv).1, (hU₁ v hv).2, (hU₂ v hv).2⟩, fun g hg hg1 => ?_⟩
  have e₁ : ‖Λ₁ g‖ < ε / 2 := hΛ₁ g (fun y ⟨v, hv, hy⟩ => hg y ⟨v, hv, fun h => hy h.1⟩) hg1
  have e₂ : ‖Λ₂ g‖ < ε / 2 := hΛ₂ g (fun y ⟨v, hv, hy⟩ => hg y ⟨v, hv, fun h => hy h.2⟩) hg1
  rw [ContinuousLinearMap.add_apply]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem NoAtom.smul (c : ℂ) {Λ : C(X, ℂ) →L[ℂ] ℂ} (h : NoAtom X T w' Λ) : NoAtom X T w' (c • Λ) := by
  intro τ ε hε
  have hc1 : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨U, hU, hΛ⟩ := h τ (ε / (‖c‖ + 1)) (div_pos hε hc1)
  refine ⟨U, hU, fun g hg hg1 => ?_⟩
  have e := hΛ g hg hg1
  rw [ContinuousLinearMap.smul_apply, norm_smul]
  have hlt : ‖c‖ / (‖c‖ + 1) < 1 := by rw [div_lt_one hc1]; exact lt_add_one _
  calc ‖c‖ * ‖Λ g‖ ≤ ‖c‖ * (ε / (‖c‖ + 1)) := mul_le_mul_of_nonneg_left e.le (norm_nonneg c)
    _ = ε * (‖c‖ / (‖c‖ + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
    _ = ε := mul_one ε

theorem NoAtom.sum {α : Type*} (s : Finset α) (Λ : α → C(X, ℂ) →L[ℂ] ℂ)
    (h : ∀ i ∈ s, NoAtom X T w' (Λ i)) : NoAtom X T w' (∑ i ∈ s, Λ i) :=
  Finset.sum_induction Λ (NoAtom X T w') (fun _ _ ha hb => ha.add hb) NoAtom.zero h

end

noncomputable def precompCLM {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (f : C(Y, Z)) :
    C(Z, ℂ) →L[ℂ] C(Y, ℂ) :=
  { toLinearMap := (ContinuousMap.compRightAlgHom ℂ ℂ f).toLinearMap
    cont := ContinuousMap.continuous_precomp f }

@[scoped simp] theorem precompCLM_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (f : C(Y, Z))
    (g : C(Z, ℂ)) : precompCLM f g = g.comp f := rfl

end W1d
p2m_reactivate "P2MW.S_AutomorphicForm_exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq.W1d"

namespace W1c

theorem exists_glue {X : Type} [TopologicalSpace X] [CompactSpace X] {ι : Type} [Fintype ι]
    (x₁ : ℕ → X) (c₁ : ℕ → ℂ) (hc₁ : Summable fun n => ‖c₁ n‖)
    (x₂ : ι → ℕ → X) (c₂ : ι → ℕ → ℂ) (hc₂ : ∀ i, Summable fun n => ‖c₂ i n‖) (c₀ : ℂ)
    (P₁ P₂ : X → Prop) (h₁ : ∀ n, c₁ n ≠ 0 → P₁ (x₁ n)) (h₂ : ∀ i n, c₂ i n ≠ 0 → P₂ (x₂ i n)) :
    ∃ (x : ℕ → X) (c : ℕ → ℂ), (Summable fun n => ‖c n‖) ∧ (∀ n, c n ≠ 0 → P₁ (x n) ∨ P₂ (x n)) ∧
      ∀ g : C(X, ℂ), ∑' n, c n * g (x n) =
        (∑' n, c₁ n * g (x₁ n)) - c₀ * ∑ i, ∑' n, c₂ i n * g (x₂ i n) := by
  classical
  obtain ⟨σ⟩ : Nonempty (ℕ ≃ (ℕ ⊕ (ι × ℕ))) := inferInstance
  have h2' : Summable (fun p : ι × ℕ => ‖c₂ p.1 p.2‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨fun i => hc₂ i, Summable.of_finite⟩
  refine ⟨fun n => Sum.elim x₁ (fun p : ι × ℕ => x₂ p.1 p.2) (σ n),
    fun n => Sum.elim c₁ (fun p : ι × ℕ => -(c₀ * c₂ p.1 p.2)) (σ n), ?_, ?_, ?_⟩
  · refine (σ.summable_iff (f := fun s => ‖Sum.elim c₁ (fun p : ι × ℕ => -(c₀ * c₂ p.1 p.2)) s‖)).2 ?_
    refine Summable.sum _ ?_ ?_
    · simpa [Function.comp_def] using hc₁
    · simpa [Function.comp_def, norm_neg, norm_mul] using h2'.mul_left ‖c₀‖
  · intro n
    dsimp only
    generalize σ n = s
    rcases s with m | ⟨i, m⟩
    · intro hn
      simp only [Sum.elim_inl] at hn
      exact Or.inl (h₁ m hn)
    · intro hn
      simp only [Sum.elim_inr] at hn
      have : c₂ i m ≠ 0 := by
        intro h; apply hn; simp [h]
      exact Or.inr (h₂ i m this)
  · intro g
    have hg : ∀ y, ‖g y‖ ≤ ‖g‖ := fun y => g.norm_coe_le_norm y
    have hS1 : Summable fun n => c₁ n * g (x₁ n) :=
      Summable.of_norm_bounded (hc₁.mul_right ‖g‖) fun n => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
    have hS2i : ∀ i, Summable fun n => c₂ i n * g (x₂ i n) := fun i =>
      Summable.of_norm_bounded ((hc₂ i).mul_right ‖g‖) fun n => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
    have hS2 : Summable fun p : ι × ℕ => -(c₀ * c₂ p.1 p.2) * g (x₂ p.1 p.2) :=
      Summable.of_norm_bounded ((h2'.mul_left ‖c₀‖).mul_right ‖g‖) fun p => by
        rw [norm_mul, norm_neg, norm_mul]; exact mul_le_mul_of_nonneg_left (hg _) (by positivity)
    rw [σ.tsum_eq (fun s => Sum.elim c₁ (fun p : ι × ℕ => -(c₀ * c₂ p.1 p.2)) s *
      g (Sum.elim x₁ (fun p : ι × ℕ => x₂ p.1 p.2) s))]
    rw [Summable.tsum_sum (by simpa [Function.comp_def] using hS1) (by simpa [Function.comp_def] using hS2)]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hS2.tsum_prod' (fun i => by simpa [neg_mul, mul_assoc] using ((hS2i i).mul_left c₀).neg)]
    simp only [neg_mul, mul_assoc, tsum_neg, tsum_mul_left, tsum_fintype, Finset.sum_neg_distrib,
      ← Finset.mul_sum, sub_eq_add_neg]

theorem inertiaDeg_eq_of_under_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w w' : HeightOneSpectrum (𝓞 L))
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
    (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal =
      (HeightOneSpectrum.under (𝓞 K) w').asIdeal.inertiaDeg' w'.asIdeal := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : w'.asIdeal.IsPrime := w'.isPrime
  haveI h1 : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w').asIdeal := ⟨by rw [← h]; rfl⟩
  haveI h2 : w'.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w').asIdeal := ⟨rfl⟩
  rw [h]
  haveI := (HeightOneSpectrum.under (𝓞 K) w').isMaximal
  haveI := w.isMaximal
  haveI := w'.isMaximal
  rw [Ideal.inertiaDeg'_eq_inertiaDeg (HeightOneSpectrum.under (𝓞 K) w').asIdeal w.asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal]
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup (HeightOneSpectrum.under (𝓞 K) w').asIdeal
    w.asIdeal w'.asIdeal (L ≃ₐ[K] L)

theorem atoms
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X) (c₀ : ℂ)
    (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ)
    (hcs : Summable fun n => ‖cs n‖)
    (heis : ∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₂ z = 1) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
              (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w))
    {ι : Type} [Fintype ι]
    (tabsK : ι → ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (csK : ι → ℕ → ℂ)
    (hcsK : ∀ i, Summable fun n => ‖csK i n‖)
    (heisK : ∀ i n, csK i n ≠ 0 →
      ∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₂ z = 1) ∧
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
            NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
          ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
            tabsK i n v = ((LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).a v,
              (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).b v))
    (hmem : ∀ i n, (fun w : HeightOneSpectrum (𝓞 L) =>
          (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
              (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).1 (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).2,
            (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).2 ^
              (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)) ∈ X) :
    ∃ (E : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hEX : ∀ n, E n ∈ X) (e : ℕ → ℂ),
      (Summable fun n => ‖e n‖) ∧
      (∀ n, e n ≠ 0 →
        (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → E n w = E n w') ∧
        ((∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₂ z = 1) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            E n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
              (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∨
         (∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₂ z = 1) ∧
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
            NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            E n w =
              ((formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).a w,
                (formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).b w)))) ∧
      ∀ g : C(X, ℂ),
        ∑' n, e n * g ⟨E n, hEX n⟩ =
          (∑' n, cs n * g ⟨tabs n, htabs n⟩) -
            c₀ * ∑ i : ι, ∑' n, csK i n * g ⟨fun w : HeightOneSpectrum (𝓞 L) =>
          (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
              (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).1 (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).2,
            (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).2 ^
              (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal), hmem i n⟩ := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hXc
  obtain ⟨x, c, hc, hdesc, hsum⟩ := W1c.exists_glue (X := X) (ι := ι)
    (fun n => (⟨tabs n, htabs n⟩ : X)) cs hcs
    (fun i n => (⟨fun w : HeightOneSpectrum (𝓞 L) =>
          (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
              (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).1 (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).2,
            (tabsK i n (HeightOneSpectrum.under (𝓞 K) w)).2 ^
              (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal), hmem i n⟩ : X)) csK hcsK c₀
    (fun y : X => (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w = (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w') ∧
      (∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₂ z = 1) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
              (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)))
    (fun y : X => (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w = (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w') ∧
      (∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₂ z = 1) ∧
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
            NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w =
              ((formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).a w,
                (formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).b w)))
    (fun n hn => heis n hn)
    (fun i n hn => by
      obtain ⟨M, hM, χ₁, χ₂, hc1, ht1, hc2, ht2, hunr, htab⟩ := heisK i n hn
      refine ⟨fun w w' hw hw' huw => ?_, M, hM, χ₁, χ₂, hc1, ht1, hc2, ht2, hunr, fun w hw => ?_⟩
      · dsimp only
        rw [W1c.inertiaDeg_eq_of_under_eq K L w w' huw, huw]
      · dsimp only
        have hu : HeightOneSpectrum.under (𝓞 K) w ∉ SK := fun h => hw (hSL w h)
        rw [htab _ hu]
        rfl)
  refine ⟨fun n => (x n).1, fun n => (x n).2, c, hc, fun n hn => ?_, fun g => hsum g⟩
  rcases hdesc n hn with ⟨hf, hL⟩ | ⟨hf, hK⟩
  · exact ⟨hf, Or.inl hL⟩
  · exact ⟨hf, Or.inr hK⟩

end W1c
p2m_reactivate "P2MW.S_AutomorphicForm_exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq.W1d"

set_option maxHeartbeats 4000000 in
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
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f)

    (harch : AreMatchingArch K L σ.symm φa faK)
    (hloc : ∀ v ∈ SK, AreMatchingLocal K L v σ.symm (φS v) (fSK v))
    (hφfac : ∃ φf, IsSemiLocalFactorization K L SK φ φa φf φS)
    (hffac : ∃ ff, IsUnitFactorization K SK f faK ff fSK)
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

    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))

    (hFLu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
      AreMatchingLocal K L v σ.symm ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (hFLs : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      ∀ (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K]
          (Fin (Module.finrank K L) → v.adicCompletion K))
        (i₀ : Fin (Module.finrank K L)) (U : Subgroup (GL (Fin 2) (v.adicCompletion K))),
        U = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
        ∀ f₁ : HeckePair.HeckeAlgebra U ℂ,
          AreMatchingLocal K L v σ.symm
            (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ)
                  (Matrix.GeneralLinearGroup.map
                    ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i₀).comp
                      e.toAlgHom).toRingHom g) *
                ({h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
                    ∀ i : Fin (Module.finrank K L), i ≠ i₀ →
                      Matrix.GeneralLinearGroup.map
                          ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i).comp
                            e.toAlgHom).toRingHom h ∈ U}.indicator (fun _ => (1 : ℂ)) g))
            (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hFLi : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → ∀ (w : v.Extension (𝓞 L)),
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1 →
      ∀ (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
        (ϖK : v.adicCompletionIntegers K), Irreducible ϖK →
        ∀ (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
          (ϖL : w.1.adicCompletionIntegers L), Irreducible ϖL →
        ∀ (hϖL0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL ≠ 0)
          (UK : Subgroup (GL (Fin 2) (v.adicCompletion K))),
          UK = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
        ∀ (UL : Subgroup (GL (Fin 2) (w.1.adicCompletion L))),
          UL = LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) →
        ∀ (TK EK : HeckePair.HeckeAlgebra UK ℂ),
          (TK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
            (HeckePair.doubleCoset UK (LocalGL2.diagPi ϖK hϖK0)).indicator (fun _ => (1 : ℂ)) →
          (EK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
            (Ideal.absNorm v.asIdeal : ℂ) •
              ({x : GL (Fin 2) (v.adicCompletion K) | ∃ u ∈ UK,
                  (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
                    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
                      (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}.indicator
                fun _ => (1 : ℂ)) →
        ∀ (TL EL : HeckePair.HeckeAlgebra UL ℂ),
          (TL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
            (HeckePair.doubleCoset UL (LocalGL2.diagPi ϖL hϖL0)).indicator (fun _ => (1 : ℂ)) →
          (EL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
            (Ideal.absNorm w.1.asIdeal : ℂ) •
              ({x : GL (Fin 2) (w.1.adicCompletion L) | ∃ u ∈ UL,
                  (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
                    algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL •
                      (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))}.indicator
                fun _ => (1 : ℂ)) →
        ∀ (p : ℕ → HeckePair.HeckeAlgebra UK ℂ), p 0 = 2 → p 1 = TK →
          (∀ k : ℕ, p (k + 2) = TK * p (k + 1) - EK * p k) →
          ∃ b : HeckePair.HeckeAlgebra UL ℂ →ₐ[ℂ] HeckePair.HeckeAlgebra UK ℂ,
            b TL = p (Module.finrank K L) ∧ b EL = EK ^ Module.finrank K L ∧
              ∀ φ : HeckePair.HeckeAlgebra UL ℂ,
                AreMatchingLocal K L v σ.symm
                  (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
                    (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
                      (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g))
                  (b φ : GL (Fin 2) (v.adicCompletion K) → ℂ))

    (XK : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ))
    (hXKc : ∀ ξK ∈ Ξ, IsCompact (XK ξK))
    (hXKbox : ∀ ξK ∈ Ξ,
      {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
            (∀ v ∈ SK, x v = 0) ∧
            ∀ v ∉ SK,
              (x v).2 = HeckeEigensystem.cNorm v *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
              ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
                  Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                    ℂˣ) : ℂ)‖ ∧
              conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ XK ξK)
    (hXK : ∀ ξK ∈ Ξ, ∀ x ∈ XK ξK,
      (fun w : HeightOneSpectrum (𝓞 L) =>
        (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
            (x (HeightOneSpectrum.under (𝓞 K) w)).1 (x (HeightOneSpectrum.under (𝓞 K) w)).2,
          (x (HeightOneSpectrum.under (𝓞 K) w)).2 ^
            (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)) ∈ X) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧ ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ ∧ HasCompactSupport φ ∧ AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧ Continuous f ∧ HasCompactSupport f ∧ AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧ AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) → AutomorphicForm.AreMatchingLocal K L v σ.symm ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧ (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) + AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) → (Module.finrank K L : ℂ) * lam = c₀) ∧
    ∃ (E : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hEX : ∀ n, E n ∈ X) (e : ℕ → ℂ),
    (Summable fun n => ‖e n‖) ∧
    (∀ n, e n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → E n w = E n w') ∧
      ((∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₂ z = 1) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            E n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
              (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∨
       (∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₂ z = 1) ∧
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
            NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            E n w =
              ((formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).a w,
                (formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).b w)))) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (g : C(X, ℂ)),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
            (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ cuspClasses L
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
              (∏ v ∈ T, (Ψ.1.a (w' v)) ^ ks v * ((HeckeEigensystem.cNorm (w' v))⁻¹ * Ψ.1.b (w' v)) ^ js v) *
                twistedCutTrace K L D σ
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) -
          (Module.finrank K L : ℂ) * lam * ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
            (∑ ξK ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK},
              (∏ v ∈ T, ((formalBaseChange K L π.1).a (w' v)) ^ ks v *
                  ((HeckeEigensystem.cNorm (w' v))⁻¹ * (formalBaseChange K L π.1).b (w' v)) ^ js v) *
                cutTrace K
                  (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π.1 tysK f hf hfc) +
          (∑' n, e n * g ⟨E n, hEX n⟩) = Λ g := by
  classical

  have hSLram : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL := by
    intro w hw
    by_contra hwSL
    exact hw (hS w fun h => hwSL (hSL w h))

  obtain ⟨hbandL, tabs, htabs, cs, hcs, heis, hmainL⟩ :=
    AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen SL hSsat hSLram ξL hξc hξt hξσ N hN tysL SK φa φS X hXc hX

  have stepK := fun ξK : Ξ =>
    AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK.1
      ((hΞ ξK.1).1 ξK.2).1 ((hΞ ξK.1).1 ξK.2).2.1 N' hN' tysK faK fSK (XK ξK.1) (hXKc ξK.1 ξK.2)
      (hXKbox ξK.1 ξK.2)
  choose hbandK tabsK htabsK csK hcsK heisK hmainK using stepK

  have hm : AreMatchingAt K L σ.symm SK φ f := by
    obtain ⟨φf, hφf⟩ := hφfac
    obtain ⟨ff, hff⟩ := hffac
    exact ⟨φa, φf, φS, faK, ff, fSK, hφf, hff, harch, hloc⟩

  obtain ⟨lam, hlam, hhex, stepΔ⟩ :=
    AutomorphicForm.exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK
      X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ φ hφ hφc hφt N' hN' tysK f hf hfc hft hm hφfac hffac c₀ hgeo
  refine ⟨lam, hlam, hhex, ?_⟩
  have hgeo' : ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' → ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ) (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ) (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f) (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f) (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) → AutomorphicForm.AreMatchingLocal K L v σ.symm ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))), (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧ LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = ((Module.finrank K L : ℂ) * lam) * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) + AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    by_cases hx : (∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧ ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ ∧ HasCompactSupport φ ∧ AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧ Continuous f ∧ HasCompactSupport f ∧ AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧ AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) → AutomorphicForm.AreMatchingLocal K L v σ.symm ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧ (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) + AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0)
    · rw [hhex hx]; exact hgeo
    · intro S' hS' φ _hφ _hφc _hφt f _hf _hfc _hft _hm _hunit
      have hK0 : (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) = 0 := by
        by_contra hne
        exact hx ⟨S', hS', φ, f, _hφ, _hφc, _hφt, _hf, _hfc, _hft, _hm, _hunit, hne⟩
      rw [hgeo S' hS' φ _hφ _hφc _hφt f _hf _hfc _hft _hm _hunit, hK0, mul_zero, mul_zero]

  have ATOMS : ∃ (E : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hEX : ∀ n, E n ∈ X) (e : ℕ → ℂ),
      (Summable fun n => ‖e n‖) ∧
      (∀ n, e n ≠ 0 →
        (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → E n w = E n w') ∧
        ((∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
            (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
            (∀ z : (AdeleRing (𝓞 L) L)ˣ,
              z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                χ₁ z = 1) ∧
            (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
            (∀ z : (AdeleRing (𝓞 L) L)ˣ,
              z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                χ₂ z = 1) ∧
            ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
              E n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
                (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∨
         (∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
            (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
            (∀ z : (AdeleRing (𝓞 K) K)ˣ,
              z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                χ₁ z = 1) ∧
            (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
            (∀ z : (AdeleRing (𝓞 K) K)ˣ,
              z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                χ₂ z = 1) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
              NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
            ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
              E n w =
                ((formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).a w,
                  (formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).b w)))) ∧
      ∀ g : C(X, ℂ),
        ∑' n, e n * g ⟨E n, hEX n⟩ =
          (∑' n, cs n * g ⟨tabs n, htabs n⟩) -
            ((Module.finrank K L : ℂ) * lam) * ∑ ξK : Ξ, ∑' n, csK ξK n *
              g ⟨fun w : HeightOneSpectrum (𝓞 L) =>
                  (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
                      (tabsK ξK n (HeightOneSpectrum.under (𝓞 K) w)).1 (tabsK ξK n (HeightOneSpectrum.under (𝓞 K) w)).2,
                    (tabsK ξK n (HeightOneSpectrum.under (𝓞 K) w)).2 ^
                      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal),
                hXK ξK.1 ξK.2 _ (htabsK ξK n)⟩ := by
    exact W1c.atoms K L SK SL hSL X hXc ((Module.finrank K L : ℂ) * lam) tabs htabs cs hcs heis tabsK csK hcsK heisK
      (fun ξK n => hXK ξK.1 ξK.2 _ (htabsK ξK n))
  obtain ⟨E, hEX, e, he, hEdesc, hEsum⟩ := ATOMS
  refine ⟨E, hEX, e, he, hEdesc, ?_⟩
  intro T hTd hT2 hTSL ws w' hw'

  have hunif : ∀ (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)),
      ∃ ϖ : u.adicCompletionIntegers F, Irreducible ϖ ∧
        algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0 := by
    intro F _ _ u
    obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible (u.adicCompletionIntegers F)
    refine ⟨ϖ, hirr, fun h => hirr.ne_zero ?_⟩
    have hinj := IsFractionRing.injective (u.adicCompletionIntegers F) (u.adicCompletion F)
    exact hinj (by rw [h, map_zero])
  have hcoset : ∀ (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
      (ϖ : u.adicCompletionIntegers F) (hirr : Irreducible ϖ)
      (h0 : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0),
      ∃ (n : ℕ) (r : Fin n → GL (Fin 2) (u.adicCompletion F)),
        HeckeIntegralSeam.IsHeckeCosetSystem
          (LocalGL2.integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F))
          (LocalGL2.diagPi ϖ h0) r := by
    intro F _ _ u ϖ hirr h0
    have hmax : IsLocalRing.maximalIdeal (u.adicCompletionIntegers F) = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
    haveI : Finite (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) := by
      haveI hfin : Finite (IsLocalRing.ResidueField (u.adicCompletionIntegers F)) := inferInstance
      exact Finite.of_equiv (IsLocalRing.ResidueField (u.adicCompletionIntegers F))
        (Ideal.quotEquivOfEq hmax).toEquiv
    exact HeckeIntegralSeam.exists_isHeckeCosetSystem_integralSubgroup_diagPi hirr h0
  have hscalar : ∀ (F' : Type) [Field F'] (a : F'), a ≠ 0 →
      ∃ z : GL (Fin 2) F', (z : Matrix (Fin 2) (Fin 2) F') = a • (1 : Matrix (Fin 2) (Fin 2) F') := by
    intro F' _ a ha
    refine ⟨⟨a • (1 : Matrix (Fin 2) (Fin 2) F'), a⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F'), ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ ha, one_smul]
    · rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ ha, one_smul]
  have DATA_L : ∃ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
      (_ : ∀ v ∈ T, Irreducible (ϖs v))
      (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
      (ns : HeightOneSpectrum (𝓞 K) → ℕ)
      (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
      (_ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
      (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
      ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) := by
    have h1 := fun v : HeightOneSpectrum (𝓞 K) => hunif L (ws v).1
    choose ϖs hirr h0 using h1
    have h2 := fun v : HeightOneSpectrum (𝓞 K) => hcoset L (ws v).1 (ϖs v) (hirr v) (h0 v)
    choose ns rTs hrTs using h2
    have h3 := fun v : HeightOneSpectrum (𝓞 K) => hscalar ((ws v).1.adicCompletion L) _ (h0 v)
    choose zs hzs using h3
    exact ⟨ϖs, fun v _ => hirr v, fun v _ => h0 v, ns, rTs, fun v _ => hrTs v, zs, fun v _ => hzs v⟩
  obtain ⟨ϖs, hϖs, hϖs0, ns, rTs, hrTs, zs, hzs⟩ := DATA_L
  have DATA_K : ∃ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
      (_ : ∀ v ∈ T, Irreducible (ϖKs v))
      (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
      (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
      (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
      (_ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
      (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
      ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    have h1 := fun v : HeightOneSpectrum (𝓞 K) => hunif K v
    choose ϖKs hirrK h0K using h1
    have h2 := fun v : HeightOneSpectrum (𝓞 K) => hcoset K v (ϖKs v) (hirrK v) (h0K v)
    choose nKs rKs hrKs using h2
    have h3 := fun v : HeightOneSpectrum (𝓞 K) => hscalar (v.adicCompletion K) _ (h0K v)
    choose zKs hzKs using h3
    exact ⟨ϖKs, fun v _ => hirrK v, fun v _ => h0K v, nKs, rKs, fun v _ => hrKs v, zKs, fun v _ => hzKs v⟩
  obtain ⟨ϖKs, hϖKs, hϖKs0, nKs, rKs, hrKs, zKs, hzKs⟩ := DATA_K

  obtain ⟨ΛL, hΛLna, hΛLfib, hΛL⟩ := hmainL T hTd hT2 hTSL ws w' hw' ϖs hϖs hϖs0 ns rTs hrTs zs hzs
  have hΛK := fun ξK : Ξ => hmainK ξK T hTd hT2 ϖKs hϖKs hϖKs0 nKs rKs hrKs zKs hzKs
  choose ΛK hΛKna hΛK using hΛK
  obtain ⟨Δ, hΔna, hΔ⟩ :=
    stepΔ T hTd hT2 hTSL ws w' hw' ϖs hϖs hϖs0 ns rTs hrTs zs hzs ϖKs hϖKs hϖKs0 nKs rKs hrKs zKs hzKs

  have PUSH : ∀ ξK : Ξ, ∃ Λ' : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ' g‖ < ε) ∧
      ∀ (g : C(X, ℂ)) (gK : C(XK ξK.1, ℂ)),
        (∀ x : XK ξK.1, gK x = g ⟨fun w : HeightOneSpectrum (𝓞 L) =>
            (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
                ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) (HeightOneSpectrum.under (𝓞 K) w)).1
                ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) (HeightOneSpectrum.under (𝓞 K) w)).2,
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) (HeightOneSpectrum.under (𝓞 K) w)).2 ^
                (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal), hXK ξK.1 ξK.2 _ x.2⟩) →
        Λ' g = ΛK ξK gK := by
    intro ξK

    have hT : ∀ v ∈ T, HeightOneSpectrum.under (𝓞 K) (w' v) = v := by
      intro v hv
      apply HeightOneSpectrum.ext
      show (w' v).asIdeal.under (𝓞 K) = v.asIdeal
      rw [hw' v hv, Ideal.under_smul]
      exact congrArg HeightOneSpectrum.asIdeal (ws v).2

    have hf : ∀ w : HeightOneSpectrum (𝓞 L),
        (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal ≠ 0 := by
      intro w
      haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := ⟨rfl⟩
      haveI : (HeightOneSpectrum.under (𝓞 K) w).asIdeal.IsMaximal :=
        (HeightOneSpectrum.under (𝓞 K) w).isMaximal
      exact (Ideal.inertiaDeg'_pos _ _).ne'

    obtain ⟨bc, hbc_def⟩ : ∃ bc : C(XK ξK.1, X), ∀ x : XK ξK.1, bc x =
        ⟨fun w : HeightOneSpectrum (𝓞 L) =>
            (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
                ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) (HeightOneSpectrum.under (𝓞 K) w)).1
                ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) (HeightOneSpectrum.under (𝓞 K) w)).2,
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) (HeightOneSpectrum.under (𝓞 K) w)).2 ^
                (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal), hXK ξK.1 ξK.2 _ x.2⟩ := by
      refine ⟨⟨fun x => ⟨_, hXK ξK.1 ξK.2 _ x.2⟩, ?_⟩, fun x => rfl⟩
      apply Continuous.subtype_mk
      exact continuous_pi fun w =>
        (W1d.continuous_satakePow_pow _).comp
          ((continuous_apply (HeightOneSpectrum.under (𝓞 K) w)).comp continuous_subtype_val)

    have hbc : ∀ (x : XK ξK.1), ∀ v ∈ T, ((bc x : X) : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) =
        (fun (v : HeightOneSpectrum (𝓞 K)) (p : ℂ × ℂ) =>
          (satakePow ((HeightOneSpectrum.under (𝓞 K) (w' v)).asIdeal.inertiaDeg' (w' v).asIdeal) p.1 p.2,
            p.2 ^ (HeightOneSpectrum.under (𝓞 K) (w' v)).asIdeal.inertiaDeg' (w' v).asIdeal)) v
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v) := by
      intro x v hv
      rw [hbc_def x]
      dsimp only
      rw [hT v hv]

    have key := ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres (XK ξK.1) (hXKc ξK.1 ξK.2) X T w'
        (fun (v : HeightOneSpectrum (𝓞 K)) (p : ℂ × ℂ) =>
          (satakePow ((HeightOneSpectrum.under (𝓞 K) (w' v)).asIdeal.inertiaDeg' (w' v).asIdeal) p.1 p.2,
            p.2 ^ (HeightOneSpectrum.under (𝓞 K) (w' v)).asIdeal.inertiaDeg' (w' v).asIdeal))
        (fun v _ => W1d.continuous_satakePow_pow _)
        (fun v _ c => AutomorphicForm.finite_preimage_satakePow_pow _ (hf (w' v)) c)
        bc hbc (ΛK ξK) (hΛKna ξK)
    refine ⟨(ΛK ξK).comp (W1d.precompCLM bc), ?_, ?_⟩
    · intro τ ε hε
      obtain ⟨U, hU, hΛ⟩ := key τ ε hε
      exact ⟨U, hU, fun g hg hg1 => by
        rw [ContinuousLinearMap.comp_apply, W1d.precompCLM_apply]; exact hΛ g hg hg1⟩
    · intro g gK hgK
      rw [ContinuousLinearMap.comp_apply, W1d.precompCLM_apply]
      congr 1
      ext x
      rw [ContinuousMap.comp_apply, hbc_def x]
      exact (hgK x).symm
  choose ΛK' hΛK'na hΛK' using PUSH

  refine ⟨-ΛL + Δ + ((Module.finrank K L : ℂ) * lam) • ∑ ξK : Ξ, ΛK' ξK, ?_, ?_⟩
  ·
    have h1 : W1d.NoAtom X T w' ΛL := hΛLna
    have h2 : W1d.NoAtom X T w' Δ := hΔna
    have h3 : ∀ ξK : Ξ, W1d.NoAtom X T w' (ΛK' ξK) := hΛK'na
    exact (h1.neg.add h2).add (W1d.NoAtom.smul ((Module.finrank K L : ℂ) * lam) (W1d.NoAtom.sum Finset.univ ΛK' fun ξK _ => h3 ξK))
  intro ks js g hg

  rw [hEsum g]
  exact AutomorphicForm.heckeWordSum_twistedCutTrace_sub_const_mul_heckeWordSum_cutTrace_add_atoms_eq_of_remainder_rows_of_comparison
    K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ φ hφ hφc hφt N' hN' tysK f hf hfc hft harch hloc hφfac hffac ((Module.finrank K L : ℂ) * lam) hgeo' cK uK d₁K d₂K TK hcK hd₁K hdK hcovK hFLu hFLs hFLi XK hXKc hXKbox hXK tabs htabs cs hcs tabsK htabsK csK hcsK T hTd hT2 hTSL ws w' hw' ϖs hϖs hϖs0 ns rTs hrTs zs hzs ϖKs hϖKs hϖKs0 nKs rKs hrKs zKs hzKs ΛL hΛL ΛK hΛK Δ hΔ ΛK' hΛK' ks js g hg

end S_AutomorphicForm_exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq (solution)
