-- Prove2me | solution 1 for AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/12e34ae8-8bec-5d0c-9ef9-38701a5bf3b1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_areMatchingAt_symm_of_prime
import Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime
import Theorems.Thm_AutomorphicForm_forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre
import Theorems.Thm_M4aHerbrand_GenuineDescent_finite_setOf_monoidHom_comp_idelicNorm_genuineBaseChange_eq_of_prime
import Theorems.Thm_AutomorphicForm_areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_prime
import Theorems.Thm_AutomorphicForm_areMatchingLocal_splitFactor_heckeAlgebra_of_prime
import Theorems.Thm_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_not_agreesAwayFromFinite_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex ExtCitation.LocalLevel.compactGw"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val"
p2m_attr_erase "simp" "AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped TensorProduct

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (hdL : d₁L < d₂L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : twistedCutTrace K L D σ
      (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0)
    (N' : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hN'₀ : N' ≠ ⊥) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f)
    (hm : AreMatchingAt K L σ⁻¹ SK φ f) :
    ∃ (ξK : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
      (π : HeckeEigensystem K ℂ),
      π ∈ cuspClasses K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K))
        ξK N' SK ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        (formalBaseChange K L π).a w = Ψ.a w ∧ (formalBaseChange K L π).b w = Ψ.b w) := by
  classical
  have _ := hN'₀

  obtain ⟨SL', N₀, Ψ', hiff, hN₀, hφt₀, hmemW, hagree, hfib, hξσ, htrW⟩ :=
    exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime K L hdeg
      cL uL d₁L d₂L TL hdL hcovL D σ hσ SK SL hSL ξL N tysL φ hφ hφc hφt Ψ hΨ
  obtain ⟨hlev, hzero, hVne⟩ := (mem_cuspClasses_iff L _ _ _ _ _).1 hmemW
  subst hlev
  have hSL'sub : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL' → w ∈ SL :=
    fun w hw => hSL w ((hiff w).1 hw)
  have hSL'K : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL' :=
    fun w hw => (hiff w).2 hw
  have hSsat' : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL' ↔ w' ∈ SL') :=
    fun w w' h => by rw [hiff, hiff, h]

  obtain ⟨ΦL, hΦs, hΦ⟩ := exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc L 1 2

  have heq := (forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre
    L 1 2 one_pos one_lt_two ΦL hΦs hΦ ξL cL uL d₁L d₂L TL hdL hcovL).resolve_left
      fun hbot => (mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero K L D hΨ).2 (hbot N SL tysL Ψ)
  have hcongr : ∀ {V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}, V₁ = V₂ →
      ∀ (h₁ : ∀ u ∈ V₁, Continuous u) (h₂ : ∀ u ∈ V₂, Continuous u),
        twistedConvTraceOn K L D σ V₁ h₁ φ hφ hφc = twistedConvTraceOn K L D σ V₂ h₂ φ hφ hφc := by
    rintro V₁ V₂ rfl h₁ h₂
    rfl
  have htrS : twistedCutTrace K L D σ
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL Ψ'.level SL' Ψ' tysL φ hφ hφc ≠ 0 := by
    intro h0
    rw [twistedCutTrace_eq] at htrW h0
    exact htrW ((hcongr (heq Ψ'.level SL' tysL Ψ') _ _).trans h0)
  have hmemS : Ψ' ∈ cuspClasses L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL Ψ'.level SL' := by
    refine (mem_cuspClasses_iff L _ _ _ _ _).2 ⟨rfl, hzero, fun hb => ?_⟩
    apply (mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero K L D htrS).2
    rw [hb, bot_inf_eq]

  haveI : IsGalois K L := (AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hdeg σ hσ).1
  have hΞfin :=
    M4aHerbrand.GenuineDescent.finite_setOf_monoidHom_comp_idelicNorm_genuineBaseChange_eq_of_prime K L hdeg ξL

  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hmemW
  have hd := SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine L
    (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L) (fun v => heckeGen (𝓞 L) L v) (adelicBox L)
    Ψ'.toRawCentral (IsIsotypicCuspFormAt.toRealization hφ₀ hφ₀ne)
  have hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1 := by
    intro z hz
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hz
    exact hd.1 u
  have hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hd.2.2 hφ₀.continuous)

  obtain ⟨hf, hfc⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn K f (hft.1.isFactorizableTestFn K)

  have hσ' : σ.symm ≠ 1 := fun h => hσ (AlgEquiv.ext fun x => by
    have hx := DFunLike.congr_fun h (σ x)
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.one_apply] at hx
    rw [AlgEquiv.one_apply]
    exact hx.symm)
  have hm' : AreMatchingAt K L σ.symm SK φ f := hm

  obtain ⟨c, -, hid⟩ :=
    fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_areMatchingAt_symm_of_prime K L hdeg
      cK uK d₁K d₂K TK hcK hd₁K hdK hcovK 1 2 one_pos one_lt_two ΦL hΦs hΦ D σ hσ SK SL' hSL'K hSsat' hS ξL
      hξc hξt hξσ hΞfin.toFinset (fun ξ => hΞfin.mem_toFinset) Ψ'.level hN₀ tysL φ hφ hφc hφt₀ N' hN' tysK f
      hf hfc hft hm'
      (fun v _ hv =>
        areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_prime K L hdeg σ.symm
          hσ' v hv)
      (fun v _ e i₀ U hU f₁ => areMatchingLocal_splitFactor_heckeAlgebra_of_prime K L hdeg σ.symm hσ' v e i₀ U hU f₁)
      (fun v _ w hw e ϖK hϖK hϖK0 ϖL hϖL hϖL0 UK hUK UL hUL tK eK htK heK tL eL htL heL p hp0 hp1 hp =>
        exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime K L hdeg σ.symm hσ' v w hw e ϖK hϖK hϖK0 ϖL hϖL
          hϖL0 UK hUK UL hUL tK eK htK heK tL eL htL heL p hp0 hp1 hp)

  have hEis : ∀ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) →
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range → χ₁ z = 1) →
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) →
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range → χ₂ z = 1) →
      ∃ w : HeightOneSpectrum (𝓞 L), w ∉ SL' ∧
        (fun w => (Ψ'.a w, Ψ'.b w)) w ≠
          ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w) := by
    intro M hM χ₁ χ₂ hc₁ ht₁ hc₂ ht₂
    have hic₁ : IsIdeleClassChar (𝓞 L) L χ₁ := by
      intro u
      exact ht₁ _ (MonoidHom.mem_range.2 ⟨u, rfl⟩)
    have hic₂ : IsIdeleClassChar (𝓞 L) L χ₂ := by
      intro u
      exact ht₂ _ (MonoidHom.mem_range.2 ⟨u, rfl⟩)
    have hci₁ : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (((χ₁ z)⁻¹ : ℂˣ) : ℂ) := by
      simpa only [Function.comp_def, map_inv] using hc₁.comp continuous_inv
    have hci₂ : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (((χ₂ z)⁻¹ : ℂˣ) : ℂ) := by
      simpa only [Function.comp_def, map_inv] using hc₂.comp continuous_inv
    have h9 :=
      not_agreesAwayFromFinite_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre L cL uL d₁L
        d₂L TL hdL hcovL Ψ' (isArithGenuineCuspRealizable_of_mem_cuspClasses hmemW) χ₁ χ₂ hic₁ hic₂
        (Units.continuous_iff.2 ⟨hc₁, hci₁⟩) (Units.continuous_iff.2 ⟨hc₂, hci₂⟩)
    unfold HeckeEigensystem.AgreesAwayFromFinite at h9
    by_contra hall
    refine h9 ⟨SL', fun w hw => ?_⟩
    by_cases hw' : (Ψ'.a w, Ψ'.b w) =
        ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
          (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)
    · exact Prod.mk.inj hw'
    · exact (hall ⟨w, hw, hw'⟩).elim
  have hmain := hid (fun w => (Ψ'.a w, Ψ'.b w)) hEis hfib
  beta_reduce at hmain

  have hsub : ∀ x : {Ψ : HeckeEigensystem L ℂ //
      Ψ ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL Ψ'.level SL' ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL' → (Ψ.a w, Ψ.b w) = (Ψ'.a w, Ψ'.b w)},
      x = ⟨Ψ', hmemS, fun w _ => rfl⟩ := fun x =>
    Subtype.ext (eq_of_mem_cuspClasses x.2.1 hmemS fun v hv => Prod.mk.inj (x.2.2 v hv))
  rw [tsum_eq_single _ fun x hx => absurd (hsub x) hx] at hmain
  have hR := fun h0 => htrS (hmain.trans h0)

  obtain ⟨ξK, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hR)
  have hnon : ∀ {X : Type} (F : X → ℂ), ∑' x, F x ≠ 0 → Nonempty X := fun F h => by
    by_contra hemp
    haveI := not_nonempty_iff.1 hemp
    exact h tsum_empty
  obtain ⟨⟨π, hπmem, hπt⟩⟩ := hnon _ hne

  refine ⟨ξK, π, hπmem, fun w hw => ?_⟩
  have h1 := Prod.mk.inj (hπt w fun hw' => hw (hSL'sub w hw'))
  have h2 := hagree w hw
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

end S_AutomorphicForm_exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime (solution)
