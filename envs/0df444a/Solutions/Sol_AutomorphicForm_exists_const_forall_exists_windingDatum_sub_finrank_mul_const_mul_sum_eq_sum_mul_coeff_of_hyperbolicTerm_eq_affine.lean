-- Prove2me | solution 1 for AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d876e04f-facd-51ca-b8de-d0e3a3319a9e

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
import Theorems.Thm_AutomorphicForm_setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
import Theorems.Thm_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_AutomorphicForm_forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_subgroup_eq_mul_integral_prod_centralScalar_mul_diagUnits2_one
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_isSectionFnOn_adeleRing_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
import Theorems.Thm_AutomorphicForm_exists_forall_hyperbolicSlope_eq_mul_sum_slotFamilyCoeff_mul_hyperbolicSlope_of_eq_affine
import Theorems.Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
import Theorems.Thm_AutomorphicForm_slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
import Theorems.Thm_AutomorphicForm_exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_glArch_mul_glFin_heckeWord_of_not_mem
import Theorems.Thm_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem
import Theorems.Thm_AutomorphicForm_setIntegral_hyperbolicCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
import Theorems.Thm_AutomorphicForm_setIntegral_twistedHyperbolicCell_fold_eq_zero_of_forall_apply_mul_sigmaAdelicAct_centralScalar_eq_of_ne_one
import Theorems.Thm_AutomorphicForm_apply_localUnit_eq_one_of_comp_idelicNorm_of_forall_apply_localUnit_eq_one_of_ramificationIdx_eq_one
import Theorems.Thm_AutomorphicForm_apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply"
p2m_attr_erase "simp" "Representation.normBar_mk ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl"
p2m_attr_erase "simp" "LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun"
p2m_attr_erase "simp" "AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun"

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

theorem exists_under_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v := by
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 L)))
  refine ⟨⟨Q, hQp, Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hQp, hQo⟩⟩, ?_⟩
  apply HeightOneSpectrum.ext
  show Ideal.under (𝓞 K) Q = v.asIdeal
  exact hQo.over.symm
end H5ASMw47

open AutomorphicForm in
open scoped TensorProduct.RightActions in
set_option maxHeartbeats 1600000 in
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
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) :
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
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →

      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∃ (r c : ℕ) (s : HeightOneSpectrum (𝓞 K) → ℂ)
        (𝒜 ℬ : AutomorphicForm.WindingDatum r T.card c),
      (∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ∧
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
      (AL - (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * AK ξK m =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * 𝒜.coeff n) ∧
      (BL - (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * BK ξK m =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * ℬ.coeff n) := by
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
  have hΔex := H5ASMw47.exists_Delta (K := K) (L := L) (σ := σ.symm) hgen
  let Δ : Set (GL (Fin 2) L) := hΔex.choose
  have hΔd := hΔex.choose_spec.1
  have hΔdisj := hΔex.choose_spec.2.1
  have hΔcov := hΔex.choose_spec.2.2
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

  let cτK : ℝ := 1
  have hcτK : 0 < cτK := one_pos
  have hτKex := AutomorphicForm.forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2 K νZK cτK hcτK
  have KHUNF := AutomorphicForm.exists_pos_forall_integral_subgroup_eq_mul_integral_prod_centralScalar_mul_diagUnits2_one K νZK DK HK hHKc hHK μHK
  let cHK : ℝ := KHUNF.choose
  have hcHK : 0 < cHK := KHUNF.choose_spec.1
  have hHKμ := KHUNF.choose_spec.2

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
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  by_cases hξinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ.symm z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩
  ·

    by_cases HUR : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
        ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1
    swap
    · push Not at HUR
      obtain ⟨ξ₀, hξ₀, v₀, hv₀, t₀, ht₀, hξ₀t⟩ := HUR
      obtain ⟨wv₀, hwv₀⟩ := H5ASMw47.exists_under_eq K L v₀
      have hwv : HeightOneSpectrum.under (𝓞 K) wv₀ = v₀ := hwv₀
      have hwSK : HeightOneSpectrum.under (𝓞 K) wv₀ ∉ SK := by rw [hwv]; exact hv₀
      have hev : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) wv₀).asIdeal wv₀.asIdeal = 1 :=
        hS wv₀ hwSK
      obtain ⟨-, -, hN₀⟩ := (hΞ ξ₀).1 hξ₀

      have hramL : ∃ sL : (wv₀.adicCompletion L)ˣ, Valued.v (sL : wv₀.adicCompletion L) = 1 ∧
          ξL ⟨Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L wv₀ sL), Subgroup.mem_top _⟩ ≠ 1 := by
        by_contra h
        push Not at h
        exact hξ₀t (AutomorphicForm.apply_localUnit_eq_one_of_comp_idelicNorm_of_forall_apply_localUnit_eq_one_of_ramificationIdx_eq_one
          K L ξL ξ₀ hN₀ v₀ wv₀ hwv hev h t₀ ht₀)
      obtain ⟨sL, hsL, hξLs⟩ := hramL

      have hramK : ∀ ξ ∈ Ξ, ∃ t : (v₀.adicCompletion K)ˣ, Valued.v (t : v₀.adicCompletion K) = 1 ∧
          ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v₀ t), Subgroup.mem_top _⟩ ≠ 1 := by
        intro ξ hξ
        obtain ⟨-, -, hNξ⟩ := (hΞ ξ).1 hξ
        by_contra h
        push Not at h
        exact hξLs (AutomorphicForm.apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
          K L ξL ξ hNξ v₀ wv₀ hwv hev h sL hsL)

      let u₀ : (AdeleRing (𝓞 L) L)ˣ := Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L wv₀ sL)
      let z₀ : (AdeleRing (𝓞 L) L)ˣ := D.unitsAct σ u₀
      have hz₀u : D.unitsAct σ.symm z₀ = u₀ := by
        show (D.unitsAct σ.symm * D.unitsAct σ) u₀ = u₀
        rw [← map_mul]
        have h1 : σ.symm * σ = 1 := by ext x; exact σ.symm_apply_apply x
        rw [h1, map_one]
        rfl
      have hσc : AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z₀) =
          AutomorphicForm.centralScalar (𝓞 L) L u₀ := by
        rw [← hz₀u]
        refine Units.ext ?_
        ext i j
        rw [AutomorphicForm.sigmaAdelicAct, Matrix.GeneralLinearGroup.map_apply]
        simp only [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
          RingHom.toMonoidHom_eq_coe, Matrix.scalar_apply, Matrix.diagonal_apply]
        split_ifs with h
        · rfl
        · exact map_zero _
      have hz₀ : ξL ⟨z₀, Subgroup.mem_top z₀⟩ ≠ 1 := by
        intro h
        apply hξLs
        calc ξL ⟨u₀, Subgroup.mem_top u₀⟩ = ξL ⟨D.unitsAct σ.symm z₀, Subgroup.mem_top _⟩ :=
              congrArg ξL (Subtype.ext hz₀u.symm)
          _ = ξL ⟨z₀, Subgroup.mem_top z₀⟩ := hξinv z₀
          _ = 1 := h

      have hv₀N : ¬ v₀.asIdeal ∣ N' := fun h => hv₀ (hN' v₀ h)
      refine ⟨1, one_ne_zero, ?_, ?_⟩
      · rintro ⟨S', -, φ, f, -, -, -, -, -, hft, -, -, hne⟩
        refine absurd (Finset.sum_eq_zero fun ξ hξ => ?_) hne
        obtain ⟨t, ht, hξt1⟩ := hramK ξ hξ
        obtain ⟨-, hξKt, -⟩ := (hΞ ξ).1 hξ
        have hfix : ∀ g : AdelicGL2 (𝓞 K) K,
            f (g * AutomorphicForm.centralScalar (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v₀ t))) = f g :=
          fun g => (hft.1.1 _ (NumberField.AdelicLevel.centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
            K N' v₀ hv₀N t ht) g).2
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x _ => ?_
        exact AutomorphicForm.setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
          K νZK ΩK hΩK ξ hξKt f _ hξt1 hfix x
      intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs

      let s : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
        (((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)
      have hs : ∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
        intro v _
        show ((((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)) ^ 2 = _
        exact Complex.cpow_nat_inv_pow _ two_ne_zero
      have hTne : T.card ≠ 0 := by omega
      refine ⟨Fintype.card (NumberField.InfinitePlace K), Fintype.card (NumberField.InfinitePlace K) + T.card, s,
        H5ASMw47.windingDatumZero_w47 _ _ _ hTne, H5ASMw47.windingDatumZero_w47 _ _ _ hTne, hs, ?_⟩
      intro ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc AKc BKc R₀ hSP

      have hφL0 : ∀ g : AdelicGL2 (𝓞 L) L,
          φL (g * AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z₀)) = φL g := by
        intro g
        rw [hσc]
        exact AutomorphicForm.apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem
          K L SK T ws ϖs hϖs0 ns rTs hrTs zs hzs ks js φL φa φf φS hSLF wv₀ hwSK sL hsL g
      have hL0 : ALc = 0 ∧ BLc = 0 := by
        have key : ∀ R : ℝ, R₀ ≤ R → (R : ℂ) * ALc + BLc = (R : ℂ) * 0 + 0 := fun R hR => by
          rw [mul_zero, add_zero, ← (hSP R hR).1]
          refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
          exact AutomorphicForm.setIntegral_twistedHyperbolicCell_fold_eq_zero_of_forall_apply_mul_sigmaAdelicAct_centralScalar_eq_of_ne_one
            K L ΦL νZL ΩL hΩL D σ.symm hgen ξL hξt φL z₀ hz₀ hφL0 R x
        exact H5ASMw47.affine_unique key

      have hK0 : ∀ ξ ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, AKc ξ m = 0 ∧ BKc ξ m = 0 := by
        intro ξ hξ m hm
        obtain ⟨-, hξt', -⟩ := (hΞ ξ).1 hξ
        obtain ⟨t, ht, hξt1⟩ := hramK ξ hξ
        obtain ⟨-, -, -, -, ff, -, hff, hff0, hfeq⟩ := hfam m hm
        have hφK0 : ∀ g : AdelicGL2 (𝓞 K) K,
            fam m (g * AutomorphicForm.centralScalar (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v₀ t))) =
              fam m g :=
          AutomorphicForm.apply_mul_centralScalar_localUnit_eq_of_glArch_mul_glFin_heckeWord_of_not_mem
            K SK T ϖKs hϖKs0 nKs rKs hrKs zKs hzKs m faK fSK (fam m) ff hff hff0 hfeq v₀ hv₀ t ht
        have key : ∀ R : ℝ, R₀ ≤ R → (R : ℂ) * AKc ξ m + BKc ξ m = (R : ℂ) * 0 + 0 := fun R hR => by
          rw [mul_zero, add_zero, ← (hSP R hR).2 ξ hξ m hm]
          refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
          exact AutomorphicForm.setIntegral_hyperbolicCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
            K ΦK νZK ΩK hΩK ξ hξt' (fam m) _ hξt1 hφK0 R x
        exact H5ASMw47.affine_unique key
      have hsum0 : ∀ F : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) →
            (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → ℂ),
          (∀ ξ ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, F ξ m = 0) →
          ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * F ξK m = 0 := fun F hF =>
        Finset.sum_eq_zero fun ξ hξ => Finset.sum_eq_zero fun m hm => by rw [hF ξ hξ m hm, mul_zero]
      refine ⟨?_, ?_⟩
      · rw [hL0.1, hsum0 AKc (fun ξ hξ m hm => (hK0 ξ hξ m hm).1), mul_zero, sub_zero]
        symm
        exact Finset.sum_eq_zero fun n _ => by rw [H5ASMw47.coeff_windingDatumZero_w47, mul_zero]
      · rw [hL0.2, hsum0 BKc (fun ξ hξ m hm => (hK0 ξ hξ m hm).2), mul_zero, sub_zero]
        symm
        exact Finset.sum_eq_zero fun n _ => by rw [H5ASMw47.coeff_windingDatumZero_w47, mul_zero]

    by_cases hTF : AutomorphicForm.IsArchTestFactor K faK ∧ ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v)
    swap
    ·

      obtain ⟨lam0, hlam0, hhex0, -⟩ :=
        AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
          K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS (fun _ => 0) (fun _ _ => 0) X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
          hξinv (AutomorphicForm.isArchTestFactor_zero K) (fun v _ => AutomorphicForm.isLocalTestFn_zero K v) HUR
      refine ⟨lam0, hlam0, hhex0, ?_⟩
      intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs

      let s : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
        (((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)
      have hs : ∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
        intro v _
        show ((((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)) ^ 2 = _
        exact Complex.cpow_nat_inv_pow _ two_ne_zero
      have hTne : T.card ≠ 0 := by omega
      refine ⟨Fintype.card (NumberField.InfinitePlace K), Fintype.card (NumberField.InfinitePlace K) + T.card, s,
        H5ASMw47.windingDatumZero_w47 _ _ _ hTne, H5ASMw47.windingDatumZero_w47 _ _ _ hTne, hs, ?_⟩
      intro ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc AKc BKc R₀ hSP
      exfalso
      obtain ⟨m₀, hm₀⟩ := H5ASMw47.slotIndex_nonempty_w47 K L ws ks js T
      obtain ⟨-, -, hfaK, hfSK, -⟩ := hfam m₀ hm₀
      exact hTF ⟨hfaK, hfSK⟩
    obtain ⟨hfaK, hfSK⟩ := hTF
    obtain ⟨νA, cG, τG, τA, τF, cT, IA, IF, hνA, hGs, hτG, hτGc, hτA, hτF, hτF1, hcT, hT, hIA, hIF⟩ :=
      AutomorphicForm.exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn K νZK SK faK hfaK fSK hfSK cτK hcτK

    obtain ⟨lamI, hlamI0, hhexI, hPBT⟩ :=
      AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
        K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
        hξinv hfaK hfSK HUR
    refine ⟨lamI, hlamI0, hhexI, ?_⟩
    intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs

    let s : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
      (((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)
    have hs : ∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
      intro v _
      show ((((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)) ^ 2 = _
      exact Complex.cpow_nat_inv_pow _ two_ne_zero
    have hTne : T.card ≠ 0 := by omega

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
      have h1 := AutomorphicForm.apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified K L ξL ξ hN v (ws v).1 hws (HUR ξ hξ v hvT)
      show _ ^ v.asIdeal.inertiaDeg' (ws v).1.asIdeal = _
      rw [h1]
      exact congrArg (fun u : ℂˣ => (u : ℂ)) (hξσ (ws v).1 (w' v) (hTSL v hv _ hws) (hTSL v hv _ hw'u) (hws.trans hw'u.symm))

    obtain ⟨ℬ, hPB⟩ := hPBT T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs s hs

    obtain ⟨lam, hlam⟩ :=
      AutomorphicForm.exists_forall_hyperbolicSlope_eq_mul_sum_slotFamilyCoeff_mul_hyperbolicSlope_of_eq_affine
        K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
        T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
        hξinv hfaK hfSK HUR
    let κm : ℂ := lam - (Module.finrank K L : ℂ) * lamI
    have PK := AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
      T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
      HUR HNW1 HNW2 s hs HXK hfaK hfSK κ₀K (cτK / cHK) cτK hcτK νA cG hGs τG hτG hτGc τA hτA τF hτF hτF1 cT hcT hT
      IA hIA IF hIF κm
    obtain ⟨𝒜, hPK⟩ := PK
    refine ⟨_, _, s, 𝒜, ℬ, hs, ?_⟩
    intro ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc AKc BKc R₀ hSP

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

    obtain ⟨ΔKfin, hΔKf, hΔKinj, hΔKc, hΔKinv⟩ :=
      H5ASMw47.exists_DeltaKfin_w47 K (AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T) fam hfamc
    have hΔKgood : ∀ γ ∈ ΔKfin, goodK γ := fun γ hγ => ⟨⟨(hΔKf γ hγ).1, (hΔKf γ hγ).2.1⟩, (hΔKf γ hγ).2.2⟩

    have hPKw := hPK ks js fam (fun m hm => (hfam m hm).2.2.2.2) ΔKfin hΔKf hΔKinj τK hτK
      (fun γ hγ => hτKc γ (hΔKgood γ hγ)) IK (fun m hm γ hγ z => hIK m hm γ (hΔKgood γ hγ) z) hΔKc

    have KCU := fun (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (hξK : ξK ∈ Ξ)
        (m : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) (hm : m ∈ SatakeCombination.slotIndex K L ws ks js T) =>
      AutomorphicForm.slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
        K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
        T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
        ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ξK hξK m hm (AKc ξK m) (BKc ξK m) R₀ (fun R hR => (hSP R hR).2 ξK hξK m hm)
        DK hgenK HK hHKc hHK μHK Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK' (fun y R => (hTSK y R).1) (fun y R => (hTSK y R).2)
        ΔKfin hΔKf hΔKinj hΔKinv (hΔKc m hm) cHK hcHK hHKμ cτK hcτK τK hτK (fun γ hγ => hτKc γ (hΔKgood γ hγ))
        (IK m) (JK m) (fun γ hγ z => hIK m hm γ (hΔKgood γ hγ) z) (fun γ hγ z => hJK m hm γ (hΔKgood γ hγ) z)
    have SLOPE : (lam - (Module.finrank K L : ℂ) * lamI) * (∑ ξK ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * AKc ξK m) =
        κm * (∑ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔKfin, (κ₀K : ℂ) *
            (((cτK / cHK : ℝ) : ℂ) *
              ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK)) := by
      have hXY : (∑ ξK ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * AKc ξK m) =
          ∑ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
            AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
              ∑ γ ∈ ΔKfin, (κ₀K : ℂ) *
                (((cτK / cHK : ℝ) : ℂ) *
                  ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK) :=
        Finset.sum_congr rfl fun ξ hξ => Finset.sum_congr rfl fun m hm => by rw [(KCU ξ hξ m hm).2]
      rw [hXY]
    have hAff : ALc - (Module.finrank K L : ℂ) * lamI * ∑ ξK ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * AKc ξK m =
        (lam - (Module.finrank K L : ℂ) * lamI) * (∑ ξK ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * AKc ξK m) := by
      rw [hlam ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc AKc BKc R₀ hSP, sub_mul]
    exact ⟨(hAff.trans SLOPE).trans hPKw, hPB ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc AKc BKc R₀ hSP⟩
  ·

    have hΞempty : ∀ ξ, ξ ∉ Ξ := by
      intro ξ hξ
      obtain ⟨-, -, hN⟩ := (hΞ ξ).1 hξ
      obtain ⟨hβinj, -, -, hprod⟩ :=
        M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
      apply hξinv
      intro z
      have hNσ : (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (D.unitsAct σ.symm z) =
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z := by
        have h1 := hprod (D.unitsAct σ.symm z)
        have h3 : ∏ τ : L ≃ₐ[K] L, D.unitsAct τ (D.unitsAct σ.symm z) = ∏ τ : L ≃ₐ[K] L, D.unitsAct τ z := by
          have hmul : ∀ τ : L ≃ₐ[K] L, D.unitsAct τ (D.unitsAct σ.symm z) = D.unitsAct (τ * σ.symm) z := fun τ => by
            rw [map_mul]; rfl
          simp_rw [hmul]
          exact Fintype.prod_equiv (Equiv.mulRight σ.symm) _ _ (fun τ => rfl)
        rw [h3, hprod z] at h1
        have h4 := congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h1
        simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h4
        exact Units.ext (hβinj h4.symm)
      calc ξL ⟨D.unitsAct σ.symm z, Subgroup.mem_top _⟩
          = ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (D.unitsAct σ.symm z), Subgroup.mem_top _⟩ :=
            (hN _).symm
        _ = ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ :=
            congrArg ξ (Subtype.ext hNσ)
        _ = ξL ⟨z, Subgroup.mem_top z⟩ := hN z
    have hΞ0 : ∀ (F : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → ℂ), ∑ ξK ∈ Ξ, F ξK = 0 := fun F =>
      Finset.sum_eq_zero fun ξ hξ => absurd hξ (hΞempty ξ)

    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · rintro ⟨S', -, φ, f, -, -, -, -, -, -, -, -, hne⟩
      exact (hne (hΞ0 _)).elim
    intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs

    let s : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
      (((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)
    have hs : ∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
      intro v _
      show ((((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ^ ((2 : ℂ)⁻¹)) ^ 2 = _
      exact Complex.cpow_nat_inv_pow _ two_ne_zero
    have hTne : T.card ≠ 0 := by omega
    refine ⟨Fintype.card (NumberField.InfinitePlace K), Fintype.card (NumberField.InfinitePlace K) + T.card, s,
      H5ASMw47.windingDatumZero_w47 _ _ _ hTne, H5ASMw47.windingDatumZero_w47 _ _ _ hTne, hs, ?_⟩
    intro ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ALc BLc AKc BKc R₀ hSP

    have hL0 : ALc = 0 ∧ BLc = 0 := by
      have hFTL : AutomorphicForm.IsFactorizableTestFn L φL := ⟨φa, φf, hSLF.1, hSLF.2.1, hSLF.2.2.2.2.2⟩
      have E0 := AutomorphicForm.exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn
        K L α β hα hαβ ΦL νZL ΩL hΩL D σ.symm hgen ξL hξc hξt _ _ _ _ hc0 _ hTc _ hΦ₀S hΦ₀s hΦ₀
      have E1 := E0 H hHc hH μH
      have E2 := E1 Δ hΔd hΔdisj hΔcov
      obtain ⟨R₁, hR1⟩ := E2.2 hξinv φL hFTL
      have key : ∀ R : ℝ, max R₀ R₁ ≤ R → (R : ℂ) * ALc + BLc = (R : ℂ) * 0 + 0 := fun R hR => by
        rw [mul_zero, add_zero, ← (hSP R ((le_max_left _ _).trans hR)).1]
        exact (hR1 R ((le_max_right _ _).trans hR)).2.2
      exact H5ASMw47.affine_unique key
    refine ⟨?_, ?_⟩
    · rw [hL0.1, hΞ0, mul_zero, sub_zero]
      symm
      exact Finset.sum_eq_zero fun n _ => by rw [H5ASMw47.coeff_windingDatumZero_w47, mul_zero]
    · rw [hL0.2, hΞ0, mul_zero, sub_zero]
      symm
      exact Finset.sum_eq_zero fun n _ => by rw [H5ASMw47.coeff_windingDatumZero_w47, mul_zero]

end S_AutomorphicForm_exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine
end P2MW
export P2MW.S_AutomorphicForm_exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine (solution)
