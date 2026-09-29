-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2cb47e27-1451-54ff-be73-7d09e9d41cd0

import Theorems.Thm_AutomorphicForm_exists_continuous_noAtomicMass_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_of_areMatchingAt_uniform
import Theorems.Thm_AutomorphicForm_exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt
import Theorems.Thm_AutomorphicForm_exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_twistedParabolic_eq_hyperbolicCell_add_unipotentCell
import Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
import Theorems.Thm_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec AutomorphicForm.gl2Weyl_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply"
p2m_attr_erase "simp" "Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff"
p2m_attr_erase "simp" "Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

section WordLocalTestFn

open AutomorphicForm in
theorem CmpParabolicU.isLocalTestFn_sum_indicator_localIntegralSet_word
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (k n : ℕ) (w : (Fin k → Fin n) → GL (Fin 2) (v.adicCompletion K)) :
    IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
      ∑ ι : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((w ι)⁻¹ * x)) := by
  classical

  have hterm : ∀ ι : Fin k → Fin n, IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
      (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((w ι)⁻¹ * x)) := by
    intro ι
    have hcont : Continuous fun x : GL (Fin 2) (v.adicCompletion K) => (w ι)⁻¹ * x := continuous_mul_left _
    have heq : (fun x : GL (Fin 2) (v.adicCompletion K) =>
        (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((w ι)⁻¹ * x)) =
        ((fun x => (w ι)⁻¹ * x) ⁻¹' localIntegralSet K v).indicator (fun _ => (1 : ℂ)) := by
      funext x
      simp only [Set.indicator_apply, Set.mem_preimage]
    rw [heq]
    have hopen : IsOpen ((fun x => (w ι)⁻¹ * x) ⁻¹' localIntegralSet K v) :=
      (isOpen_localIntegralSet K v).preimage hcont
    have hcpt : IsCompact ((fun x => (w ι)⁻¹ * x) ⁻¹' localIntegralSet K v) := by
      have : (fun x => (w ι)⁻¹ * x) ⁻¹' localIntegralSet K v = (fun x => (w ι) * x) '' localIntegralSet K v := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image]
        constructor
        · intro hx; exact ⟨(w ι)⁻¹ * x, hx, by rw [mul_inv_cancel_left]⟩
        · rintro ⟨y, hy, rfl⟩; rwa [inv_mul_cancel_left]
      rw [this]
      exact (isCompact_localIntegralSet K v).image (continuous_mul_left _)
    exact ⟨isLocallyConstant_indicator_one hopen hcpt.isClosed,
      HasCompactSupport.intro hcpt fun x hx => by simp [hx]⟩

  have hsum : ∀ s : Finset (Fin k → Fin n), IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
      ∑ ι ∈ s, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((w ι)⁻¹ * x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact isLocalTestFn_zero K v
    | insert a s ha ih =>
      have h1 := hterm a
      simp only [Finset.sum_insert ha]
      exact ⟨h1.1.comp₂ ih.1 (· + ·), h1.2.add ih.2⟩
  exact hsum Finset.univ

end WordLocalTestFn

namespace CmpParabolic

theorem slope_eq_of_tendsto {F : ℝ → ℂ} {ν μ : ℂ}
    (h : Filter.Tendsto (fun R : ℝ => F R - ((R : ℂ) * ν + μ)) Filter.atTop (nhds 0)) :
    HalfLine.slope F = ν := by
  unfold HalfLine.slope
  refine Filter.Tendsto.limUnder_eq ?_
  have h1 : Filter.Tendsto (fun R : ℝ => F (R + 1) - (((R + 1 : ℝ) : ℂ) * ν + μ)) Filter.atTop (nhds 0) :=
    h.comp (Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id)
  have h2 := h1.sub h
  have : (fun R : ℝ => F (R + 1) - F R) =
      fun R : ℝ => (F (R + 1) - (((R + 1 : ℝ) : ℂ) * ν + μ)) - (F R - ((R : ℂ) * ν + μ)) + ν := by
    funext R; push_cast; ring
  rw [this]
  simpa using h2.add_const ν

theorem intercept_eq_of_tendsto {F : ℝ → ℂ} {ν μ : ℂ}
    (h : Filter.Tendsto (fun R : ℝ => F R - ((R : ℂ) * ν + μ)) Filter.atTop (nhds 0)) :
    HalfLine.intercept F = μ := by
  have hs : HalfLine.slope F = ν := slope_eq_of_tendsto h
  unfold HalfLine.intercept
  refine Filter.Tendsto.limUnder_eq ?_
  rw [hs]
  have : (fun R : ℝ => F R - (R : ℂ) * ν) = fun R : ℝ => (F R - ((R : ℂ) * ν + μ)) + μ := by
    funext R; ring
  rw [this]
  simpa using h.add_const μ

theorem tendsto_congr_of_forall_le {F G : ℝ → ℂ} {ν μ : ℂ} {R₀ : ℝ} (hFG : ∀ R : ℝ, R₀ ≤ R → F R = G R)
    (h : Filter.Tendsto (fun R : ℝ => F R - ((R : ℂ) * ν + μ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun R : ℝ => G R - ((R : ℂ) * ν + μ)) Filter.atTop (nhds 0) := by
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hR
  rw [hFG R hR]

theorem aux_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (a : κ → ℂ) (P Q ν μ : ι → κ → ℂ)
    (R c₀ : ℂ) :
    c₀ * ∑ i ∈ s, ∑ j ∈ t, a j * ((P i j + Q i j) - (R * ν i j + μ i j)) =
      c₀ * ∑ i ∈ s, ∑ j ∈ t, a j * P i j + c₀ * ∑ i ∈ s, ∑ j ∈ t, a j * Q i j -
        R * (c₀ * ∑ i ∈ s, ∑ j ∈ t, a j * ν i j) - c₀ * ∑ i ∈ s, ∑ j ∈ t, a j * μ i j := by
  have : ∀ i ∈ s, ∑ j ∈ t, a j * ((P i j + Q i j) - (R * ν i j + μ i j)) =
      ∑ j ∈ t, a j * P i j + ∑ j ∈ t, a j * Q i j - R * ∑ j ∈ t, a j * ν i j - ∑ j ∈ t, a j * μ i j := by
    intro i _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

end CmpParabolic

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
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧ ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ ∧ HasCompactSupport φ ∧ AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧ Continuous f ∧ HasCompactSupport f ∧ AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧ AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) → AutomorphicForm.AreMatchingLocal K L v σ.symm ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧ (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) + AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) → (Module.finrank K L : ℂ) * lam = c₀) ∧
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
      ∃ Δ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Δ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL →
        IsArchBiFinite L tysL φL →
      ∀ fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ,
        (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
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
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)
        ) →
      AreMatchingAt K L σ.symm (SK ∪ T) φL
        (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x) →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
      HalfLine.intercept (fun R : ℝ =>
        ∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.hyperbolicCell K ∨ γ ∈ AutomorphicForm.unipotentCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y =>
                    AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φL x y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
        (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            HalfLine.intercept (fun R : ℝ =>
              ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        Δ g := by
  obtain ⟨lam, hlam, hhex, hHyp⟩ :=
    AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_of_areMatchingAt_uniform
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
  refine ⟨lam, hlam, hhex, ?_⟩
  intro T hTdisj hTcard hTabove ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs

  obtain ⟨Δh, νh, hΔh, hH⟩ := hHyp
      T hTdisj hTcard hTabove ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
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
  obtain ⟨Δu, νu, hΔu, hU⟩ :=
    AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK ((Module.finrank K L : ℂ) * lam) hgeo'
      T hTdisj hTcard hTabove ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
  refine ⟨Δh + Δu, ?_, ?_⟩
  ·
    intro τ ε hε
    obtain ⟨Uh, hUh, hh⟩ := hΔh τ (ε / 2) (by positivity)
    obtain ⟨Uu, hUu, hu⟩ := hΔu τ (ε / 2) (by positivity)
    refine ⟨fun v => Uh v ∩ Uu v, fun v hv => ⟨(hUh v hv).1.inter (hUu v hv).1, (hUh v hv).2, (hUu v hv).2⟩, ?_⟩
    intro g hg0 hg1
    have h1 := hh g (fun y hy => by
      obtain ⟨v, hv, hyv⟩ := hy
      exact hg0 y ⟨v, hv, fun hmem => hyv hmem.1⟩) hg1
    have h2 := hu g (fun y hy => by
      obtain ⟨v, hv, hyv⟩ := hy
      exact hg0 y ⟨v, hv, fun hmem => hyv hmem.2⟩) hg1
    calc ‖(Δh + Δu) g‖ = ‖Δh g + Δu g‖ := by rw [ContinuousLinearMap.add_apply]
      _ ≤ ‖Δh g‖ + ‖Δu g‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  · intro ks js φL hφL hφLc φf hfac hbi harch fam hfam hmatch g hg

    obtain ⟨R₁, hR₁⟩ := hH ks js φL hφL hφLc φf hfac hbi harch fam hfam hmatch
    obtain ⟨R₂, hR₂⟩ := hU ks js φL hφL hφLc φf hfac hbi harch fam hfam hmatch

    have hSL : ∃ R₆ : ℝ, ∀ R : ℝ, R₆ ≤ R →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.hyperbolicCell K ∨ γ ∈ AutomorphicForm.unipotentCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y =>
                    AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φL x y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
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
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) +
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by
      obtain ⟨R₆, h₆⟩ :=
        AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_twistedParabolic_eq_hyperbolicCell_add_unipotentCell
          K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ.symm hgen ξL hξc hξt φL hφL hφLc (SK ∪ T) φa _ φf hfac
      exact ⟨R₆, fun R hR => (h₆ R hR).2.2.2.2⟩

    have hK : ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∃ ν μ : ℂ,
        Filter.Tendsto (fun R : ℝ => (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) - ((R : ℂ) * ν + μ)) Filter.atTop (nhds 0) := by
      intro ξK hξK m hm
      have hξ := (hΞ ξK).mp hξK
      have hffm : IsFactorizableTestFn K (fam m) := by
        obtain ⟨_, _, hfa, _, ff, hff, _, _, hprod⟩ := hfam m hm
        exact ⟨faK, ff, hfa, hff, hprod⟩
      obtain ⟨R₅, hR₅⟩ :=
        AutomorphicForm.exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
          K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξK hξ.1 hξ.2.1 (fam m) hffm
      have hffmU : ∃ (S' : Finset (HeightOneSpectrum (𝓞 K))) (fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
          (ff' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
          (fS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
          AutomorphicForm.IsUnitFactorization K S' (fam m) fa' ff' fS' := by
        obtain ⟨_, _, hfa, hfS, ff, hff, hprod, hvan, hfeq⟩ := hfam m hm
        refine ⟨SK ∪ T, faK, ff,
          fun v => if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
            else fSK v,
          hfa, hff, ?_, hprod, hvan, hfeq⟩
        intro v hv
        by_cases hvT : v ∈ T
        · dsimp only
          rw [dif_pos hvT]
          exact CmpParabolicU.isLocalTestFn_sum_indicator_localIntegralSet_word K v _ _ _
        · dsimp only
          rw [dif_neg hvT]
          rcases Finset.mem_union.mp hv with h | h
          · exact hfS v h
          · exact absurd h hvT
      obtain ⟨ν, μ, hνμ⟩ :=
        AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
          K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξK hξ.1 hξ.2.1 (fam m) hffmU
      exact ⟨ν, μ, CmpParabolic.tendsto_congr_of_forall_le hR₅ hνμ⟩

    have hSK : ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∃ R₇ : ℝ, ∀ R : ℝ, R₇ ≤ R →
        (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
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
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) +
        (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
      intro ξK hξK m hm
      have hξ := (hΞ ξK).mp hξK
      have hffm : IsFactorizableTestFn K (fam m) := by
        obtain ⟨_, _, hfa, _, ff, hff, _, _, hprod⟩ := hfam m hm
        exact ⟨faK, ff, hfa, hff, hprod⟩
      obtain ⟨R₇, h₇⟩ :=
        AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
          K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξK hξ.1 hξ.2.1 (fam m) hffm
      exact ⟨R₇, fun R hR => (h₇ R hR).2.2.2.2⟩

    choose! νK μK hνμK using hK
    choose! RK hRK using hSK

    have hintK : ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        HalfLine.intercept (fun R : ℝ => (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) = μK ξK m :=
      fun ξK hξK m hm => CmpParabolic.intercept_eq_of_tendsto (hνμK ξK hξK m hm)
    obtain ⟨R₆, hR₆⟩ := hSL
    have hevK : ∀ᶠ R in Filter.atTop, ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
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
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) +
        (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
      refine (Finset.eventually_all Ξ).mpr fun ξK hξK => (Finset.eventually_all _).mpr fun m hm => ?_
      filter_upwards [Filter.eventually_ge_atTop (RK ξK m)] with R hR
      exact hRK ξK hξK m hm R hR

    have hL : Filter.Tendsto (fun R : ℝ => (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.hyperbolicCell K ∨ γ ∈ AutomorphicForm.unipotentCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y =>
                    AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φL x y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
        ((R : ℂ) * ((νh + νu) g + ((Module.finrank K L : ℂ) * lam) * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * νK ξK m) +
          ((Δh + Δu) g + ((Module.finrank K L : ℂ) * lam) * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * μK ξK m))) Filter.atTop (nhds 0) := by
      have hsum : Filter.Tendsto (fun R : ℝ => ((Module.finrank K L : ℂ) * lam) * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * ((∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) - ((R : ℂ) * νK ξK m + μK ξK m))) Filter.atTop (nhds 0) := by
        have := tendsto_finset_sum Ξ (fun ξK hξK => tendsto_finset_sum (SatakeCombination.slotIndex K L ws ks js T)
          (fun m hm => (hνμK ξK hξK m hm).const_mul (SatakeCombination.slotFamilyCoeff K L ws ks js T m)))
        simpa using this.const_mul ((Module.finrank K L : ℂ) * lam)
      refine hsum.congr' ((hevK.and (Filter.eventually_ge_atTop (max (max R₁ R₂) R₆))).mono fun R hR' => ?_)
      beta_reduce
      obtain ⟨hRKR, hR⟩ := hR'
      have h1 := (hR₁ R (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR)).2.2.2 g hg
      have h2 := (hR₂ R (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR)).2.2.2 g hg
      have h6 := hR₆ R (le_trans (le_max_right _ _) hR)
      have hKs : ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * ((∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) - ((R : ℂ) * νK ξK m + μK ξK m)) =
          ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * (((∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
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
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) +
            (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) - ((R : ℂ) * νK ξK m + μK ξK m)) :=
        Finset.sum_congr rfl fun ξK hξK => Finset.sum_congr rfl fun m hm => by rw [hRKR ξK hξK m hm]
      rw [hKs, h6, CmpParabolic.aux_sum, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
      linear_combination -(h1 + h2)

    have hLint := CmpParabolic.intercept_eq_of_tendsto hL
    have hKsum : (∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * HalfLine.intercept (fun R : ℝ => (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) =
        ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * μK ξK m :=
      Finset.sum_congr rfl fun ξK hξK => Finset.sum_congr rfl fun m hm => by rw [hintK ξK hξK m hm]
    rw [hLint, hKsum, ContinuousLinearMap.add_apply]
    ring

end S_AutomorphicForm_exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform (solution)
