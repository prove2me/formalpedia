-- Prove2me | solution 1 for AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e5167e47-93c2-5066-b2a9-3950a1ec51ea

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
import Theorems.Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_areMatchingLocal_heckeWord_sum_coeff_univWord_mul_heckeWord_of_ramificationIdx_eq_one_of_prime
import Theorems.Thm_AutomorphicForm_eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
import Theorems.Thm_AutomorphicForm_exists_diagUnits2_normString_isOrbitalIntegral_ne_zero_isTwistedOrbitalIntegral_eq_heckeWord_of_ramificationIdx_eq_one_of_prime
import Theorems.Thm_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet
import Theorems.Thm_AutomorphicForm_exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet
import Theorems.Thm_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
import Theorems.Thm_AutomorphicForm_exists_smul_eq_of_isUnitFactorization_of_isUnitFactorization_of_exists_ne_zero
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.gl2Weyl_val AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply"
p2m_attr_erase "simp" "AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace IPACK

noncomputable def zero (r d c : ℕ) (hd : d ≠ 0) : AutomorphicForm.WindingDatum r d c where
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

end IPACK

namespace IPACK

theorem mul_prod_ite_union_eq {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    (SK T : Finset ι) (hd : Disjoint T SK) (W A A' : ∀ v, α v → ℂ) (x : ∀ v, α v) (a a' : ℂ)
    (h : a' * ∏ v ∈ SK, A' v (x v) = a * ∏ v ∈ SK, A v (x v)) :
    a' * ∏ v ∈ SK ∪ T, (fun v => if v ∈ T then W v else A' v) v (x v) =
      a * ∏ v ∈ SK ∪ T, (fun v => if v ∈ T then W v else A v) v (x v) := by
  rw [Finset.prod_union hd.symm, Finset.prod_union hd.symm]
  have e1 : ∀ B : ∀ v, α v → ℂ,
      ∏ v ∈ SK, (fun v => if v ∈ T then W v else B v) v (x v) = ∏ v ∈ SK, B v (x v) :=
    fun B => Finset.prod_congr rfl fun v hv => by simp [Finset.disjoint_right.mp hd hv]
  have e2 : ∀ B B' : ∀ v, α v → ℂ,
      ∏ v ∈ T, (fun v => if v ∈ T then W v else B v) v (x v) =
        ∏ v ∈ T, (fun v => if v ∈ T then W v else B' v) v (x v) :=
    fun B B' => Finset.prod_congr rfl fun v hv => by simp [hv]
  rw [e1 A, e1 A', e2 A' A, ← mul_assoc, ← mul_assoc, h]

theorem mul_prod_dite_union_eq {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    (SK T : Finset ι) (hd : Disjoint T SK) (W : ∀ v, v ∈ T → α v → ℂ) (A A' : ∀ v, α v → ℂ)
    (x : ∀ v, α v) (a a' : ℂ)
    (h : a' * ∏ v ∈ SK, A' v (x v) = a * ∏ v ∈ SK, A v (x v)) :
    a' * ∏ v ∈ SK ∪ T, (fun v => if hv : v ∈ T then W v hv else A' v) v (x v) =
      a * ∏ v ∈ SK ∪ T, (fun v => if hv : v ∈ T then W v hv else A v) v (x v) := by
  rw [Finset.prod_union hd.symm, Finset.prod_union hd.symm]
  have e1 : ∀ B : ∀ v, α v → ℂ,
      ∏ v ∈ SK, (fun v => if hv : v ∈ T then W v hv else B v) v (x v) = ∏ v ∈ SK, B v (x v) :=
    fun B => Finset.prod_congr rfl fun v hv => by simp [Finset.disjoint_right.mp hd hv]
  have e2 : ∀ B B' : ∀ v, α v → ℂ,
      ∏ v ∈ T, (fun v => if hv : v ∈ T then W v hv else B v) v (x v) =
        ∏ v ∈ T, (fun v => if hv : v ∈ T then W v hv else B' v) v (x v) :=
    fun B B' => Finset.prod_congr rfl fun v hv => by simp [hv]
  rw [e1 A, e1 A', e2 A' A, ← mul_assoc, ← mul_assoc, h]

end IPACK

namespace IPACK

open AutomorphicForm

theorem ne_one_of_zpowers {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime) :
    σ ≠ 1 := by
  intro h
  have hsub : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
    have hτ := hgen τ
    rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hτ
    exact hτ
  haveI : Subsingleton (L ≃ₐ[K] L) := ⟨fun a b => by rw [hsub a, hsub b]⟩
  have hcard := IsGalois.card_aut_eq_finrank K L
  rw [Nat.card_of_subsingleton (1 : L ≃ₐ[K] L)] at hcard
  exact Nat.not_prime_one (hcard ▸ hdeg)

theorem isOrbitalIntegral_smul (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (I c : ℂ) (hc : c ≠ 0)
    (h : IsOrbitalIntegral K v γ τ f I) : IsOrbitalIntegral K v γ τ (c • f) (c * I) := by
  obtain ⟨w, ⟨h1, h2, h3, h4⟩, hI⟩ := h
  refine ⟨w, ⟨h1, h2, h3, fun x hx => h4 x ?_⟩, ?_⟩
  · intro h0
    apply hx
    simp [Pi.smul_apply, h0]
  · rw [hI, ← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem isLocalTestFn_smul (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (c : ℂ) (h : IsLocalTestFn K v f) : IsLocalTestFn K v (c • f) :=
  ⟨h.1.comp (fun y : ℂ => c • y), h.2.comp_left (g := fun y : ℂ => c • y) (smul_zero _)⟩

end IPACK

namespace IPACK

open AutomorphicForm

theorem isOrbitalIntegralOn_smul {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (I c : ℂ) (hc : c ≠ 0)
    (h : IsOrbitalIntegralOn A μ γ τ f I) : IsOrbitalIntegralOn A μ γ τ (c • f) (c * I) := by
  obtain ⟨w, ⟨h1, h2, h3, h4⟩, hI⟩ := h
  refine ⟨w, ⟨h1, h2, h3, fun x hx => h4 x ?_⟩, ?_⟩
  · intro h0
    apply hx
    simp [Pi.smul_apply, h0]
  · rw [hI, ← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

open scoped TensorProduct.RightActions in
theorem isTwistedOrbitalIntegralOn_smul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I c : ℂ) (hc : c ≠ 0)
    (h : IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (c • φ) (c * I) := by
  obtain ⟨w, ⟨h1, h2, h3, h4⟩, hI⟩ := h
  refine ⟨w, ⟨h1, h2, h3, fun x hx => h4 x ?_⟩, ?_⟩
  · intro h0
    apply hx
    simp [Pi.smul_apply, h0]
  · rw [hI, ← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

open scoped TensorProduct.RightActions in
theorem areMatchingOn_smul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (μK : @Measure (GL (Fin 2) A) (glBorelOf A))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (f : GL (Fin 2) A → ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : AreMatchingOn K L A σ μL μK φ f) : AreMatchingOn K L A σ μL μK (c • φ) (c • f) := by
  refine ⟨fun δ hδ γ hγ y hy τ τ' hτ hτ' hC I I' hI' hI => ?_, fun γ hγ hn τ hτ I hI => ?_⟩
  · have hI'0 := isTwistedOrbitalIntegralOn_smul K L σ μL δ τ' (c • φ) I' c⁻¹ (inv_ne_zero hc) hI'
    have hI0 := isOrbitalIntegralOn_smul μK γ τ (c • f) I c⁻¹ (inv_ne_zero hc) hI
    rw [inv_smul_smul₀ hc] at hI'0 hI0
    have e := h.1 δ hδ γ hγ y hy τ τ' hτ hτ' hC _ _ hI'0 hI0
    exact mul_left_cancel₀ (inv_ne_zero hc) e
  · have hI0 := isOrbitalIntegralOn_smul μK γ τ (c • f) I c⁻¹ (inv_ne_zero hc) hI
    rw [inv_smul_smul₀ hc] at hI0
    have e := h.2 γ hγ hn τ hτ _ hI0
    rcases mul_eq_zero.mp e with h0 | h0
    · exact absurd h0 (inv_ne_zero hc)
    · exact h0

open scoped Classical in
theorem isArchTestFactor_smul (F : Type) [Field F] [NumberField F] (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (c : ℂ) (h : IsArchTestFactor F fa) : IsArchTestFactor F (c • fa) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hc⟩ := h
  refine ⟨⟨c • Φ, hΦ.const_smul c, fun g => ?_⟩, hc.comp_left (g := fun y : ℂ => c • y) (smul_zero _)⟩
  simp only [Pi.smul_apply, hfa g]

open scoped TensorProduct.RightActions in
theorem isSemiLocalTestFn_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (f : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (c : ℂ)
    (h : IsSemiLocalTestFn K L v f) : IsSemiLocalTestFn K L v (c • f) :=
  ⟨h.1.comp (fun y : ℂ => c • y), h.2.comp_left (g := fun y : ℂ => c • y) (smul_zero _)⟩

theorem areMatchingArch_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (c : ℂ) (hc : c ≠ 0) (h : AreMatchingArch K L σ φa fa) : AreMatchingArch K L σ (c • φa) (c • fa) :=
  areMatchingOn_smul K L σ _ _ _ _ c hc h

theorem areMatchingLocal_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (fv : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (c : ℂ) (hc : c ≠ 0) (h : AreMatchingLocal K L v σ φv fv) : AreMatchingLocal K L v σ (c • φv) (c • fv) :=
  areMatchingOn_smul K L σ _ _ _ _ c hc h

theorem zero_factor_L (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (h : IsSemiLocalFactorization K L S φ φa φf Φ) (h0 : ∀ g, φ g = 0) :
    (∀ a, φa a = 0) ∨ ∃ v ∈ S, ∀ x, Φ v x = 0 := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha⟩, hS⟩ := hc
  choose x hx using fun v : HeightOneSpectrum (𝓞 K) => fun hv : v ∈ S => hS v hv
  obtain ⟨g, hga, hgS, hgint⟩ := AutomorphicForm.exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet K L S a (fun v => if hv : v ∈ S then x v hv else 1)
  have h1 := h.2.2.2.2.2 g
  rw [h0 g, hga, h.2.2.2.1 _ hgint] at h1
  refine absurd h1.symm (mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr fun v hv => ?_))
  rw [hgS v hv]
  simpa [hv] using hx v hv

theorem zero_factor_K (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (h : IsUnitFactorization K S f fa ff Ψ) (h0 : ∀ g, f g = 0) :
    (∀ a, fa a = 0) ∨ ∃ v ∈ S, ∀ x, Ψ v x = 0 := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha⟩, hS⟩ := hc
  choose x hx using fun v : HeightOneSpectrum (𝓞 K) => fun hv : v ∈ S => hS v hv
  obtain ⟨g, hga, hgS, hgint⟩ := AutomorphicForm.exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet K S a (fun v => if hv : v ∈ S then x v hv else 1)
  have h1 := h.2.2.2.2.2 g
  rw [h0 g, hga, h.2.2.2.1 _ hgint] at h1
  refine absurd h1.symm (mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr fun v hv => ?_))
  rw [hgS v hv]
  simpa [hv] using hx v hv

theorem isLocalTestFn_finset_sum (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → GL (Fin 2) (v.adicCompletion K) → ℂ)
    (h : ∀ i ∈ s, IsLocalTestFn K v (g i)) : IsLocalTestFn K v (fun x => ∑ i ∈ s, g i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using isLocalTestFn_zero K v
  | @insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    exact ⟨h1.1.comp₂ h2.1 (· + ·), h1.2.add h2.2⟩

theorem regroup {ι : Type*} [DecidableEq ι] {α : ι → Type*} {R : Type*}
    (SK T : Finset ι) (hd : Disjoint T SK)
    (supp : ι → Finset R) (coef : ι → R → ℂ) (Wd : ∀ v, R → α v → ℂ) (A : ∀ v, α v → ℂ)
    (y : ∀ v, α v) (a : ℂ) :
    ∑ m ∈ T.pi supp, (∏ v ∈ T.attach, coef v.1 (m v.1 v.2)) *
        (a * ∏ v ∈ SK ∪ T, (if hv : v ∈ T then Wd v (m v hv) else A v) (y v))
      = a * ∏ v ∈ SK ∪ T, (if v ∈ T then (fun x => ∑ r ∈ supp v, coef v r * Wd v r x) else A v) (y v) := by
  rw [Finset.prod_union hd.symm]
  have eA : ∏ v ∈ SK, (if v ∈ T then (fun x => ∑ r ∈ supp v, coef v r * Wd v r x) else A v) (y v) =
      ∏ v ∈ SK, A v (y v) :=
    Finset.prod_congr rfl fun v hv => by simp [Finset.disjoint_right.mp hd hv]
  have eT : ∏ v ∈ T, (if v ∈ T then (fun x => ∑ r ∈ supp v, coef v r * Wd v r x) else A v) (y v) =
      ∏ v ∈ T, ∑ r ∈ supp v, coef v r * Wd v r (y v) :=
    Finset.prod_congr rfl fun v hv => by simp [hv]
  rw [eA, eT, Finset.prod_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.prod_union hd.symm]
  have eA' : ∏ v ∈ SK, (if hv : v ∈ T then Wd v (m v hv) else A v) (y v) = ∏ v ∈ SK, A v (y v) :=
    Finset.prod_congr rfl fun v hv => by simp [Finset.disjoint_right.mp hd hv]
  have eT' : ∏ v ∈ T, (if hv : v ∈ T then Wd v (m v hv) else A v) (y v) =
      ∏ v ∈ T.attach, Wd v.1 (m v.1 v.2) (y v.1) := by
    rw [← Finset.prod_attach T (fun v => (if hv : v ∈ T then Wd v (m v hv) else A v) (y v))]
    exact Finset.prod_congr rfl fun v _ => by simp [v.2]
  rw [eA', eT', Finset.prod_mul_distrib]
  ring

theorem unitFactorization_comb (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTdisj : Disjoint T SK)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, IsLocalTestFn K v (fSK v))
    (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hfam : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
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
        ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)) :
    ∃ (ffF : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
      (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      IsUnitFactorization K (SK ∪ T) (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
              SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x) faK ffF fS ∧ (∀ v ∈ SK, fS v = fSK v) ∧
      ∀ v ∈ T, fS v = (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) := by
  classical
  have hKCt : ∀ v ∈ T, IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) := by
    intro v _
    refine isLocalTestFn_finset_sum K v _ (fun r x => (fun (v : HeightOneSpectrum (𝓞 K)) (r : Fin 2 →₀ ℕ) =>
        (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v)) v r * (fun (v : HeightOneSpectrum (𝓞 K)) (r : Fin 2 →₀ ℕ) (x : GL (Fin 2) (v.adicCompletion K)) =>
        ∑ ι : Fin (r 0) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) v r x) fun r _ => ?_
    exact isLocalTestFn_smul K v _ _
      (AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v (nKs v) (rKs v) (zKs v) (r 0) (r 1))
  have hfS : ∀ v ∈ SK ∪ T, IsLocalTestFn K v ((fun v => if v ∈ T then (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) else fSK v) v) := by
    intro v hv
    by_cases hvT : v ∈ T
    · simpa [hvT] using hKCt v hvT
    · simpa [hvT] using hfSK v ((Finset.mem_union.mp hv).resolve_right hvT)
  obtain ⟨f₀, ffF, -, -, hf₀, -⟩ :=
    AutomorphicForm.exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn K (SK ∪ T) faK hfaK (fun v => if v ∈ T then (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) else fSK v) hfS
  choose ffm hffm using hfam
  refine ⟨ffF, fun v => if v ∈ T then (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) else fSK v,
    ⟨hfaK, hf₀.2.1, hfS, hf₀.2.2.2.1, hf₀.2.2.2.2.1, fun g => ?_⟩,
    fun v hv => by simp [Finset.disjoint_right.mp hTdisj hv], fun v hv => by simp [hv]⟩
  by_cases hint : ∀ v ∉ SK ∪ T,
      AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ localIntegralSet K v
  · rw [hf₀.2.2.2.1 _ hint]
    have e1 : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m g =
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            (faK (AdelicLevel.glArch (𝓞 K) K g) * ∏ v ∈ SK ∪ T,
              (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                  ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                    (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                      (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                else fSK v) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) :=
      fun m hm => by rw [(hffm m hm).2.2.2 g, (hffm m hm).2.1 _ hint]
    show (∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m g) = _
    rw [Finset.sum_congr rfl e1]
    unfold SatakeCombination.slotIndex SatakeCombination.slotFamilyCoeff SatakeCombination.slotCoeff
      SatakeCombination.slotWord SatakeCombination.slotDeg
    exact IPACK.regroup SK T hTdisj (fun (v : HeightOneSpectrum (𝓞 K)) => (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support) (fun (v : HeightOneSpectrum (𝓞 K)) (r : Fin 2 →₀ ℕ) =>
        (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v)) (fun (v : HeightOneSpectrum (𝓞 K)) (r : Fin 2 →₀ ℕ) (x : GL (Fin 2) (v.adicCompletion K)) =>
        ∑ ι : Fin (r 0) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) fSK
      (fun v => AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g)) (faK (AdelicLevel.glArch (𝓞 K) K g))
  · push Not at hint
    rw [hf₀.2.2.2.2.1 _ hint, mul_zero]
    show (∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m g) = 0
    exact Finset.sum_eq_zero fun m hm => by
      rw [(hffm m hm).2.2.2 g, (hffm m hm).2.2.1 _ hint, mul_zero, mul_zero]

open scoped TensorProduct.RightActions in

theorem word_place_facts (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (w : v.Extension (𝓞 L))
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (WLf : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (KCf : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hWLf : WLf = (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
              ((List.ofFn fun m => rT (ι m)).prod * z ^ j)))⁻¹ * x)))
    (hKCf : KCf = (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' w.1.asIdeal - 1) k j).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' w.1.asIdeal - 1) k j).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm w.1.asIdeal : ℂ) ^ j *
            ∑ ι : Fin (r 0) → Fin nK,
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (r 1))⁻¹ * x)))
    (hBC : IsSemiLocalTestFn K L v WLf)
    (hKC : IsLocalTestFn K v KCf) :
    (∀ ρ : ℂ, ρ ≠ 0 → AreMatchingLocal K L v σ WLf (ρ • KCf) → ρ = 1) ∧
    (∀ d : ℂ, AreMatchingLocal K L v σ (fun _ => 0) (d • KCf) → d = 0) ∧
    (∀ c : ℂ, AreMatchingLocal K L v σ (c • WLf) (fun _ => 0) → c = 0) ∧
    (∃ x, WLf x ≠ 0) ∧ (∃ x, KCf x ≠ 0) := by
  subst hWLf hKCf
  obtain ⟨a, b, α, β, τ, τ', I, I', hab, hN, hτ, hτ1, hτ', hτ'1, hI, hI', hI0, hII⟩ :=
    AutomorphicForm.exists_diagUnits2_normString_isOrbitalIntegral_ne_zero_isTwistedOrbitalIntegral_eq_heckeWord_of_ramificationIdx_eq_one_of_prime
      K L hdeg σ hσ v hv w ϖ hϖ hϖ0 n rT hrT z hz ϖK hϖK hϖK0 nK rK hrK zK hzK k j
  have hI'0 : I' ≠ 0 := hII ▸ hI0
  refine ⟨fun ρ hρ hm => ?_, fun d hm => ?_, fun c hm => ?_, ?_, ?_⟩
  · have hIρ := isOrbitalIntegral_smul K v _ τ _ I ρ hρ hI
    have key := AutomorphicForm.eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime
      K L σ hgen hdeg hσ v _ hBC _ (isLocalTestFn_smul K v _ ρ hKC) hm a b hab α β hN τ hτ hτ1 τ' hτ' hτ'1 (ρ * I) I' hIρ hI'
    have h1 : ρ * I = 1 * I := by rw [one_mul, ← key, hII]
    exact mul_right_cancel₀ hI0 h1
  · by_contra hd
    have hId := isOrbitalIntegral_smul K v _ τ _ I d hd hI
    have key := AutomorphicForm.eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime
      K L σ hgen hdeg hσ v _ (isSemiLocalTestFn_zero K L v) _ (isLocalTestFn_smul K v _ d hKC) hm a b hab α β hN τ hτ hτ1 τ' hτ' hτ'1
      (d * I) 0 hId (isTwistedOrbitalIntegral_zero K L v σ _ τ')
    exact mul_ne_zero hd hI0 key.symm
  · by_contra hc
    have hIc : IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' (c • (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
              ((List.ofFn fun m => rT (ι m)).prod * z ^ j)))⁻¹ * x))) (c * I') :=
      isTwistedOrbitalIntegralOn_smul K L σ _ _ τ' _ I' c hc hI'
    have hI0' : IsOrbitalIntegral K v (diagUnits2 a b) τ (fun _ => (0 : ℂ)) 0 :=
      ⟨fun _ => 0, isSectionFn_zero K v _ τ, by simp⟩
    have key := AutomorphicForm.eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime
      K L σ hgen hdeg hσ v _ (isSemiLocalTestFn_smul K L v _ c hBC) _ (isLocalTestFn_zero K v) hm a b hab α β hN τ hτ hτ1 τ' hτ' hτ'1
      0 (c * I') hI0' hIc
    exact mul_ne_zero hc hI'0 key
  · by_contra h0
    push Not at h0
    obtain ⟨w', -, hw'⟩ := hI'
    apply hI'0
    rw [hw']
    simp only [h0, zero_mul, integral_zero]
  · by_contra h0
    push Not at h0
    obtain ⟨w', -, hw'⟩ := hI
    apply hI0
    rw [hw']
    simp only [h0, zero_mul, integral_zero]

theorem partners_of_word (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTdisj : Disjoint T SK)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (WL : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (KC : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (φL : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hSLF : IsSemiLocalFactorization K L (SK ∪ T) φL φa φf (fun v => if v ∈ T then WL v else φS v))
    (F : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (ffF : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hF : IsUnitFactorization K (SK ∪ T) F faK ffF fS)
    (hfS : ∀ v ∈ SK, fS v = fSK v) (hfT : ∀ v ∈ T, fS v = KC v)
    (hm : AreMatchingAt K L σ (SK ∪ T) φL F)
    (WPF : ∀ v ∈ T,
      (∀ ρ : ℂ, ρ ≠ 0 → AreMatchingLocal K L v σ (WL v) (ρ • KC v) → ρ = 1) ∧
      (∀ d : ℂ, AreMatchingLocal K L v σ (fun _ => 0) (d • KC v) → d = 0) ∧
      (∀ c : ℂ, AreMatchingLocal K L v σ (c • WL v) (fun _ => 0) → c = 0) ∧
      (∃ x, WL v x ≠ 0) ∧ (∃ x, KC v x ≠ 0)) :
    ∃ (φa' : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
      (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
      (fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (fS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      IsArchTestFactor L φa' ∧ (∀ v ∈ SK, IsSemiLocalTestFn K L v (φS' v)) ∧
      IsArchTestFactor K fa' ∧ (∀ v ∈ SK, IsLocalTestFn K v (fS' v)) ∧
      AreMatchingArch K L σ φa' fa' ∧ (∀ v ∈ SK, AreMatchingLocal K L v σ (φS' v) (fS' v)) ∧
      (∀ (a : GL (Fin 2) (InfiniteAdeleRing L))
        (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        φa' a * ∏ v ∈ SK, φS' v (x v) = φa a * ∏ v ∈ SK, φS v (x v)) ∧
      (∀ (a : GL (Fin 2) (InfiniteAdeleRing K)) (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        fa' a * ∏ v ∈ SK, fS' v (x v) = faK a * ∏ v ∈ SK, fSK v (x v)) := by
  classical
  have R1 : ∀ v ∈ T, ∀ ρ : ℂ, ρ ≠ 0 → AreMatchingLocal K L v σ (WL v) (ρ • KC v) → ρ = 1 := fun v hv => (WPF v hv).1
  have R2 : ∀ v ∈ T, ∀ d : ℂ, AreMatchingLocal K L v σ (fun _ => 0) (d • KC v) → d = 0 := fun v hv => (WPF v hv).2.1
  have R3 : ∀ v ∈ T, ∀ c : ℂ, AreMatchingLocal K L v σ (c • WL v) (fun _ => 0) → c = 0 := fun v hv => (WPF v hv).2.2.1
  have hWL0 : ∀ v ∈ T, ∃ x, WL v x ≠ 0 := fun v hv => (WPF v hv).2.2.2.1
  have hKC0 : ∀ v ∈ T, ∃ x, KC v x ≠ 0 := fun v hv => (WPF v hv).2.2.2.2
  have hφS : ∀ v ∈ SK, IsSemiLocalTestFn K L v (φS v) := by
    intro v hv
    have hvT : v ∉ T := Finset.disjoint_right.mp hTdisj hv
    simpa [hvT] using hSLF.2.2.1 v (Finset.mem_union_left T hv)
  have hfSK : ∀ v ∈ SK, IsLocalTestFn K v (fSK v) := by
    intro v hv
    rw [← hfS v hv]
    exact hF.2.2.1 v (Finset.mem_union_left T hv)
  by_cases hφL0 : ∃ g, φL g ≠ 0
  · by_cases hF0 : ∃ g, F g ≠ 0
    ·
      obtain ⟨ρa, ρ, hρa0, hρ0, hprod, hfaK', hfS', hmA, hmS⟩ :=
        AutomorphicForm.exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
          K L σ (SK ∪ T) φL φa φf _ hSLF F faK ffF fS hF hm hφL0 hF0
      have hpin : ∀ v ∈ T, ρ v = 1 := by
        intro v hv
        have hvU : v ∈ SK ∪ T := Finset.mem_union_right SK hv
        refine R1 v hv (ρ v) (hρ0 v hvU) ?_
        have h := hmS v hvU
        rw [hfT v hv] at h
        simpa [hv] using h
      have hT1 : ∏ v ∈ T, ρ v = 1 := Finset.prod_eq_one fun v hv => hpin v hv
      rw [Finset.prod_union hTdisj.symm, hT1, mul_one] at hprod
      refine ⟨φa, φS, ρa • faK, fun v => ρ v • fSK v, hSLF.1, hφS, hfaK', ?_, hmA, ?_, fun a x => rfl, ?_⟩
      · intro v hv
        beta_reduce
        rw [← hfS v hv]
        exact hfS' v (Finset.mem_union_left T hv)
      · intro v hv
        have hvT : v ∉ T := Finset.disjoint_right.mp hTdisj hv
        have h := hmS v (Finset.mem_union_left T hv)
        rw [hfS v hv] at h
        simpa [hvT] using h
      · intro a x
        simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
        linear_combination (faK a * ∏ v ∈ SK, fSK v (x v)) * hprod
    ·
      have hF00 : ∀ g, F g = 0 := by simpa using hF0
      obtain ⟨φa₁, φf₁, φS₁, fa₁, ff₁, fS₁, hφ₁, hf₁, hmA₁, hmS₁⟩ := hm
      obtain ⟨ca, c, hca, hc, -, hφa₁, hφS₁⟩ :=
        AutomorphicForm.exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero K L (SK ∪ T) φL φa φf _ hSLF φa₁ φf₁ φS₁ hφ₁ hφL0
      have hz₁ := zero_factor_K K (SK ∪ T) F fa₁ ff₁ fS₁ hf₁ hF00
      have hzK := zero_factor_K K (SK ∪ T) F faK ffF fS hF hF00

      have hz₁' : (∀ a, fa₁ a = 0) ∨ ∃ v ∈ SK, ∀ x, fS₁ v x = 0 := by
        rcases hz₁ with h | ⟨v, hv, h⟩
        · exact Or.inl h
        · rcases Finset.mem_union.mp hv with hvS | hvT
          · exact Or.inr ⟨v, hvS, h⟩
          · exfalso
            have hm1 := hmS₁ v hv
            rw [hφS₁ v hv, show fS₁ v = fun _ => 0 from funext h] at hm1
            have : c v = 0 := R3 v hvT (c v) (by simpa [hvT] using hm1)
            exact hc v hv this
      have hzK' : (∀ a, faK a = 0) ∨ ∃ v ∈ SK, ∀ x, fSK v x = 0 := by
        rcases hzK with h | ⟨v, hv, h⟩
        · exact Or.inl h
        · rcases Finset.mem_union.mp hv with hvS | hvT
          · exact Or.inr ⟨v, hvS, fun x => by rw [← hfS v hvS]; exact h x⟩
          · exfalso
            obtain ⟨x, hx⟩ := hKC0 v hvT
            exact hx (by rw [← hfT v hvT]; exact h x)
      refine ⟨φa, φS, ca⁻¹ • fa₁, fun v => (c v)⁻¹ • fS₁ v, hSLF.1, hφS,
        isArchTestFactor_smul K _ _ hf₁.1, ?_, ?_, ?_, fun a x => rfl, ?_⟩
      · intro v hv
        exact isLocalTestFn_smul K v _ _ (hf₁.2.2.1 v (Finset.mem_union_left T hv))
      · have h := areMatchingArch_smul K L σ _ _ ca⁻¹ (inv_ne_zero hca) (hφa₁ ▸ hmA₁)
        rwa [inv_smul_smul₀ hca] at h
      · intro v hv
        have hvT : v ∉ T := Finset.disjoint_right.mp hTdisj hv
        have hvU : v ∈ SK ∪ T := Finset.mem_union_left T hv
        have h0 := hmS₁ v hvU
        rw [hφS₁ v hvU] at h0
        have h := areMatchingLocal_smul K L v σ _ _ (c v)⁻¹ (inv_ne_zero (hc v hvU)) h0
        rw [inv_smul_smul₀ (hc v hvU)] at h
        simpa [hvT] using h
      · intro a x
        have hR : faK a * ∏ v ∈ SK, fSK v (x v) = 0 := by
          rcases hzK' with h | ⟨v, hv, h⟩
          · rw [h a, zero_mul]
          · rw [Finset.prod_eq_zero hv (h (x v)), mul_zero]
        have hL : (ca⁻¹ • fa₁) a * ∏ v ∈ SK, ((fun v => (c v)⁻¹ • fS₁ v) v) (x v) = 0 := by
          rcases hz₁' with h | ⟨v, hv, h⟩
          · simp [Pi.smul_apply, h a]
          · rw [Finset.prod_eq_zero hv (by simp [Pi.smul_apply, h (x v)]), mul_zero]
        rw [hL, hR]
  ·
    have hφL00 : ∀ g, φL g = 0 := by simpa using hφL0
    have hzΦ := zero_factor_L K L (SK ∪ T) φL φa φf _ hSLF hφL00
    have hzΦ' : (∀ a, φa a = 0) ∨ ∃ v ∈ SK, ∀ x, φS v x = 0 := by
      rcases hzΦ with h | ⟨v, hv, h⟩
      · exact Or.inl h
      · rcases Finset.mem_union.mp hv with hvS | hvT
        · refine Or.inr ⟨v, hvS, fun x => ?_⟩
          have hvT : v ∉ T := Finset.disjoint_right.mp hTdisj hvS
          simpa [hvT] using h x
        · exfalso
          obtain ⟨x, hx⟩ := hWL0 v hvT
          exact hx (by simpa [hvT] using h x)
    have hRφ : ∀ (a : GL (Fin 2) (InfiniteAdeleRing L))
        (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        φa a * ∏ v ∈ SK, φS v (x v) = 0 := by
      intro a x
      rcases hzΦ' with h | ⟨v, hv, h⟩
      · rw [h a, zero_mul]
      · rw [Finset.prod_eq_zero hv (h (x v)), mul_zero]
    by_cases hF0 : ∃ g, F g ≠ 0
    ·
      obtain ⟨φa₁, φf₁, φS₁, fa₁, ff₁, fS₁, hφ₁, hf₁, hmA₁, hmS₁⟩ := hm
      obtain ⟨da, d, hda, hd, -, hfa₁, hfS₁⟩ :=
        AutomorphicForm.exists_smul_eq_of_isUnitFactorization_of_isUnitFactorization_of_exists_ne_zero K (SK ∪ T) F faK ffF fS hF fa₁ ff₁ fS₁ hf₁ hF0
      have hz₁ := zero_factor_L K L (SK ∪ T) φL φa₁ φf₁ φS₁ hφ₁ hφL00
      have hz₁' : (∀ a, φa₁ a = 0) ∨ ∃ v ∈ SK, ∀ x, φS₁ v x = 0 := by
        rcases hz₁ with h | ⟨v, hv, h⟩
        · exact Or.inl h
        · rcases Finset.mem_union.mp hv with hvS | hvT
          · exact Or.inr ⟨v, hvS, h⟩
          · exfalso
            have hm1 := hmS₁ v hv
            rw [hfS₁ v hv, hfT v hvT, show φS₁ v = fun _ => 0 from funext h] at hm1
            exact hd v hv (R2 v hvT (d v) hm1)
      refine ⟨da⁻¹ • φa₁, fun v => (d v)⁻¹ • φS₁ v, faK, fSK,
        isArchTestFactor_smul L _ _ hφ₁.1, ?_, hF.1, hfSK, ?_, ?_, ?_, fun a x => rfl⟩
      · intro v hv
        exact isSemiLocalTestFn_smul K L v _ _ (hφ₁.2.2.1 v (Finset.mem_union_left T hv))
      · have h := areMatchingArch_smul K L σ _ _ da⁻¹ (inv_ne_zero hda) (hfa₁ ▸ hmA₁)
        rwa [inv_smul_smul₀ hda] at h
      · intro v hv
        have hvU : v ∈ SK ∪ T := Finset.mem_union_left T hv
        have h0 := hmS₁ v hvU
        rw [hfS₁ v hvU, hfS v hv] at h0
        have h := areMatchingLocal_smul K L v σ _ _ (d v)⁻¹ (inv_ne_zero (hd v hvU)) h0
        rwa [inv_smul_smul₀ (hd v hvU)] at h
      · intro a x
        have hL : (da⁻¹ • φa₁) a * ∏ v ∈ SK, ((fun v => (d v)⁻¹ • φS₁ v) v) (x v) = 0 := by
          rcases hz₁' with h | ⟨v, hv, h⟩
          · simp [Pi.smul_apply, h a]
          · rw [Finset.prod_eq_zero hv (by simp [Pi.smul_apply, h (x v)]), mul_zero]
        rw [hL, hRφ]
    ·
      have hF00 : ∀ g, F g = 0 := by simpa using hF0
      have hzK := zero_factor_K K (SK ∪ T) F faK ffF fS hF hF00
      have hzK' : (∀ a, faK a = 0) ∨ ∃ v ∈ SK, ∀ x, fSK v x = 0 := by
        rcases hzK with h | ⟨v, hv, h⟩
        · exact Or.inl h
        · rcases Finset.mem_union.mp hv with hvS | hvT
          · exact Or.inr ⟨v, hvS, fun x => by rw [← hfS v hvS]; exact h x⟩
          · exfalso
            obtain ⟨x, hx⟩ := hKC0 v hvT
            exact hx (by rw [← hfT v hvT]; exact h x)
      refine ⟨fun _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0, isArchTestFactor_zero L,
        fun v _ => isSemiLocalTestFn_zero K L v, isArchTestFactor_zero K, fun v _ => isLocalTestFn_zero K v,
        areMatchingArch_zero K L σ, fun v _ => areMatchingLocal_zero K L v σ, ?_, ?_⟩
      · intro a x
        rw [zero_mul, hRφ]
      · intro a x
        rw [zero_mul]
        rcases hzK' with h | ⟨v, hv, h⟩
        · rw [h a, zero_mul]
        · rw [Finset.prod_eq_zero hv (h (x v)), mul_zero]

end IPACK

open LanglandsTunnell.CubicInduction (diagUnits2)

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
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

    (hξinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ.symm z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (hfaK : IsArchTestFactor K faK)
    (hfSK : ∀ v ∈ SK, IsLocalTestFn K v (fSK v))
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

  by_cases H : ∃ (φa' : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
      (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
      (fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (fS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      IsArchTestFactor L φa' ∧ (∀ v ∈ SK, IsSemiLocalTestFn K L v (φS' v)) ∧
      IsArchTestFactor K fa' ∧ (∀ v ∈ SK, IsLocalTestFn K v (fS' v)) ∧
      AreMatchingArch K L σ.symm φa' fa' ∧ (∀ v ∈ SK, AreMatchingLocal K L v σ.symm (φS' v) (fS' v)) ∧
      (∀ (a : GL (Fin 2) (InfiniteAdeleRing L))
        (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        φa' a * ∏ v ∈ SK, φS' v (x v) = φa a * ∏ v ∈ SK, φS v (x v)) ∧
      (∀ (a : GL (Fin 2) (InfiniteAdeleRing K)) (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        fa' a * ∏ v ∈ SK, fS' v (x v) = faK a * ∏ v ∈ SK, fSK v (x v))
  · obtain ⟨φa', φS', fa', fS', hφa', hφS', hfaK', hfSK', hmA, hmS, hCφ, hCf⟩ := H

    obtain ⟨lam, hlam0, hhex, hrest⟩ := AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL
      φa' φS' fa' fS' X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
      hξinv hfaK' hfSK' hφa' hφS' hmA hmS hur
    refine ⟨lam, hlam0, hhex, ?_⟩
    intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs s hs
    obtain ⟨ℬ, hℬ⟩ := hrest T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs s hs
    refine ⟨ℬ, ?_⟩
    intro ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch AL BL AK BK R₀ hSP

    have hΦ' : ∀ v ∈ SK ∪ T, IsSemiLocalTestFn K L v ((fun v => if v ∈ T then (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)) else φS' v) v) := by
      intro v hv
      by_cases hvT : v ∈ T
      · simpa [hvT] using hSLF.2.2.1 v hv
      · simpa [hvT] using hφS' v ((Finset.mem_union.mp hv).resolve_right hvT)
    obtain ⟨φ₀, φf', -, -, hφ₀, -⟩ := AutomorphicForm.exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn K L (SK ∪ T) φa' hφa' (fun v => if v ∈ T then (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)) else φS' v) hΦ'
    have hSLF' : IsSemiLocalFactorization K L (SK ∪ T) φL φa' φf' (fun v => if v ∈ T then (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)) else φS' v) := by
      refine ⟨hφ₀.1, hφ₀.2.1, hφ₀.2.2.1, hφ₀.2.2.2.1, hφ₀.2.2.2.2.1, fun g => ?_⟩
      rw [hSLF.2.2.2.2.2 g]
      by_cases hint : ∀ v ∉ SK ∪ T, semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v
      · rw [hSLF.2.2.2.1 _ hint, hφ₀.2.2.2.1 _ hint]
        exact (IPACK.mul_prod_ite_union_eq SK T hTdisj (fun v => (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x))) φS φS'
          (fun v => semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g))
          (φa (AdelicLevel.glArch (𝓞 L) L g)) (φa' (AdelicLevel.glArch (𝓞 L) L g)) (hCφ _ _)).symm
      · push Not at hint
        rw [hSLF.2.2.2.2.1 _ hint, hφ₀.2.2.2.2.1 _ hint, mul_zero, mul_zero]
    refine hℬ ks js φL hφL hφLc φf' hSLF' hbi harch fam ?_ hmatch AL BL AK BK R₀ hSP

    intro m hm
    obtain ⟨hbiK, harchK, -, -, ff, hffin, hffeq, hff0, hfam_eq⟩ := hfam m hm
    have hΨ' : ∀ v ∈ SK ∪ T, IsLocalTestFn K v ((fun v => if hv : v ∈ T then (fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) else fS' v) v) := by
      intro v hv
      by_cases hvT : v ∈ T
      · simpa [hvT] using AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v (nKs v) (rKs v) (zKs v) ((m v hvT) 0) ((m v hvT) 1)
      · simpa [hvT] using hfSK' v ((Finset.mem_union.mp hv).resolve_right hvT)
    obtain ⟨f₀, ff', -, -, hf₀, -⟩ := AutomorphicForm.exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn K (SK ∪ T) fa' hfaK' (fun v => if hv : v ∈ T then (fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) else fS' v) hΨ'
    refine ⟨hbiK, harchK, hfaK', hfSK', ff', hf₀.2.1, hf₀.2.2.2.1, hf₀.2.2.2.2.1, fun g => ?_⟩
    rw [hfam_eq g]
    by_cases hint : ∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ localIntegralSet K v
    · rw [hffeq _ hint, hf₀.2.2.2.1 _ hint]
      exact (IPACK.mul_prod_dite_union_eq SK T hTdisj (fun v hv => (fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x))) fSK fS'
        (fun v => AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))
        (faK (AdelicLevel.glArch (𝓞 K) K g)) (fa' (AdelicLevel.glArch (𝓞 K) K g)) (hCf _ _)).symm
    · push Not at hint
      rw [hff0 _ hint, hf₀.2.2.2.2.1 _ hint, mul_zero, mul_zero]
  ·

    obtain ⟨lam0, hlam0, hhex0, -⟩ := AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL
      (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => 0) X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
      hξinv (AutomorphicForm.isArchTestFactor_zero K) (fun v _ => AutomorphicForm.isLocalTestFn_zero K v)
      (AutomorphicForm.isArchTestFactor_zero L) (fun v _ => AutomorphicForm.isSemiLocalTestFn_zero K L v)
      (AutomorphicForm.areMatchingArch_zero K L σ.symm) (fun v _ => AutomorphicForm.areMatchingLocal_zero K L v σ.symm) hur
    refine ⟨lam0, hlam0, hhex0, ?_⟩
    intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs s hs

    have hTne : T.card ≠ 0 := by omega
    refine ⟨IPACK.zero _ _ _ hTne, ?_⟩
    intro ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch AL BL AK BK R₀ hSP
    exfalso
    apply H

    have hFfac : ∃ (ffF : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        IsUnitFactorization K (SK ∪ T) (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
              SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x) faK ffF fS ∧ (∀ v ∈ SK, fS v = fSK v) ∧
        ∀ v ∈ T, fS v = (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) :=
      IPACK.unitFactorization_comb K L ws SK T hTdisj nKs rKs zKs ks js faK hfaK fSK hfSK fam
        (fun m hm => (hfam m hm).2.2.2.2)
    obtain ⟨ffF, fS, hF, hfS_eq, hfS_T⟩ := hFfac
    have hσ1 : σ.symm ≠ 1 := IPACK.ne_one_of_zpowers σ.symm hgen hdeg

    refine IPACK.partners_of_word K L σ.symm SK T hTdisj φa φS faK fSK (fun v => (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x))) (fun v => (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)))
      φL φf hSLF _ ffF fS hF hfS_eq hfS_T hmatch ?_
    intro v hv
    have hvS : v ∉ SK := Finset.disjoint_left.mp hTdisj hv
    have hvU : v ∈ SK ∪ T := Finset.mem_union_right SK hv
    have hvu : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1 :=
      fun w' hw' => hS w' (by rw [hw']; exact hvS)
    have hBC := hSLF.2.2.1 v hvU
    simp only [hv, if_true] at hBC
    have hKC := hF.2.2.1 v hvU
    rw [hfS_T v hv] at hKC
    exact IPACK.word_place_facts K L hdeg σ.symm hgen hσ1 v hvu (ws v) (ϖs v) (hϖirr v hv) (hϖs0 v hv)
      (ns v) (rTs v) (hrTs v hv) (zs v) (hzs v hv) (ϖKs v) (hϖKirr v hv) (hϖKs0 v hv) (nKs v) (rKs v) (hrKs v hv)
      (zKs v) (hzKs v hv) (ks v) (js v) _ _ rfl rfl hBC hKC

end S_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
end P2MW
export P2MW.S_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine (solution)
