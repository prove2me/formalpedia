-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ee8a1032-fa29-581e-b07d-6cc15f07a507

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_SemistableCovering_ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_smul_of_mem_riemannRochSpace_of_rankOne
import Theorems.Thm_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus~RegularProlongation"

namespace BDescK3Bridge

theorem mapDomain_filter_apply_eq_zero_of_mem_nodes
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (C : ComponentChart A F Fb) (D : Divisor L F) [DecidablePred fun P : Place L F => P ∈ C.dom]
    (x : Place (IsLocalRing.ResidueField ↥A) Fb) (hx : x ∈ C.nodes) :
    (Finsupp.mapDomain C.placeMap (D.filter fun P => P ∈ C.dom) : Divisor (IsLocalRing.ResidueField ↥A) Fb) x = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  show Finsupp.single (C.placeMap Q) _ x = 0
  rw [Finsupp.single_apply, if_neg]
  intro hQx
  have hQdom : Q ∈ C.dom := by
    rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hQ
    by_contra hnd; exact hQ (if_neg hnd)
  exact C.placeMap_not_mem_nodes Q hQdom (hQx ▸ hx)

theorem mem_riemannRochSpace_add_nodeDivisor_of_ord_clauses
    {κ : Type*} [Field κ] {n m : ℕ} (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)] [∀ i, Algebra κ (Fbar i)]
    (N : ∀ i, Finset (Place κ (Fbar i)))
    (src tgt : Fin m → Fin n) (xs : ∀ e, Place κ (Fbar (src e))) (xt : ∀ e, Place κ (Fbar (tgt e)))
    (hxs : ∀ e, xs e ∈ N (src e)) (hxt : ∀ e, xt e ∈ N (tgt e))
    (hN₁ : ∀ i, ∀ x ∈ N i, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place κ (Fbar j)) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, Place κ (Fbar j)) = ⟨i, x⟩)
    (hN₂ : ∀ i, ∀ x ∈ N i, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place κ (Fbar j))) (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place κ (Fbar j))) (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ →
          E = E')
    (Dbar : ∀ i, Divisor κ (Fbar i)) (hDbarN : ∀ i, ∀ x ∈ N i, Dbar i x = 0)
    (k : Fin m → ℤ)
    (h : ∀ i, Fbar i)
    (C1 : ∀ i, ∀ Q, Q ∉ N i → h i ≠ 0 → 0 ≤ Q.ord (h i) + Dbar i Q)
    (C2 : ∀ e, h (src e) ≠ 0 → k e ≤ (xs e).ord (h (src e)))
    (C3 : ∀ e, h (tgt e) ≠ 0 → -k e ≤ (xt e).ord (h (tgt e))) :
    ∀ i, h i ∈ riemannRochSpace (Dbar i +
      Finsupp.split (∑ e, (Finsupp.single (⟨src e, xs e⟩ : Σ j, Place κ (Fbar j)) (-k e) +
        Finsupp.single (⟨tgt e, xt e⟩ : Σ j, Place κ (Fbar j)) (k e))) i) := by
  classical
  have hss : ∀ e e', (⟨src e', xs e'⟩ : Σ j, Place κ (Fbar j)) = ⟨src e, xs e⟩ → e' = e := by
    intro e e' hh
    have := hN₂ _ _ (hxs e) (Sum.inl e') (Sum.inl e) hh rfl
    cases this; rfl
  have hts : ∀ e e', (⟨tgt e', xt e'⟩ : Σ j, Place κ (Fbar j)) ≠ ⟨src e, xs e⟩ := by
    intro e e' hh
    have := hN₂ _ _ (hxs e) (Sum.inr e') (Sum.inl e) hh rfl
    cases this
  have hst : ∀ e e', (⟨src e', xs e'⟩ : Σ j, Place κ (Fbar j)) ≠ ⟨tgt e, xt e⟩ := by
    intro e e' hh
    have := hN₂ _ _ (hxt e) (Sum.inl e') (Sum.inr e) hh rfl
    cases this
  have htt : ∀ e e', (⟨tgt e', xt e'⟩ : Σ j, Place κ (Fbar j)) = ⟨tgt e, xt e⟩ → e' = e := by
    intro e e' hh
    have := hN₂ _ _ (hxt e) (Sum.inr e') (Sum.inr e) hh rfl
    cases this; rfl
  set Kdiv : ∀ i, Divisor κ (Fbar i) := fun i =>
    Finsupp.split (∑ e, (Finsupp.single (⟨src e, xs e⟩ : Σ j, Place κ (Fbar j)) (-k e) +
      Finsupp.single (⟨tgt e, xt e⟩ : Σ j, Place κ (Fbar j)) (k e))) i with hKdiv
  have hKapply : ∀ i x, Kdiv i x = ∑ e, ((Finsupp.single (⟨src e, xs e⟩ : Σ j, Place κ (Fbar j)) (-k e) ⟨i, x⟩) +
      Finsupp.single (⟨tgt e, xt e⟩ : Σ j, Place κ (Fbar j)) (k e) ⟨i, x⟩) := by
    intro i x
    rw [hKdiv, Finsupp.split_apply, Finsupp.finsetSum_apply]
    rfl
  have hKs : ∀ e, Kdiv (src e) (xs e) = -k e := by
    intro e
    rw [hKapply, Finset.sum_eq_single e]
    · rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_neg (hts e e), add_zero]
    · intro e' _ hne
      rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (fun hh => hne (hss e e' hh)), if_neg (hts e e'), add_zero]
    · intro hh; exact absurd (Finset.mem_univ e) hh
  have hKt : ∀ e, Kdiv (tgt e) (xt e) = k e := by
    intro e
    rw [hKapply, Finset.sum_eq_single e]
    · rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (hst e e), if_pos rfl, zero_add]
    · intro e' _ hne
      rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (hst e e'), if_neg (fun hh => hne (htt e e' hh)), add_zero]
    · intro hh; exact absurd (Finset.mem_univ e) hh
  have hK0 : ∀ i x, x ∉ N i → Kdiv i x = 0 := by
    intro i x hx
    rw [hKapply]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [Finsupp.single_apply, Finsupp.single_apply, if_neg, if_neg, add_zero]
    · intro hh
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hh
      subst h1
      exact hx (eq_of_heq h2 ▸ hxt e)
    · intro hh
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hh
      subst h1
      exact hx (eq_of_heq h2 ▸ hxs e)
  intro i
  show h i ∈ riemannRochSpace (Dbar i + Kdiv i)
  rw [mem_riemannRochSpace_iff]
  intro v
  rcases eq_or_ne (h i) 0 with h0 | h0
  · exact Or.inl h0
  right
  rw [Finsupp.add_apply]
  by_cases hv : v ∈ N i
  · obtain ⟨e, he | he⟩ := hN₁ i v hv
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp he
      subst h1
      have hv' : xs e = v := eq_of_heq h2
      subst hv'
      rw [hDbarN _ _ (hxs e), hKs, zero_add, neg_neg]
      exact C2 e h0
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp he
      subst h1
      have hv' : xt e = v := eq_of_heq h2
      subst hv'
      rw [hDbarN _ _ (hxt e), hKt, zero_add]
      exact C3 e h0
  · rw [hK0 i v hv, add_zero]
    have := C1 i v hv h0
    omega

end BDescK3Bridge

open Classical in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hw1 : ∀ e, w e = 1)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (φ : Fin n → ℤ)
    (D : Divisor L F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom)
    (hdegD : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i)) +
      ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)))
    :
    let Dbar : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fbar i) := fun i =>
      Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom)
    let k : Fin m → ℤ := fun e => φ (tgt e) - φ (src e)
    let zs : ∀ e, Fbar (src e) := fun e => (C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩
    let zt : ∀ e, Fbar (tgt e) := fun e => (C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩
    let ubar : Fin m → IsLocalRing.ResidueField A := fun e => IsLocalRing.residue A ((hw e).choose : A)
    let wt : Fin n → L := fun i => (((π : A) : L) ^ (φ i))⁻¹

    (∀ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers), g ≠ 0 → (∀ P, 0 ≤ P.ord g + D P) →
      (∀ i, ∀ Q, Q ∉ (C i).nodes → (C i).residue ⟨wt i • g, hg i⟩ ≠ 0 →
        0 ≤ Q.ord ((C i).residue ⟨wt i • g, hg i⟩) + Dbar i Q) ∧
      (∀ e, (C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ ≠ 0 →
        k e ≤ (xs e).ord ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩)) ∧
      (∀ e, (C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ ≠ 0 →
        -k e ≤ (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩)) ∧
      ∀ e, (xs e).evalAt ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ * zs e ^ (-k e)) * ubar e ^ (k e) =
        (xt e).evalAt ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e))) ∧

    (∀ h : ∀ i, Fbar i,
      (∀ i, ∀ Q, Q ∉ (C i).nodes → h i ≠ 0 → 0 ≤ Q.ord (h i) + Dbar i Q) →
      (∀ e, h (src e) ≠ 0 → k e ≤ (xs e).ord (h (src e))) →
      (∀ e, h (tgt e) ≠ 0 → -k e ≤ (xt e).ord (h (tgt e))) →
      (∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))) →
      ∃ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers), (g = 0 ∨ ∀ P, 0 ≤ P.ord g + D P) ∧
        ∀ i, (C i).residue ⟨wt i • g, hg i⟩ = h i) := by
  classical

  have hINTO := AlgebraicCurve.SemistableCovering.ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
    A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hw1 hatt hnodes hcover hdisc hgenus φ D hD

  have hK9 := AlgebraicCurve.SemistableCovering.finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
    A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hw1 hatt hnodes hcover hdisc hgenus φ D hD hdegD

  obtain ⟨s, hs, hsD, hli⟩ :=
    AlgebraicCurve.SemistableCovering.exists_linearIndependent_pi_residue_smul_of_mem_riemannRochSpace_of_rankOne
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus D φ
  refine ⟨hINTO, ?_⟩
  intro h hC1 hC2 hC3 hC4

  obtain ⟨U, hUfin, hUdim, hWU⟩ : ∃ U : Submodule (IsLocalRing.ResidueField ↥A) (∀ i, Fbar i),
      FiniteDimensional (IsLocalRing.ResidueField ↥A) U ∧ Module.finrank (IsLocalRing.ResidueField ↥A) U = Module.finrank L (riemannRochSpace D) ∧
      ∀ x : ∀ i, Fbar i, x ∈ {x : ∀ i, Fbar i | (∀ i, x i ∈ riemannRochSpace ((Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) : Divisor (IsLocalRing.ResidueField ↥A) (Fbar i)) + Finsupp.split (∑ e, (Finsupp.single (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) (-(φ (tgt e) - φ (src e))) + Finsupp.single (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) (φ (tgt e) - φ (src e)))) i)) ∧ ∀ e, (xs e).evalAt (x (src e) * (C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩ ^ (-(φ (tgt e) - φ (src e)))) * IsLocalRing.residue ↥A ((hw e).choose : ↥A) ^ (φ (tgt e) - φ (src e)) = (xt e).evalAt (x (tgt e) * (C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩ ^ (φ (tgt e) - φ (src e)))} → x ∈ U :=
    ⟨_, hK9.1, hK9.2, fun x hx => Submodule.subset_span hx⟩

  have hxs : ∀ e, xs e ∈ (C (src e)).nodes := fun e => (hatt e).1.1
  have hxt : ∀ e, xt e ∈ (C (tgt e)).nodes := fun e => (hatt e).2.1
  have hDbarN : ∀ i, ∀ x ∈ (C i).nodes, (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) : Divisor (IsLocalRing.ResidueField ↥A) (Fbar i)) x = 0 :=
    fun i x hx => BDescK3Bridge.mapDomain_filter_apply_eq_zero_of_mem_nodes (C i) D x hx

  have bridge : ∀ h' : ∀ i, Fbar i,
      (∀ i, ∀ Q, Q ∉ (C i).nodes → h' i ≠ 0 → 0 ≤ Q.ord (h' i) + (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) : Divisor (IsLocalRing.ResidueField ↥A) (Fbar i)) Q) →
      (∀ e, h' (src e) ≠ 0 → (φ (tgt e) - φ (src e)) ≤ (xs e).ord (h' (src e))) →
      (∀ e, h' (tgt e) ≠ 0 → -(φ (tgt e) - φ (src e)) ≤ (xt e).ord (h' (tgt e))) →
      ∀ i, h' i ∈ riemannRochSpace ((Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) : Divisor (IsLocalRing.ResidueField ↥A) (Fbar i)) + Finsupp.split (∑ e, (Finsupp.single (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) (-(φ (tgt e) - φ (src e))) + Finsupp.single (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) (φ (tgt e) - φ (src e)))) i) :=
    fun h' c1 c2 c3 => BDescK3Bridge.mem_riemannRochSpace_add_nodeDivisor_of_ord_clauses Fbar (fun i => (C i).nodes)
      src tgt xs xt hxs hxt hnodes.1 hnodes.2 _ hDbarN (fun e => (φ (tgt e) - φ (src e))) h' c1 c2 c3

  have hs' : ∀ j i, (((π : A) : L) ^ (φ i))⁻¹ • s j ∈ (C i).integers := fun j i => hs j i
  have hred0 : ∀ j, s j ≠ 0 := by
    intro j hj
    apply hli.ne_zero j
    funext i
    show (C i).residue ⟨(((π : A) : L) ^ (φ i))⁻¹ • s j, hs j i⟩ = 0
    have : (⟨(((π : A) : L) ^ (φ i))⁻¹ • s j, hs j i⟩ : (C i).integers) = 0 := Subtype.ext (by simp [hj])
    rw [this, map_zero]
  have hsD' : ∀ j P, 0 ≤ P.ord (s j) + D P := by
    intro j P
    have := (mem_riemannRochSpace_iff.mp (hsD j) P).resolve_left (hred0 j)
    omega

  have hle : Submodule.span (IsLocalRing.ResidueField ↥A)
      (Set.range fun j => fun i => (C i).residue ⟨(((π : A) : L) ^ (φ i))⁻¹ • s j, hs j i⟩) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨c1, c2, c3, c4⟩ := hINTO (s j) (hs' j) (hred0 j) (hsD' j)
    exact hWU _ ⟨bridge _ c1 c2 c3, c4⟩
  haveI := hUfin
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact hUdim.symm)

  have hhU : h ∈ Submodule.span (IsLocalRing.ResidueField ↥A)
      (Set.range fun j => fun i => (C i).residue ⟨(((π : A) : L) ^ (φ i))⁻¹ • s j, hs j i⟩) := by
    rw [heq]
    exact hWU _ ⟨bridge h hC1 hC2 hC3, hC4⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hhU

  have hres : Function.Surjective (IsLocalRing.residue ↥A) := Ideal.Quotient.mk_surjective
  choose a ha using fun j => hres (c j)
  refine ⟨∑ j, ((a j : A) : L) • s j, fun i => ?_, ?_, fun i => ?_⟩
  ·
    rw [Finset.smul_sum]
    refine sum_mem fun j _ => ?_
    rw [smul_smul, mul_comm, ← smul_smul, Algebra.smul_def]
    exact mul_mem (((C i).algebraMap_mem_iff _).mpr (a j).2) (hs j i)
  ·
    have hg : (∑ j, ((a j : A) : L) • s j) ∈ riemannRochSpace D :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hsD j)
    by_cases hg0 : (∑ j, ((a j : A) : L) • s j) = 0
    · exact Or.inl hg0
    · right
      intro P
      have := (mem_riemannRochSpace_iff.mp hg P).resolve_left hg0
      omega
  ·
    have hdecomp : ∀ hmem : (((π : A) : L) ^ (φ i))⁻¹ • ∑ j, ((a j : A) : L) • s j ∈ (C i).integers,
        (⟨(((π : A) : L) ^ (φ i))⁻¹ • ∑ j, ((a j : A) : L) • s j, hmem⟩ : (C i).integers) =
          ∑ j, (⟨algebraMap L F ((a j : A) : L), ((C i).algebraMap_mem_iff _).mpr (a j).2⟩ : (C i).integers) *
            ⟨(((π : A) : L) ^ (φ i))⁻¹ • s j, hs j i⟩ := by
      intro hmem
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      simp only [MulMemClass.coe_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm, ← smul_smul, Algebra.smul_def]
    rw [hdecomp, map_sum]
    have hci := congrFun hc i
    rw [Finset.sum_apply] at hci
    rw [← hci]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, (C i).residue_algebraMap (a j), Pi.smul_apply,
      show IsLocalRing.residue ↥A (a j) = c j from ha j]
    exact (Algebra.smul_def (c j) _).symm

end S_AlgebraicCurve_SemistableCovering_exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one (solution)
