-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/00257439-1de1-5ef1-8fb6-2c4102a0e608

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos

import Theorems.Thm_AlgebraicCurve_SemistableCovering_ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne

import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_nodeEquivOfPlaces_apply"
p2m_attr_erase "simp" "ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus P2MW.S_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne.AlgebraicCurve"
open scoped IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord_zero Place.ord_inv Divisor Divisor.degree Divisor.degree_single riemannRochSpace mem_riemannRochSpace_iff genusFF IsCurveOver exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType IsCurveOver.exists_separating_transcendental Place.exists_ord_sub_algebraMap_pos_of_transcendental SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne SemistableCovering.exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne"
p2m_open "AlgebraicCurve~genus"

private theorem infinite_place_of_isCurveOver (k Fb : Type*) [Field k] [IsAlgClosed k] [Field Fb] [Algebra k Fb]
    [IsCurveOver k Fb] [Algebra.EssFiniteType k Fb] (hrat : ∀ v : Place k Fb, v.IsRational) :
    Infinite (Place k Fb) := by
  obtain ⟨t, ht, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := k) (F := Fb)
  haveI := hfd; haveI := hsep
  have hex : ∀ c : k, ∃ v : Place k Fb, 0 < v.ord (t - algebraMap k Fb c) := fun c =>
    Place.exists_ord_sub_algebraMap_pos_of_transcendental t ht c
  choose v hv using hex
  have htc : ∀ c : k, t ≠ algebraMap k Fb c := by
    intro c htc
    apply ht
    rw [htc]
    exact isAlgebraic_algebraMap c
  refine Infinite.of_injective v fun c c' hcc' => ?_
  have h1 := ((v c).mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos (hrat _) t c (htc c)).mpr (hv c)
  have h2 := ((v c').mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos (hrat _) t c' (htc c')).mpr (hv c')
  rw [← hcc'] at h2
  exact h1.2.symm.trans h2.2

private theorem exists_finset_subset_compl_card_eq {α : Type*} [Infinite α] (S : Finset α) (N : ℕ) :
    ∃ T : Finset α, (∀ x ∈ T, x ∉ S) ∧ T.card = N := by
  classical
  have hinf : ((S : Set α)ᶜ).Infinite := S.finite_toSet.infinite_compl
  obtain ⟨T, hT, hcard⟩ := hinf.exists_subset_card_eq N
  exact ⟨T, fun x hx hxS => hT (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hxS), hcard⟩

end AlgebraicCurve

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord_zero Place.ord_inv Divisor Divisor.degree Divisor.degree_single riemannRochSpace mem_riemannRochSpace_iff genusFF IsCurveOver exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType IsCurveOver.exists_separating_transcendental Place.exists_ord_sub_algebraMap_pos_of_transcendental SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne SemistableCovering.exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne" namespace SemistableCovering p2m_export "AlgebraicCurve.SemistableCovering" "ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne" end AlgebraicCurve.SemistableCovering
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.SemistableCovering" in

private theorem AlgebraicCurve.SemistableCovering.K0_exists_chartDivisors
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
    :
    ∃ E : Fin n → Divisor L F, (∀ i, ∀ Q ∈ (E i).support, Q ∈ (C i).dom) ∧ (∀ i, 0 ≤ E i) ∧
      (∀ i, ((C i).nodes.card : ℤ) + 2 * genusFF (IsLocalRing.ResidueField A) (Fbar i) + 2 ≤
        Divisor.degree (Finsupp.mapDomain (C i).placeMap (E i))) ∧
      (∀ i, ∀ Q ∈ (E i).support, ∀ Q' ∈ (E i).support, (C i).placeMap Q = (C i).placeMap Q' → Q = Q') ∧
      (∀ i, ∀ Q ∈ (E i).support, (E i) Q = 1) := by
  classical
  have _ := hrk; have _ := hgenus; have _ := hnodes; have _ := hratF; have _ := hcover; have _ := hatt; have _ := hw
  have _ := hpair; have _ := hπ0
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := A.isAlgClosed_residueField_of_isAlgClosed

  have key : ∀ i, ∃ Ei : Divisor L F, (∀ Q ∈ Ei.support, Q ∈ (C i).dom) ∧ 0 ≤ Ei ∧
      ((C i).nodes.card : ℤ) + 2 * genusFF (IsLocalRing.ResidueField A) (Fbar i) + 2 ≤
        Divisor.degree (Finsupp.mapDomain (C i).placeMap Ei) ∧
      (∀ Q ∈ Ei.support, ∀ Q' ∈ Ei.support, (C i).placeMap Q = (C i).placeMap Q' → Q = Q') ∧
      (∀ Q ∈ Ei.support, Ei Q = 1) := by
    intro i
    haveI : Infinite (Place (IsLocalRing.ResidueField A) (Fbar i)) :=
      infinite_place_of_isCurveOver (IsLocalRing.ResidueField A) (Fbar i) (hratBar i)
    set N : ℕ := (C i).nodes.card + 2 * genusFF (IsLocalRing.ResidueField A) (Fbar i) + 2 with hN
    obtain ⟨Ubar, hUbar, hUcard⟩ := exists_finset_subset_compl_card_eq (C i).nodes N

    have hlift : ∀ y : Place (IsLocalRing.ResidueField A) (Fbar i), y ∉ (C i).nodes →
        ∃ P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = y := by
      intro y hy
      obtain ⟨T, hT, -, -, -, huniq⟩ := hdisc i y hy
      obtain ⟨P, ⟨hPdom, hPmap, -⟩, -⟩ := huniq π hπ
      exact ⟨P, hPdom, hPmap⟩

    have hUne : Ubar.Nonempty := by
      rw [← Finset.card_pos, hUcard, hN]; omega
    obtain ⟨y₀, hy₀⟩ := hUne
    obtain ⟨P₀, -, -⟩ := hlift y₀ (hUbar y₀ hy₀)
    have hQ : ∀ y : Place (IsLocalRing.ResidueField A) (Fbar i), ∃ P : Place L F,
        y ∉ (C i).nodes → P ∈ (C i).dom ∧ (C i).placeMap P = y := by
      intro y
      by_cases hy : y ∈ (C i).nodes
      · exact ⟨P₀, fun h => absurd hy h⟩
      · obtain ⟨P, hP1, hP2⟩ := hlift y hy
        exact ⟨P, fun _ => ⟨hP1, hP2⟩⟩
    choose Q hQ using hQ
    have hQdom : ∀ y ∈ Ubar, Q y ∈ (C i).dom := fun y hy => (hQ y (hUbar y hy)).1
    have hQmap : ∀ y ∈ Ubar, (C i).placeMap (Q y) = y := fun y hy => (hQ y (hUbar y hy)).2
    have hQinj : ∀ y ∈ Ubar, ∀ y' ∈ Ubar, Q y = Q y' → y = y' := by
      intro y hy y' hy' hyy'
      rw [← hQmap y hy, ← hQmap y' hy', hyy']
    refine ⟨∑ y ∈ Ubar, Finsupp.single (Q y) 1, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro P hP
      obtain ⟨y, hy, hyP⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hP)
      rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hyP
      rw [hyP]; exact hQdom y hy
    · exact Finset.sum_nonneg fun y _ => by
        intro P; rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply]; split_ifs <;> norm_num
    ·
      have hmap : Finsupp.mapDomain (C i).placeMap (∑ y ∈ Ubar, Finsupp.single (Q y) (1 : ℤ)) =
          ∑ y ∈ Ubar, Finsupp.single y 1 := by
        rw [Finsupp.mapDomain_finsetSum]
        exact Finset.sum_congr rfl fun y hy => by rw [Finsupp.mapDomain_single, hQmap y hy]
      rw [hmap, map_sum]
      have : ∀ y ∈ Ubar, Divisor.degree (Finsupp.single y (1 : ℤ)) = 1 := fun y _ => by
        rw [Divisor.degree_single, one_mul]
        have hbij : Function.Bijective (algebraMap (IsLocalRing.ResidueField A) y.ResidueField) :=
          ⟨y.algebraMap_residueField_injective, hratBar i y⟩
        show (Module.finrank (IsLocalRing.ResidueField A) y.ResidueField : ℤ) = 1
        rw [← ((AlgEquiv.ofBijective (Algebra.ofId _ y.ResidueField) hbij).toLinearEquiv.finrank_eq),
          Module.finrank_self]; rfl
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one, hUcard, hN]
      push_cast; exact le_refl _
    ·
      intro P hP P' hP' hmap
      obtain ⟨y, hy, hyP⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hP)
      obtain ⟨y', hy', hyP'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hP')
      rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hyP hyP'
      rw [hyP, hyP'] at hmap ⊢
      rw [hQmap y hy, hQmap y' hy'] at hmap
      rw [hmap]
    ·
      intro P hP
      obtain ⟨y, hy, hyP⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hP)
      rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hyP
      rw [hyP, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single y]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro y' hy' hne
        rw [Finsupp.single_apply, if_neg]
        exact fun h0 => hne (hQinj y' hy' y hy h0)
      · intro h0; exact absurd hy h0
  choose E h1 h2 h3 h4 h5 using key
  exact ⟨E, h1, h2, h3, h4, h5⟩

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.SemistableCovering" in

private theorem AlgebraicCurve.SemistableCovering.K2_exists_targets
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
    (E : Fin n → Divisor L F) (hE : ∀ i, ∀ Q ∈ (E i).support, Q ∈ (C i).dom) (hE0 : ∀ i, 0 ≤ E i)
    (hEbig : ∀ i, ((C i).nodes.card : ℤ) + 2 * genusFF (IsLocalRing.ResidueField A) (Fbar i) + 2 ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (E i)))
    (hEred : ∀ i, ∀ Q ∈ (E i).support, ∀ Q' ∈ (E i).support, (C i).placeMap Q = (C i).placeMap Q' → Q = Q')
    (hEone : ∀ i, ∀ Q ∈ (E i).support, (E i) Q = 1)
    (e₀ : Fin m) (lam : (IsLocalRing.ResidueField A)ˣ)
    :
    ∃ sbar : ∀ i, Fbar i, (∀ i, sbar i ≠ 0) ∧
      (∀ i, sbar i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (E i))) ∧
      (∀ i, ∀ x ∈ (C i).nodes, (sbar i) ∈ x.toValuationSubring ∧ x.evalAt (sbar i) ≠ 0) ∧
      (∀ e, e ≠ e₀ → (xs e).evalAt (sbar (src e)) = (xt e).evalAt (sbar (tgt e))) ∧
      (xs e₀).evalAt (sbar (src e₀)) = (lam : IsLocalRing.ResidueField A) * (xt e₀).evalAt (sbar (tgt e₀)) := by
  classical
  have _ := hrk; have _ := hgenus; have _ := hratF; have _ := hcover; have _ := hw; have _ := hpair; have _ := hπ0
  have _ := hπ; have _ := hdisc; have _ := hE0
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := A.isAlgClosed_residueField_of_isAlgClosed

  let val : ∀ i, Place (IsLocalRing.ResidueField A) (Fbar i) → IsLocalRing.ResidueField A := fun i x =>
    if (⟨i, x⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨src e₀, xs e₀⟩ then (lam : _) else 1
  have hval0 : ∀ i x, val i x ≠ 0 := by
    intro i x; simp only [val]; split_ifs
    · exact lam.ne_zero
    · exact one_ne_zero

  have key : ∀ i, ∃ g : Fbar i, g ≠ 0 ∧ g ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (E i)) ∧
      ∀ x ∈ (C i).nodes, g ∈ x.toValuationSubring ∧ x.evalAt g = val i x := by
    intro i
    haveI : Infinite (Place (IsLocalRing.ResidueField A) (Fbar i)) :=
      infinite_place_of_isCurveOver (IsLocalRing.ResidueField A) (Fbar i) (hratBar i)
    set U : Finset (Place (IsLocalRing.ResidueField A) (Fbar i)) := (E i).support.image (C i).placeMap with hU

    have hmapE : Finsupp.mapDomain (C i).placeMap (E i) = ∑ y ∈ U, Finsupp.single y 1 := by
      have hEsum : E i = ∑ Q ∈ (E i).support, Finsupp.single Q 1 := by
        conv_lhs => rw [← Finsupp.sum_single (E i)]
        exact Finset.sum_congr rfl fun Q hQ => by rw [hEone i Q hQ]
      rw [hEsum, Finsupp.mapDomain_finsetSum, hU, Finset.sum_image (fun Q hQ Q' hQ' h => hEred i Q hQ Q' hQ' h)]
      exact Finset.sum_congr rfl fun Q _ => Finsupp.mapDomain_single
    have hUnodes : ∀ y ∈ U, y ∉ (C i).nodes := by
      intro y hy
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hy
      exact (C i).placeMap_not_mem_nodes Q (hE i Q hQ)
    have hdisj : Disjoint U (C i).nodes := Finset.disjoint_left.mpr hUnodes

    have hdegU : Divisor.degree (∑ y ∈ U, Finsupp.single y (1 : ℤ) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i)) = U.card := by
      rw [map_sum]
      have : ∀ y ∈ U, Divisor.degree (Finsupp.single y (1 : ℤ) :
          Divisor (IsLocalRing.ResidueField A) (Fbar i)) = 1 := fun y _ => by
        rw [Divisor.degree_single, one_mul]
        have hbij : Function.Bijective (algebraMap (IsLocalRing.ResidueField A) y.ResidueField) :=
          ⟨y.algebraMap_residueField_injective, hratBar i y⟩
        show (Module.finrank (IsLocalRing.ResidueField A) y.ResidueField : ℤ) = 1
        rw [← ((AlgEquiv.ofBijective (Algebra.ofId _ y.ResidueField) hbij).toLinearEquiv.finrank_eq),
          Module.finrank_self]; rfl
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (C i).nodes.card + 2 * genusFF (IsLocalRing.ResidueField A) (Fbar i) + 2 ≤ U.card := by
      have := hEbig i
      rw [hmapE, hdegU] at this
      exact_mod_cast this

    obtain ⟨T, hT, hTcard⟩ := exists_finset_subset_compl_card_eq (U ∪ (C i).nodes) 1
    obtain ⟨t₀, ht₀⟩ := Finset.card_pos.mp (by rw [hTcard]; exact Nat.one_pos)
    have ht₀U : t₀ ∉ U := fun h0 => hT t₀ ht₀ (Finset.mem_union_left _ h0)
    have ht₀n : t₀ ∉ (C i).nodes := fun h0 => hT t₀ ht₀ (Finset.mem_union_right _ h0)
    obtain ⟨g, hgRR, hgt₀, hgval, -⟩ :=
      AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
        (IsLocalRing.ResidueField A) (Fbar i) U (C i).nodes ∅ t₀ 0 (val i) ∅ hdisj
        (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) ht₀U ht₀n (Finset.notMem_empty _) hcard
    refine ⟨g, ?_, by rw [hmapE]; exact hgRR, fun x hx => ?_⟩
    · rintro rfl
      rw [map_zero, sub_zero, Place.ord_zero] at hgt₀
      exact zero_ne_one hgt₀
    · obtain ⟨hmem, hres⟩ := hgval x hx
      refine ⟨hmem, ?_⟩
      rw [x.evalAt_of_mem hmem, hres, x.residueInv_algebraMap]
  choose sbar hs0 hsRR hsnode using key

  obtain ⟨-, hinj⟩ := hnodes
  have hsrc : ∀ e, (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨src e₀, xs e₀⟩ → e = e₀ := by
    intro e he
    have := hinj (src e₀) (xs e₀) (hatt e₀).1.1 (Sum.inl e) (Sum.inl e₀) he rfl
    exact Sum.inl_injective this
  have htgt : ∀ e, (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) ≠ ⟨src e₀, xs e₀⟩ := by
    intro e he
    have := hinj (src e₀) (xs e₀) (hatt e₀).1.1 (Sum.inr e) (Sum.inl e₀) he rfl
    exact Sum.inr_ne_inl this
  refine ⟨sbar, hs0, hsRR, fun i x hx => ⟨(hsnode i x hx).1, by rw [(hsnode i x hx).2]; exact hval0 i x⟩, ?_, ?_⟩
  · intro e he
    rw [(hsnode (src e) (xs e) (hatt e).1.1).2, (hsnode (tgt e) (xt e) (hatt e).2.1).2]
    simp only [val, if_neg (htgt e)]
    rw [if_neg (fun h0 => he (hsrc e h0))]
  · rw [(hsnode (src e₀) (xs e₀) (hatt e₀).1.1).2, (hsnode (tgt e₀) (xt e₀) (hatt e₀).2.1).2]
    simp only [val, if_neg (htgt e₀), if_pos rfl, mul_one]

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
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt (An e₀).param ∈ A) (h' : P'.evalAt (An e₀).param ∈ A)
    (hd : (⟨P.evalAt (An e₀).param, h⟩ : A) = u * π ^ d) (hd' : (⟨P'.evalAt (An e₀).param, h'⟩ : A) = u' * π ^ d)
    :
    ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ Q, Df Q = Q.ord f) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Df Q = (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) Q) ∧
      ∃ Di : Fin n → Divisor L F, Df - (Finsupp.single P 1 - Finsupp.single P' 1) = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by
  classical

  obtain ⟨E, hE, hE0, hEbig, hEred, hEone⟩ :=
    AlgebraicCurve.SemistableCovering.K0_exists_chartDivisors A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus

  set lam : (IsLocalRing.ResidueField A)ˣ := Units.map (IsLocalRing.residue A).toMonoidHom (u * u'⁻¹) with hlam
  obtain ⟨sbar, hs0, hsRR, hsnode, hglue, hglue₀⟩ :=
    AlgebraicCurve.SemistableCovering.K2_exists_targets A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs
      xt w hpair hw hatt hnodes hcover hdisc hgenus E hE hE0 hEbig hEred hEone e₀ lam
  have hglue₀' : (xs e₀).evalAt (sbar (src e₀)) =
      IsLocalRing.residue A ((u : A) * ↑u'⁻¹) * (xt e₀).evalAt (sbar (tgt e₀)) := by
    rw [hglue₀, hlam]; rfl

  have hdegE : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (E i) : Divisor (IsLocalRing.ResidueField A) (Fbar i)) := by
    intro i; have := hEbig i; linarith
  have hsnode' : ∀ i, ∀ x ∈ (C i).nodes, (sbar i) ∈ x.toValuationSubring ∧ x.ord (sbar i) = 0 := by
    intro i x hx
    obtain ⟨hreg, hval⟩ := hsnode i x hx
    refine ⟨hreg, ?_⟩

    have hres : IsLocalRing.residue x.toValuationSubring ⟨sbar i, hreg⟩ ≠ 0 := by
      intro h0; apply hval
      rw [x.evalAt_of_mem hreg, h0, ← map_zero (algebraMap (IsLocalRing.ResidueField A) x.ResidueField),
        x.residueInv_algebraMap]
    have hu : IsUnit (⟨sbar i, hreg⟩ : x.toValuationSubring) := by
      by_contra hnu; apply hres
      rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    obtain ⟨uu, huu⟩ := hu
    have := x.ord_coe_unit uu
    rwa [huu] at this
  obtain ⟨g, hg0, hgRR, hgres⟩ :=
    AlgebraicCurve.SemistableCovering.exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne A π hπ hπ0
      hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus E hE hE0 hdegE e₀
      P P' hP hP' hPP' d u u' h h' hd hd' sbar hsRR hsnode' hglue hglue₀'

  have hEann : ∀ e, ∀ Q ∈ (An e).dom, (∑ i, E i) Q = 0 := by
    intro e Q hQ
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_contra hne
    have hQs : Q ∈ (E i).support := Finsupp.mem_support_iff.mpr hne
    rcases hcover Q with ⟨j, -, -, hnot⟩ | ⟨e', -, -, hnot⟩
    · exact hnot e hQ
    · exact hnot i (hE i Q hQs)
  have hord : ∀ Q : Place L F,
      -((((∑ i, E i) + Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F)) Q) ≤ Q.ord g := fun Q =>
    ((mem_riemannRochSpace_iff.mp hgRR) Q).resolve_left hg0
  have hgann : ∀ e, ∀ Q ∈ (An e).dom, Q ≠ P → Q ≠ P' → 0 ≤ Q.ord g := by
    intro e Q hQ hQP hQP'
    have := hord Q
    rw [Finsupp.sub_apply, Finsupp.add_apply, hEann e Q hQ, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (Ne.symm hQP), if_neg (Ne.symm hQP')] at this
    simpa using this
  have hgP : -1 ≤ P.ord g := by
    have := hord P
    rw [Finsupp.sub_apply, Finsupp.add_apply, hEann e₀ P hP, Finsupp.single_apply, Finsupp.single_apply,
      if_pos rfl, if_neg (Ne.symm hPP')] at this
    simpa using this
  have hgP' : 1 ≤ P'.ord g := by
    have := hord P'
    rw [Finsupp.sub_apply, Finsupp.add_apply, hEann e₀ P' hP', Finsupp.single_apply, Finsupp.single_apply,
      if_neg hPP', if_pos rfl] at this
    simpa using this
  have hgres' : ∀ i, ∃ hg : g ∈ (C i).integers, (C i).residue ⟨g, hg⟩ ≠ 0 ∧ ∀ x ∈ (C i).nodes,
      (C i).residue ⟨g, hg⟩ ∈ x.toValuationSubring ∧ x.evalAt ((C i).residue ⟨g, hg⟩) ≠ 0 := by
    intro i
    obtain ⟨hg, hres⟩ := hgres i
    refine ⟨hg, by rw [hres]; exact hs0 i, fun x hx => ?_⟩
    rw [hres]; exact hsnode i x hx

  obtain ⟨Dg, hDg, hann, Di, hDi, hsupp, hdeg⟩ :=
    AlgebraicCurve.SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne A π hπ
      hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus e₀ P P' hP
      hP' hPP' d u u' h h' hd hd' g hg0 hgann hgP hgP' hgres'

  refine ⟨g⁻¹, -Dg, inv_ne_zero hg0, fun Q => by rw [Finsupp.neg_apply, hDg, Place.ord_inv], ?_, fun i => -Di i,
    ?_, ?_, ?_⟩
  · intro e Q hQ
    rw [Finsupp.neg_apply, hann e Q hQ, Finsupp.sub_apply, Finsupp.sub_apply]; ring
  · have : -Dg - (Finsupp.single P 1 - Finsupp.single P' 1) = -(Dg - (Finsupp.single P' 1 - Finsupp.single P 1)) := by
      abel
    rw [this, hDi, ← Finset.sum_neg_distrib]
  · intro i Q hQ; rw [Finsupp.support_neg] at hQ; exact hsupp i Q hQ
  · intro i; rw [map_neg, hdeg, neg_zero]

end S_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne (solution)
