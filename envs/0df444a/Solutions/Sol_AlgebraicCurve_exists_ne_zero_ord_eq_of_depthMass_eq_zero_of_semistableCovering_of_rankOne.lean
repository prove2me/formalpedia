-- Prove2me | solution 1 for AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c70fc12b-a9dc-52f0-8b46-27102436ed08

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
import Theorems.Thm_Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus P2MW.S_AlgebraicCurve_exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Divisor Divisor.degree genusFF IsCurveOver SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "IsAttached modulus mk dom param mk.injEq"
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve~genus"

variable {L : Type*} [Field L] {A : ValuationSubring L}

private theorem depth_unique {π : A} (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    {x : A} {d d' : ℕ} {u u' : Aˣ} (hd : x = u * π ^ d) (hd' : x = u' * π ^ d') : d = d' := by
  wlog hle : d ≤ d' generalizing d d' u u'
  · exact (this hd' hd ((le_total d d').resolve_left hle)).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · exfalso
    have h1 : (u : A) * π ^ d = u' * π ^ k * π ^ d := by rw [← hd, hd', pow_add]; ring
    have h2 : (u : A) = u' * π ^ k := mul_right_cancel₀ (pow_ne_zero _ hπ0) h1
    apply (IsLocalRing.mem_maximalIdeal _).mp _ u.isUnit
    rw [h2]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπ _ hk)

end AlgebraicCurve.Annulus

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
    (Dan : Divisor L F)
    (hDan : ∀ Q ∈ Dan.support, ∃ e, Q ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : Q.evalAt (An e).param ∈ A),
      (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d)
    (hmass : ∀ (e : Fin m) (d : ℕ), ∀ S : Finset (Place L F),
      (∀ Q, Q ∈ S ↔ Q ∈ Dan.support ∧ Q ∈ (An e).dom ∧
        ∃ (u : Aˣ) (h : Q.evalAt (An e).param ∈ A), (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
      (S.sum fun Q => Dan Q) = 0)
    :
    ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ Q, Df Q = Q.ord f) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Df Q = Dan Q) ∧
      ∃ Di : Fin n → Divisor L F, Df - Dan = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by
  classical

  let latt : Place L F → Fin m → ℕ → Prop := fun Q e d =>
    Q ∈ (An e).dom ∧ ∃ (u : Aˣ) (h : Q.evalAt (An e).param ∈ A), (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d
  have huniq : ∀ Q e d e' d', latt Q e d → latt Q e' d' → e = e' ∧ d = d' := by
    rintro Q e d e' d' ⟨he, u, h, hd⟩ ⟨he', u', h', hd'⟩
    obtain rfl : e' = e := by
      rcases hcover Q with ⟨i, -, -, hnot⟩ | ⟨e'', -, hun, -⟩
      · exact absurd he (hnot e)
      · exact (hun e' he').trans (hun e he).symm
    exact ⟨rfl, Annulus.depth_unique hπ hπ0 hd hd'⟩
  let ℓ : Place L F → Option (Fin m × ℕ) := fun Q =>
    if hq : ∃ e d, latt Q e d then some (hq.choose, hq.choose_spec.choose) else none
  have hℓ : ∀ Q e d, latt Q e d → ℓ Q = some (e, d) := by
    intro Q e d hQ
    have hq : ∃ e d, latt Q e d := ⟨e, d, hQ⟩
    simp only [ℓ, dif_pos hq]
    obtain ⟨h1, h2⟩ := huniq Q _ _ e d hq.choose_spec.choose_spec hQ
    exact congrArg some (Prod.ext h1 h2)
  have hℓ' : ∀ Q e d, ℓ Q = some (e, d) → latt Q e d := by
    intro Q e d hQ
    by_cases hq : ∃ e d, latt Q e d
    · simp only [ℓ, dif_pos hq, Option.some.injEq, Prod.mk.injEq] at hQ
      obtain ⟨h1, h2⟩ := hQ
      rw [← h1, ← h2]
      exact hq.choose_spec.choose_spec
    · simp only [ℓ, dif_neg hq] at hQ
      exact absurd hQ (by simp)

  have hfib : ∀ b, ((Dan.support.filter fun Q => ℓ Q = b).sum fun Q => Dan Q) = 0 := by
    intro b
    rcases b with _ | ⟨e, d⟩
    · refine Finset.sum_eq_zero fun Q hQ => ?_
      exfalso
      rw [Finset.mem_filter] at hQ
      obtain ⟨e, he, d, u, h, hd⟩ := hDan Q hQ.1
      have := hℓ Q e d ⟨he, u, h, hd⟩
      rw [hQ.2] at this
      exact Option.some_ne_none _ this.symm
    · apply hmass e d
      intro Q
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hs, hQ⟩; exact ⟨hs, hℓ' Q e d hQ⟩
      · rintro ⟨hs, hQ⟩; exact ⟨hs, hℓ Q e d hQ⟩
  obtain ⟨l, hl, hsum⟩ := Finsupp.exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero ℓ Dan hfib

  have key : ∀ l : List (Place L F × Place L F),
      (∀ p ∈ l, ℓ p.1 = ℓ p.2 ∧ p.1 ∈ Dan.support ∧ p.2 ∈ Dan.support ∧ p.1 ≠ p.2) →
      ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ Q, Df Q = Q.ord f) ∧
        (∀ e, ∀ Q ∈ (An e).dom,
          Df Q = (l.map fun p => (Finsupp.single p.1 1 - Finsupp.single p.2 1 : Divisor L F)).sum Q) ∧
        ∃ Di : Fin n → Divisor L F,
          Df - (l.map fun p => (Finsupp.single p.1 1 - Finsupp.single p.2 1 : Divisor L F)).sum = ∑ i, Di i ∧
          (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨1, 0, one_ne_zero, fun Q => by simp, fun e Q _ => by simp, fun _ => 0, by simp, by simp, by simp⟩
    | cons p l ih =>
      intro hl
      obtain ⟨f₁, Df₁, hf₁, hDf₁, hann₁, Di₁, hDi₁, hsupp₁, hdeg₁⟩ :=
        ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      obtain ⟨hℓp, hp1, -, hne⟩ := hl p List.mem_cons_self
      obtain ⟨e, he, d, u, h, hd⟩ := hDan p.1 hp1
      have h1 : ℓ p.1 = some (e, d) := hℓ p.1 e d ⟨he, u, h, hd⟩
      obtain ⟨he', u', h', hd'⟩ := hℓ' p.2 e d (hℓp ▸ h1)
      obtain ⟨f₀, Df₀, hf₀, hDf₀, hann₀, Di₀, hDi₀, hsupp₀, hdeg₀⟩ :=
        AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne A π hπ hπ0
          hrk F n m
          Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus e p.1 p.2 he he' hne d
          u u' h h' hd hd'
      refine ⟨f₀ * f₁, Df₀ + Df₁, mul_ne_zero hf₀ hf₁,
        fun Q => by rw [Finsupp.add_apply, hDf₀, hDf₁, Q.ord_mul hf₀ hf₁], ?_, fun i => Di₀ i + Di₁ i, ?_, ?_, ?_⟩
      · intro e' Q hQ
        rw [List.map_cons, List.sum_cons, Finsupp.add_apply, Finsupp.add_apply, hann₀ e' Q hQ, hann₁ e' Q hQ]
      · rw [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← hDi₀, ← hDi₁]; abel
      · intro i Q hQ
        rcases Finset.mem_union.mp (Finsupp.support_add hQ) with h0 | h0
        · exact hsupp₀ i Q h0
        · exact hsupp₁ i Q h0
      · intro i; rw [map_add, hdeg₀, hdeg₁, add_zero]
  obtain ⟨f, Df, hf, hDf, hann, Di, hDi, hsupp, hdeg⟩ := key l hl
  rw [← hsum] at hann hDi
  exact ⟨f, Df, hf, hDf, hann, Di, hDi, hsupp, hdeg⟩

end S_AlgebraicCurve_exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne (solution)
