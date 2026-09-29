-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e9ad6094-9685-52b7-b5a3-497a8e0497a6

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
import Theorems.Thm_AlgebraicCurve_mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open AlgebraicCurve

namespace CPairSharp

private theorem _root_.CPairSharp.mem_of_pow_mem {L : Type} [Field L] (A : ValuationSubring L) {y : L} {N : ℕ} (hN : 0 < N)
    (hy : y ^ N ∈ A) : y ∈ A := by
  rw [← A.valuation_le_one_iff] at hy ⊢
  rw [map_pow] at hy
  by_contra h
  exact absurd hy (not_le.mpr (one_lt_pow' (not_le.mp h) hN.ne'))

p2m_export "CPairSharp" "mem_of_pow_mem"
theorem not_mem_chart_of_mem_annulus {ιP ιC ιA : Type} {domC : ιC → Set ιP} {domA : ιA → Set ιP}
    (hcover : ∀ P : ιP, (∃ i, P ∈ domC i ∧ (∀ j, P ∈ domC j → j = i) ∧ ∀ e, P ∉ domA e) ∨
      (∃ e, P ∈ domA e ∧ (∀ e', P ∈ domA e' → e' = e) ∧ ∀ i, P ∉ domC i))
    {P : ιP} {e : ιA} (hP : P ∈ domA e) : ∀ i, P ∉ domC i := by
  rcases hcover P with ⟨i, -, -, h⟩ | ⟨e', -, -, h⟩
  · exact absurd hP (h e)
  · exact h

theorem annulus_eq_of_mem {ιP ιC ιA : Type} {domC : ιC → Set ιP} {domA : ιA → Set ιP}
    (hcover : ∀ P : ιP, (∃ i, P ∈ domC i ∧ (∀ j, P ∈ domC j → j = i) ∧ ∀ e, P ∉ domA e) ∨
      (∃ e, P ∈ domA e ∧ (∀ e', P ∈ domA e' → e' = e) ∧ ∀ i, P ∉ domC i))
    {P : ιP} {e e' : ιA} (hP : P ∈ domA e) (hP' : P ∈ domA e') : e' = e := by
  rcases hcover P with ⟨i, -, -, h⟩ | ⟨e₀, -, h, -⟩
  · exact absurd hP (h e)
  · rw [h e hP, h e' hP']

theorem chart_eq_of_mem {ιP ιC ιA : Type} {domC : ιC → Set ιP} {domA : ιA → Set ιP}
    (hcover : ∀ P : ιP, (∃ i, P ∈ domC i ∧ (∀ j, P ∈ domC j → j = i) ∧ ∀ e, P ∉ domA e) ∨
      (∃ e, P ∈ domA e ∧ (∀ e', P ∈ domA e' → e' = e) ∧ ∀ i, P ∉ domC i))
    {P : ιP} {i j : ιC} (hP : P ∈ domC i) (hP' : P ∈ domC j) : j = i := by
  rcases hcover P with ⟨i₀, -, h, -⟩ | ⟨e, -, -, h⟩
  · rw [h i hP, h j hP']
  · exact absurd hP (h i)

end CPairSharp

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
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
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom)
    (hrad : ∃ u : Aˣ, P.evalAt (An e₀).param = ((u : A) : L) * P'.evalAt (An e₀).param)
    (hrat : ∃ (N d : ℕ) (v : Aˣ), 0 < N ∧ (P.evalAt (An e₀).param) ^ N = ((v : A) : L) * (π : L) ^ d)
    :
    ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ Q, Df Q = Q.ord f) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Df Q = (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) Q) ∧
      ∃ Di : Fin n → Divisor L F, Df - (Finsupp.single P 1 - Finsupp.single P' 1) = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧
        ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
          Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) := by
  classical
  obtain ⟨u, hu⟩ := hrad
  obtain ⟨N, d, v, hN, hv⟩ := hrat
  rcases eq_or_ne P P' with hPP | hPP'
  · subst hPP
    refine ⟨1, 0, one_ne_zero, fun Q => by simp [Place.ord_one], fun e Q _ => by simp, fun _ => 0, by simp, by simp,
      fun i => by simp only [Finsupp.mapDomain_zero]; exact zero_mem _⟩

  obtain ⟨ϖL, hϖL⟩ := IsAlgClosed.exists_pow_nat_eq (π : L) hN
  have hϖA : ϖL ∈ A := CPairSharp.mem_of_pow_mem A hN (by rw [hϖL]; exact π.2)
  set ϖ : A := ⟨ϖL, hϖA⟩ with hϖdef
  have hϖN : ϖ ^ N = π := Subtype.ext (by push_cast; exact hϖL)
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem N (by rw [hϖN]; exact hπ)
  have hϖL0 : ϖL ≠ 0 := fun h => by
    apply hπ0; apply Subtype.ext; change (π : L) = 0; rw [← hϖL, h, zero_pow hN.ne']
  have hϖ0 : ϖ ≠ 0 := fun h => hϖL0 (congrArg Subtype.val h)
  have hwN : ∀ e, ∃ u : Aˣ, (An e).modulus = u * ϖ ^ (N * w e) := fun e => by
    obtain ⟨u', hu'⟩ := hw e; exact ⟨u', by rw [pow_mul, hϖN, hu']⟩

  have hzP0 : P.evalAt (An e₀).param ≠ 0 := ((An e₀).mem_dom P hP).2.2.2.1
  set q : L := P.evalAt (An e₀).param / ϖL ^ d with hq
  have hπL0 : (π : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hqN : q ^ N = ((v : A) : L) := by
    rw [hq, div_pow, hv, ← pow_mul, mul_comm d N, pow_mul, hϖL, mul_div_assoc, div_self (pow_ne_zero _ hπL0), mul_one]
  have hqA : q ∈ A := CPairSharp.mem_of_pow_mem A hN (by rw [hqN]; exact (v : A).2)
  have hq0 : q ≠ 0 := by rw [hq]; exact div_ne_zero hzP0 (pow_ne_zero _ hϖL0)
  have hqiA : q⁻¹ ∈ A := CPairSharp.mem_of_pow_mem A hN (by
    rw [inv_pow, hqN]
    have : (((v : A) : L))⁻¹ = (((v⁻¹ : Aˣ) : A) : L) := by
      symm; apply eq_inv_of_mul_eq_one_left
      rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel]; rfl
    rw [this]; exact ((v⁻¹ : Aˣ) : A).2)
  set u₁ : Aˣ := ⟨⟨q, hqA⟩, ⟨q⁻¹, hqiA⟩, Subtype.ext (by push_cast; exact mul_inv_cancel₀ hq0),
    Subtype.ext (by push_cast; exact inv_mul_cancel₀ hq0)⟩ with hu₁
  obtain ⟨hPA, -⟩ := ((An e₀).mem_dom P hP).2.2.1
  obtain ⟨hP'A, -⟩ := ((An e₀).mem_dom P' hP').2.2.1
  have hzPq : P.evalAt (An e₀).param = q * ϖL ^ d := by
    rw [hq]; field_simp
  have hu₁L : ((u₁ : A) : L) = q := by rw [hu₁]
  have hd : (⟨P.evalAt (An e₀).param, hPA⟩ : A) = u₁ * ϖ ^ d := by
    apply Subtype.ext
    change P.evalAt (An e₀).param = (((u₁ : A) * ϖ ^ d : A) : L)
    push_cast
    rw [hu₁L, hzPq]
  have huL : (((u⁻¹ : Aˣ) : A) : L) * ((u : A) : L) = 1 := by
    rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel]; rfl
  have hd' : (⟨P'.evalAt (An e₀).param, hP'A⟩ : A) = (u⁻¹ * u₁) * ϖ ^ d := by
    apply Subtype.ext
    change P'.evalAt (An e₀).param = ((((u⁻¹ * u₁ : Aˣ) : A) * ϖ ^ d : A) : L)
    have : P'.evalAt (An e₀).param = (((u⁻¹ : Aˣ) : A) : L) * P.evalAt (An e₀).param := by
      rw [hu, ← mul_assoc, huL, one_mul]
    rw [this, hzPq, Units.val_mul]; push_cast; rw [hu₁L]; ring

  obtain ⟨f, Df, hf0, hDf, hDfan, Ei, hEi, hEidom, hEideg⟩ := AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
    A ϖ hϖm hϖ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt (fun e => N * w e) hpair hwN hatt hnodes hcover
    hdisc hgenus e₀ P P' hP hP' hPP' d u₁ (u⁻¹ * u₁) hPA hP'A hd hd'
  refine ⟨f, Df, hf0, hDf, hDfan, Ei, hEi, hEidom, ?_⟩
  intro i

  have hPC : ∀ j, P ∉ (C j).dom := CPairSharp.not_mem_chart_of_mem_annulus hcover hP
  have hP'C : ∀ j, P' ∉ (C j).dom := CPairSharp.not_mem_chart_of_mem_annulus hcover hP'
  have hsingle0 : ∀ R : Place L F, (∀ j, R ∈ (C j).dom → True) → ∀ j, R ∈ (C j).dom →
      (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) R = 0 := by
    intro R _ j hR
    have hPR : P ≠ R := fun h => hPC j (by rw [h]; exact hR)
    have hP'R : P' ≠ R := fun h => hP'C j (by rw [h]; exact hR)
    rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hPR.symm, Finsupp.single_eq_of_ne hP'R.symm, sub_zero]
  have hEi_apply : ∀ j, ∀ R ∈ (C j).dom, Ei j R = R.ord f := by
    intro j R hR
    have h1 := congrArg (fun D : Divisor L F => D R) hEi
    have h0 := hsingle0 R (fun _ _ => trivial) j hR
    simp only [Finsupp.sub_apply, Finsupp.coe_finsetSum, Finset.sum_apply] at h1 h0
    rw [h0, sub_zero, hDf R] at h1
    rw [h1, Finset.sum_eq_single j]
    · intro j' _ hj'
      by_contra hne
      exact hj' (CPairSharp.chart_eq_of_mem hcover hR (hEidom j' R (Finsupp.mem_support_iff.mpr hne)))
    · intro h; exact absurd (Finset.mem_univ j) h

  set N : Fin m → Divisor L F := fun e' => if e' = e₀ then Finsupp.single P 1 - Finsupp.single P' 1 else 0
    with hN
  have hNdom : ∀ e', ∀ R ∈ (N e').support, R ∈ (An e').dom := by
    intro e' R hR
    by_cases he : e' = e₀
    · subst he
      simp only [hN, if_pos rfl] at hR
      rcases Finset.mem_union.mp (Finsupp.support_sub hR) with h | h
      · rw [Finsupp.mem_support_single] at h; rw [h.1]; exact hP
      · rw [Finsupp.mem_support_single] at h; rw [h.1]; exact hP'
    · simp [hN, if_neg he] at hR
  have hNval : ∀ e', ∀ R ∈ (An e').dom, N e' R = R.ord f := by
    intro e' R hR
    rw [← hDf R, hDfan e' R hR]
    by_cases he : e' = e₀
    · simp only [hN, if_pos he]
    · simp only [hN, if_neg he, Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply]
      have hPR : P ≠ R := fun h => he (CPairSharp.annulus_eq_of_mem hcover hP (by rw [h]; exact hR))
      have hP'R : P' ≠ R := fun h => he (CPairSharp.annulus_eq_of_mem hcover hP' (by rw [h]; exact hR))
      rw [Finsupp.single_eq_of_ne hPR.symm, Finsupp.single_eq_of_ne hP'R.symm, sub_zero]
  have hNsum : ∀ e', ((N e').sum fun _ k => k) = 0 := by
    intro e'
    by_cases he : e' = e₀
    · simp only [hN, if_pos he]
      rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_single_index rfl, sub_self]
    · simp only [hN, if_neg he, Finsupp.sum_zero_index]
  have hvP' : A.valuation (P'.evalAt (An e₀).param) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((An e₀).mem_dom P' hP').2.2.2.1
  have hNprod : ∀ e', ((N e').prod fun R k => A.valuation (R.evalAt (An e').param) ^ k) = 1 := by
    intro e'
    by_cases he : e' = e₀
    · subst he
      simp only [hN, if_pos rfl]
      rw [sub_eq_add_neg, ← Finsupp.single_neg,
        Finsupp.prod_add_index_of_disjoint (by
          rw [Finsupp.support_single_ne_zero _ one_ne_zero,
            Finsupp.support_single_ne_zero _ (neg_ne_zero.mpr one_ne_zero)]
          exact Finset.disjoint_singleton.mpr hPP')]
      rw [Finsupp.prod_single_index (zpow_zero _), Finsupp.prod_single_index (zpow_zero _),
        hu, map_mul, A.valuation_unit, one_mul, zpow_one, zpow_neg, zpow_one, mul_inv_cancel₀ hvP']
    · simp only [hN, if_neg he, Finsupp.prod_zero_index]

  have hEprin := AlgebraicCurve.mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one
    A π hπ hπ0 F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes f hf0 Ei hEidom
    hEi_apply hEideg N hNdom hNval hNsum hNprod i
  exact hEprin

end S_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne (solution)
