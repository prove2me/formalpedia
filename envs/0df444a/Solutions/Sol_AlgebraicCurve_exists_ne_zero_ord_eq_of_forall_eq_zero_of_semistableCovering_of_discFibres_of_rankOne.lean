-- Prove2me | solution 1 for AlgebraicCurve.exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/08747b49-fb46-5278-840e-a7ba2de56967

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open AlgebraicCurve in
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
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))
    let ends : (Σ e : Fin m, Fin (w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → μ (Finsupp.single P 1) = 0) →
      ∀ Dan : Divisor L F,
        (∀ P ∈ Dan.support, ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
        (∀ v : Σ e : Fin m, Fin (w e - 1), μ Dan (Sum.inr v) = 0) →
        ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ P, Df P = P.ord f) ∧
          (∀ e, ∀ Q ∈ (An e).dom, Df Q = Dan Q) ∧ ∀ i, μ Df (Sum.inl i) = 0 := by
  intro V ends lap μ h1 h2 h3 Dan hDanC hmassC
  classical

  have hdeg1 : ∀ Q : Place L F, Q.IsRational → (Q.deg : ℤ) = 1 := by
    intro Q hQ
    have e : L ≃ₗ[L] Q.ResidueField :=
      LinearEquiv.ofBijective (Algebra.linearMap L Q.ResidueField) ⟨Q.algebraMap_residueField_injective, hQ⟩
    have hfin : Module.finrank L Q.ResidueField = 1 := by
      rw [← e.finrank_eq, Module.finrank_self]
    show ((Module.finrank L Q.ResidueField : ℕ) : ℤ) = 1
    rw [hfin]; rfl

  have hdepth : ∀ (e : Fin m) (Q : Place L F), Q ∈ (An e).dom → ∀ (d : ℕ) (u : Aˣ)
      (h : Q.evalAt (An e).param ∈ A), (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d → 0 < d ∧ d < w e := by
    intro e Q hQ d u h hd
    obtain ⟨-, -, ⟨h', hmem⟩, -, mm, hmm, hmod⟩ := (An e).mem_dom Q hQ
    have hmem' : (⟨Q.evalAt (An e).param, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := hmem
    rw [hd] at hmem'
    obtain ⟨ue, hue⟩ := hw e

    have key : (ue : A) * π ^ w e = (u : A) * π ^ d * mm := by
      apply Subtype.ext
      have h1' : (((An e).modulus : A) : L) = ((ue : A) : L) * ((π : A) : L) ^ w e := by
        rw [hue]; push_cast; rfl
      have h2' : (Q.evalAt (An e).param) = ((u : A) : L) * ((π : A) : L) ^ d := by
        have := congrArg Subtype.val hd
        simpa using this
      push_cast
      rw [← h1', hmod, h2']
    constructor
    · by_contra hd0
      have hd0' : d = 0 := by omega
      rw [hd0', pow_zero, mul_one] at hmem'
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem' u.isUnit
    · by_contra hdw
      have hle : w e ≤ d := by omega
      have hsplit : (π : A) ^ d = π ^ w e * π ^ (d - w e) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      rw [hsplit] at key
      have hπw : (π : A) ^ w e ≠ 0 := pow_ne_zero _ hπ0
      have key2 : (ue : A) = (u : A) * π ^ (d - w e) * mm := by
        apply mul_left_cancel₀ hπw
        calc π ^ w e * (ue : A) = (ue : A) * π ^ w e := by ring
          _ = (u : A) * (π ^ w e * π ^ (d - w e)) * mm := key
          _ = π ^ w e * ((u : A) * π ^ (d - w e) * mm) := by ring
      have : (ue : A) ∈ IsLocalRing.maximalIdeal A := by
        rw [key2]; exact Ideal.mul_mem_left _ _ hmm
      exact (IsLocalRing.mem_maximalIdeal _).mp this ue.isUnit

  have hμsum : ∀ (D : Divisor L F) (x : V), μ D x = ∑ Q ∈ D.support, D Q * μ (Finsupp.single Q 1) x := by
    intro D x
    have hD : μ D = D.sum fun Q k => μ (Finsupp.single Q k) := by
      conv_lhs => rw [← Finsupp.sum_single D]
      rw [map_finsuppSum]
    rw [hD, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro Q _
    rw [← Finsupp.smul_single_one Q (D Q), map_zsmul, Pi.smul_apply, smul_eq_mul]

  have hμQ : ∀ Q ∈ Dan.support, ∃ (e : Fin m) (d : ℕ) (hd0 : 0 < d) (hdw : d < w e),
      Q ∈ (An e).dom ∧ (∃ (u : Aˣ) (h : Q.evalAt (An e).param ∈ A), (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d) ∧
      μ (Finsupp.single Q 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1 := by
    intro Q hQ
    obtain ⟨e, hQe, d, u, h, hd⟩ := hDanC Q hQ
    obtain ⟨hd0, hdw⟩ := hdepth e Q hQe d u h hd
    exact ⟨e, d, hd0, hdw, hQe, ⟨u, h, hd⟩, h2 e Q hQe d u h hd hd0 hdw⟩

  have hmassA : ∀ (e : Fin m) (d : ℕ), ∀ S : Finset (Place L F),
      (∀ Q, Q ∈ S ↔ Q ∈ Dan.support ∧ Q ∈ (An e).dom ∧
        ∃ (u : Aˣ) (h : Q.evalAt (An e).param ∈ A), (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
      (S.sum fun Q => Dan Q) = 0 := by
    intro e d S hS
    by_cases hd : 0 < d ∧ d < w e
    · have hsub : S ⊆ Dan.support := fun Q hQ => ((hS Q).mp hQ).1
      have key : (S.sum fun Q => Dan Q) = μ Dan (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) := by
        rw [hμsum]
        symm
        rw [← Finset.sum_subset hsub ?hz]
        · refine Finset.sum_congr rfl ?_
          intro Q hQS
          obtain ⟨-, hQe, u, h, hdQ⟩ := (hS Q).mp hQS
          rw [h2 e Q hQe d u h hdQ hd.1 hd.2, Pi.single_eq_same, mul_one]
        · intro Q hQ hQS
          obtain ⟨e', d', hd0', hdw', hQe', ⟨u', h', hd'⟩, hμ⟩ := hμQ Q hQ
          rw [hμ, Pi.single_apply]
          split_ifs with heq
          · exfalso
            have heq' := Sum.inr.inj heq
            have hee : e = e' := congrArg Sigma.fst heq'
            subst hee
            have hdd : d - 1 = d' - 1 := by
              have := (Sigma.mk.inj_iff.mp heq').2
              exact Fin.mk.inj_iff.mp (eq_of_heq this)
            have hdd' : d' = d := by omega
            subst hdd'
            exact hQS ((hS Q).mpr ⟨hQ, hQe', u', h', hd'⟩)
          · rw [mul_zero]
      rw [key]
      exact hmassC _
    · have hS0 : S = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro Q hQS
        obtain ⟨-, hQe, u, h, hdQ⟩ := (hS Q).mp hQS
        exact hd (hdepth e Q hQe d u h hdQ)
      rw [hS0, Finset.sum_empty]

  obtain ⟨f, Df, hf0, hDf, hDfAnn, Di, hsumDi, hDisupp, hDideg⟩ :=
    AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus Dan hDanC hmassA
  refine ⟨f, Df, hf0, hDf, hDfAnn, ?_⟩
  intro i
  have hDan0 : μ Dan (Sum.inl i) = 0 := by
    rw [hμsum]
    refine Finset.sum_eq_zero ?_
    intro Q hQ
    obtain ⟨e', d', hd0', hdw', hQe', hu', hμ'⟩ := hμQ Q hQ
    rw [hμ', Pi.single_eq_of_ne Sum.inl_ne_inr, mul_zero]
  have hDi0 : ∀ j, μ (Di j) (Sum.inl i) = 0 := by
    intro j
    rw [hμsum]
    by_cases hji : j = i
    · subst hji
      have hdeg : ∑ Q ∈ (Di j).support, Di j Q = Divisor.degree (Di j) := by
        rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
        refine Finset.sum_congr rfl ?_
        intro Q hQ
        show Di j Q = Di j Q * (Q.deg : ℤ)
        rw [hdeg1 Q (hratF j Q (hDisupp j Q hQ)), mul_one]
      rw [← hDideg j, ← hdeg]
      refine Finset.sum_congr rfl ?_
      intro Q hQ
      rw [h1 j Q (hDisupp j Q hQ), Pi.single_eq_same, mul_one]
    · refine Finset.sum_eq_zero ?_
      intro Q hQ
      rw [h1 j Q (hDisupp j Q hQ), Pi.single_eq_of_ne (fun h => hji (Sum.inl_injective h).symm), mul_zero]
  have hDf_eq : Df = Dan + ∑ j, Di j := by rw [← hsumDi]; abel
  rw [hDf_eq, map_add, map_sum, Pi.add_apply, Finset.sum_apply, hDan0, zero_add]
  exact Finset.sum_eq_zero fun j _ => hDi0 j

end S_AlgebraicCurve_exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne (solution)
