-- Prove2me | solution 1 for AlgebraicCurve.exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7779c596-15a3-5617-8c22-d3a71117aba5

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_exists_multidegree_of_semistableCovering
import Theorems.Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
import Theorems.Thm_ValuationSubring_exists_pow_eq_unit_mul_zpow_of_isAlgebraic_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk"
p2m_attr_erase "simp" "ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.AlgebraicCurve"

namespace KummerLevelComb

theorem potential_apply {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (φ : V → ℤ) (v : V) :
    (∑ u, φ u • ((fun u => ∑ ε, ((if (ends ε).1 = u then (Pi.single u 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
        (if (ends ε).2 = u then (Pi.single u 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))) u)) v =
      ∑ ε, ((if (ends ε).1 = v then φ v - φ (ends ε).2 else 0) + (if (ends ε).2 = v then φ v - φ (ends ε).1 else 0)) := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ε _ => ?_

  have h1 : ∀ u, φ u * ((if (ends ε).1 = u then (Pi.single u 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) v) =
      if (ends ε).1 = u then φ (ends ε).1 * ((Pi.single (ends ε).1 1 : V → ℤ) v - (Pi.single (ends ε).2 1 : V → ℤ) v)
      else 0 := by
    intro u
    split_ifs with h
    · subst h; simp [Pi.sub_apply]
    · simp
  have h2 : ∀ u, φ u * ((if (ends ε).2 = u then (Pi.single u 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0) v) =
      if (ends ε).2 = u then φ (ends ε).2 * ((Pi.single (ends ε).2 1 : V → ℤ) v - (Pi.single (ends ε).1 1 : V → ℤ) v)
      else 0 := by
    intro u
    split_ifs with h
    · subst h; simp [Pi.sub_apply]
    · simp
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  by_cases ha : (ends ε).1 = v <;> by_cases hb : (ends ε).2 = v <;>
    simp [Pi.single_apply, ha, hb, eq_comm] <;> (try subst ha) <;> (try subst hb) <;> simp_all <;> ring

theorem potential_sub {V : Type*} [Fintype V] (lap : V → V → ℤ) (a b : V → ℤ) (v : V) :
    (∑ u, (a u - b u) • lap u) v = (∑ u, a u • lap u) v - (∑ u, b u • lap u) v := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]

theorem potential_mul {V : Type*} [Fintype V] (lap : V → V → ℤ) (q : ℤ) (a : V → ℤ) (v : V) :
    (∑ u, (q * a u) • lap u) v = q * (∑ u, a u • lap u) v := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

end KummerLevelComb

namespace KummerLevelComb

theorem potential_sum_eq_zero {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (φ : V → ℤ) :
    ∑ v, (∑ u, φ u • ((fun u => ∑ ε, ((if (ends ε).1 = u then (Pi.single u 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
        (if (ends ε).2 = u then (Pi.single u 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))) u)) v = 0 := by
  classical
  simp_rw [potential_apply ends φ]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ε _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

end KummerLevelComb

open KummerLevelComb in
theorem KummerLevel.comb_exists_sub_eq_laplacian_support_dvd
    (n m : ℕ) (src tgt : Fin m → Fin n) (w : Fin m → ℕ)
    (q M : ℕ) (hq : 0 < q) (hM : 0 < M) (hqM : ∀ e, q * M ∣ w e) (hw0 : ∀ e, w e ≠ 0) :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))
    let ends : (Σ e : Fin m, Fin (w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ (x φ : V → ℤ), (∀ v, (q : ℤ) * x v = (∑ u, φ u • lap u) v) →
      ∃ (y χ : V → ℤ), (∀ v, x v - y v = (∑ u, χ u • lap u) v) ∧
        ∀ (e : Fin m) (d : Fin (w e - 1)), y (Sum.inr ⟨e, d⟩) ≠ 0 → M ∣ (d : ℕ) + 1 := by
  intro V ends lap x φ hx
  classical

  have hinj : ∀ (e : Fin m) (a b : Fin (w e - 1)), (Sum.inr ⟨e, a⟩ : V) = Sum.inr ⟨e, b⟩ → (a : ℕ) = b := by
    intro e a b h
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact congrArg Fin.val h
  have hinj' : ∀ (e e' : Fin m) (a : Fin (w e' - 1)) (b : Fin (w e - 1)), e' ≠ e →
      (Sum.inr ⟨e', a⟩ : V) ≠ Sum.inr ⟨e, b⟩ := by
    intro e e' a b hne h
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
    exact hne h.1

  let pos : ∀ e : Fin m, ℕ → V := fun e p =>
    if h0 : p = 0 then Sum.inl (src e) else if hw : p < w e then Sum.inr ⟨e, ⟨p - 1, by omega⟩⟩ else Sum.inl (tgt e)
  have hends : ∀ (e : Fin m) (j : Fin (w e)), ends ⟨e, j⟩ = (pos e j, pos e (j + 1)) := by
    intro e j
    have hj := j.2
    simp only [ends, pos]
    ext
    · by_cases h0 : (j : ℕ) = 0
      · simp [h0]
      · simp [h0, hj]
    · by_cases h1 : (j : ℕ) + 1 = w e
      · simp [h1, hw0 e]
      · have : (j : ℕ) + 1 < w e := by omega
        simp [h1, this]
  have hposinr : ∀ (e : Fin m) (d : Fin (w e - 1)), pos e ((d : ℕ) + 1) = Sum.inr ⟨e, d⟩ := by
    intro e d
    have hd := d.2
    simp only [pos, Nat.add_one_ne_zero, dif_neg, not_false_eq_true]
    rw [dif_pos (by omega)]
    simp

  have hpos_eq : ∀ (e : Fin m) (d : Fin (w e - 1)) (p : ℕ), p ≤ w e → pos e p = Sum.inr ⟨e, d⟩ → p = (d : ℕ) + 1 := by
    intro e d p hp h
    simp only [pos] at h
    split_ifs at h with h0 hw
    · have := hinj e _ _ h
      simp only [Fin.val_mk] at this
      omega
  have hpos_ne : ∀ (e e' : Fin m) (d : Fin (w e - 1)) (p : ℕ), e' ≠ e → pos e' p ≠ Sum.inr ⟨e, d⟩ := by
    intro e e' d p hne h
    simp only [pos] at h
    split_ifs at h with h0 hw
    exact hinj' e e' _ _ hne h

  have heval : ∀ (ψ : V → ℤ) (e : Fin m) (d : Fin (w e - 1)),
      (∑ u, ψ u • lap u) (Sum.inr ⟨e, d⟩) =
        2 * ψ (Sum.inr ⟨e, d⟩) - ψ (pos e (d : ℕ)) - ψ (pos e ((d : ℕ) + 1 + 1)) := by
    intro ψ e d
    have hd := d.2
    rw [show (∑ u, ψ u • lap u) (Sum.inr ⟨e, d⟩) = _ from potential_apply ends ψ (Sum.inr ⟨e, d⟩)]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single e]
    · have key : ∀ j : Fin (w e),
          ((if (ends ⟨e, j⟩).1 = Sum.inr ⟨e, d⟩ then ψ (Sum.inr ⟨e, d⟩) - ψ (ends ⟨e, j⟩).2 else 0) +
            (if (ends ⟨e, j⟩).2 = Sum.inr ⟨e, d⟩ then ψ (Sum.inr ⟨e, d⟩) - ψ (ends ⟨e, j⟩).1 else 0)) =
          (if j = ⟨(d : ℕ) + 1, by omega⟩ then ψ (Sum.inr ⟨e, d⟩) - ψ (pos e ((d : ℕ) + 1 + 1)) else 0) +
            (if j = ⟨(d : ℕ), by omega⟩ then ψ (Sum.inr ⟨e, d⟩) - ψ (pos e (d : ℕ)) else 0) := by
        intro j
        rw [hends]
        simp only
        congr 1
        · by_cases hj : j = ⟨(d : ℕ) + 1, by omega⟩
          · subst hj
            rw [if_pos rfl, if_pos (hposinr e d)]
          · rw [if_neg hj, if_neg]
            intro h
            exact hj (Fin.ext (hpos_eq e d j (le_of_lt j.2) h))
        · by_cases hj : j = ⟨(d : ℕ), by omega⟩
          · subst hj
            rw [if_pos rfl, if_pos (hposinr e d)]
          · rw [if_neg hj, if_neg]
            intro h
            have := hpos_eq e d ((j : ℕ) + 1) (by omega) h
            exact hj (Fin.ext (by simp only [Fin.val_mk]; omega))
      rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      ring
    · intro e' _ hne
      apply Finset.sum_eq_zero
      intro j _
      rw [hends]
      simp only
      rw [if_neg (hpos_ne e e' d _ hne), if_neg (hpos_ne e e' d _ hne), add_zero]
    · intro h
      exact absurd (Finset.mem_univ e) h

  have hpos0 : ∀ e : Fin m, pos e 0 = Sum.inl (src e) := fun e => by simp [pos]
  have hposw : ∀ e : Fin m, pos e (w e) = Sum.inl (tgt e) := fun e => by simp [pos, hw0 e]
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'

  have hq1 : ∀ e : Fin m, ¬ 0 < w e - 1 → q = 1 := by
    intro e h
    have hwe : w e = 1 := by have := hw0 e; omega
    have h1 : q * M ∣ 1 := hwe ▸ hqM e
    have := Nat.eq_one_of_mul_eq_one_right (Nat.dvd_one.mp h1)
    exact this

  let s : Fin m → ℤ := fun e => if h : 0 < w e - 1 then φ (Sum.inr ⟨e, ⟨0, h⟩⟩) - φ (Sum.inl (src e)) else 0
  have hslope : ∀ (e : Fin m) (p : ℕ), p + 1 ≤ w e →
      (q : ℤ) ∣ (φ (pos e (p + 1)) - φ (pos e p)) - s e := by
    intro e p
    induction p with
    | zero =>
      intro h1
      by_cases h : 0 < w e - 1
      · have : pos e (0 + 1) = Sum.inr ⟨e, ⟨0, h⟩⟩ := hposinr e ⟨0, h⟩
        rw [this, hpos0]
        simp only [s, dif_pos h, sub_self, dvd_zero]
      · rw [hq1 e h]
        simp
    | succ p ih =>
      intro hp
      have hd : p < w e - 1 := by omega
      have h1 := hx (Sum.inr ⟨e, ⟨p, hd⟩⟩)
      rw [heval φ e ⟨p, hd⟩] at h1
      have h2 : Sum.inr ⟨e, ⟨p, hd⟩⟩ = pos e (p + 1) := (hposinr e ⟨p, hd⟩).symm
      rw [h2] at h1
      simp only [Fin.val_mk] at h1
      have ih' := ih (by omega)
      have : φ (pos e (p + 1 + 1)) - φ (pos e (p + 1)) - s e =
          (φ (pos e (p + 1)) - φ (pos e p) - s e) - (q : ℤ) * x (pos e (p + 1)) := by
        rw [h1]; ring
      rw [this]
      exact dvd_sub ih' (dvd_mul_right _ _)
  have hlin : ∀ (e : Fin m) (p : ℕ), p ≤ w e →
      (q : ℤ) ∣ φ (pos e p) - (φ (Sum.inl (src e)) + (p : ℤ) * s e) := by
    intro e p
    induction p with
    | zero => intro; rw [hpos0]; simp
    | succ p ih =>
      intro hp
      have h1 := hslope e p hp
      have h2 := ih (by omega)
      have : φ (pos e (p + 1)) - (φ (Sum.inl (src e)) + ((p + 1 : ℕ) : ℤ) * s e) =
          (φ (pos e (p + 1)) - φ (pos e p) - s e) + (φ (pos e p) - (φ (Sum.inl (src e)) + (p : ℤ) * s e)) := by
        push_cast; ring
      rw [this]
      exact dvd_add h1 h2

  have hends_mod : ∀ e : Fin m, φ (Sum.inl (tgt e)) % (q : ℤ) = φ (Sum.inl (src e)) % (q : ℤ) := by
    intro e
    have h := hlin e (w e) le_rfl
    rw [hposw] at h
    obtain ⟨t, ht⟩ := hqM e
    have hqw : (q : ℤ) ∣ ((w e : ℕ) : ℤ) * s e := by
      refine Dvd.dvd.mul_right ?_ _
      exact_mod_cast (⟨M * t, by rw [ht, mul_assoc]⟩ : q ∣ w e)
    have : (q : ℤ) ∣ φ (Sum.inl (tgt e)) - φ (Sum.inl (src e)) := by
      have := dvd_add h hqw
      have e1 : φ (Sum.inl (tgt e)) - (φ (Sum.inl (src e)) + (w e : ℤ) * s e) + (w e : ℤ) * s e =
          φ (Sum.inl (tgt e)) - φ (Sum.inl (src e)) := by ring
      rwa [e1] at this
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr (Int.emod_eq_zero_of_dvd this)

  let K : Fin m → ℕ := fun e => w e / M
  have hMdvd : ∀ e, M ∣ w e := fun e => dvd_trans (dvd_mul_left M q) (hqM e)
  have hMK : ∀ e, (M : ℤ) * (K e : ℤ) = (w e : ℤ) := by
    intro e
    have : M * (w e / M) = w e := Nat.mul_div_cancel' (hMdvd e)
    exact_mod_cast this
  have hMle : ∀ e, M ≤ w e := fun e => Nat.le_of_dvd (Nat.pos_of_ne_zero (hw0 e)) (hMdvd e)
  have hqK : ∀ e, (q : ℤ) ∣ (K e : ℤ) := by
    intro e
    obtain ⟨t, ht⟩ := hqM e
    have : K e = q * t := by
      show w e / M = q * t
      exact Nat.div_eq_of_eq_mul_left hM (by rw [ht]; ring)
    rw [this]
    push_cast
    exact dvd_mul_right _ _
  let c : Fin m → ℤ := fun e => φ (Sum.inl (src e)) % (q : ℤ)
  let R : Fin m → ℕ → ℤ := fun e p =>
    c e + (p : ℤ) * s e - (if p ≤ M then (p : ℤ) else (M : ℤ)) * (K e : ℤ) * s e
  let r : V → ℤ := fun v => match v with
    | Sum.inl i => φ (Sum.inl i) % (q : ℤ)
    | Sum.inr ⟨e, d⟩ => R e ((d : ℕ) + 1)

  have hR0 : ∀ e, R e 0 = c e := by intro e; simp [R]
  have hRw : ∀ e, R e (w e) = c e := by
    intro e
    simp only [R]
    by_cases h : w e ≤ M
    · have hwM : w e = M := le_antisymm h (hMle e)
      have hK1 : (K e : ℤ) = 1 := by
        have : K e = 1 := by show w e / M = 1; rw [hwM]; exact Nat.div_self hM
        exact_mod_cast this
      rw [if_pos h, hK1]; ring
    · rw [if_neg h, hMK]; ring
  have hrpos : ∀ (e : Fin m) (p : ℕ), p ≤ w e → r (pos e p) = R e p := by
    intro e p hp
    by_cases h0 : p = 0
    · subst h0; rw [hpos0, hR0]
    · by_cases hw : p < w e
      · have : pos e p = Sum.inr ⟨e, ⟨p - 1, by omega⟩⟩ := by simp [pos, h0, hw]
        rw [this]
        show R e (p - 1 + 1) = R e p
        rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
      · have hpw : p = w e := by omega
        subst hpw
        rw [hposw, hRw]
        show φ (Sum.inl (tgt e)) % (q : ℤ) = c e
        exact hends_mod e

  have hcong : ∀ v, (q : ℤ) ∣ φ v - r v := by
    rintro (i | ⟨e, d⟩)
    · show (q : ℤ) ∣ φ (Sum.inl i) - φ (Sum.inl i) % (q : ℤ)
      rw [Int.emod_def]; exact ⟨φ (Sum.inl i) / (q : ℤ), by ring⟩
    · have hd := d.2
      show (q : ℤ) ∣ φ (Sum.inr ⟨e, d⟩) - R e ((d : ℕ) + 1)
      have h1 := hlin e ((d : ℕ) + 1) (by omega)
      rw [hposinr] at h1
      have h2 : (q : ℤ) ∣ φ (Sum.inl (src e)) - c e := by
        show (q : ℤ) ∣ φ (Sum.inl (src e)) - φ (Sum.inl (src e)) % (q : ℤ)
        rw [Int.emod_def]; exact ⟨φ (Sum.inl (src e)) / (q : ℤ), by ring⟩
      have h3 : (q : ℤ) ∣ (if (d : ℕ) + 1 ≤ M then (((d : ℕ) + 1 : ℕ) : ℤ) else (M : ℤ)) * (K e : ℤ) * s e :=
        Dvd.dvd.mul_right (Dvd.dvd.mul_left (hqK e) _) _
      have : φ (Sum.inr ⟨e, d⟩) - R e ((d : ℕ) + 1) =
          (φ (Sum.inr ⟨e, d⟩) - (φ (Sum.inl (src e)) + (((d : ℕ) + 1 : ℕ) : ℤ) * s e)) +
          (φ (Sum.inl (src e)) - c e) +
          (if (d : ℕ) + 1 ≤ M then (((d : ℕ) + 1 : ℕ) : ℤ) else (M : ℤ)) * (K e : ℤ) * s e := by
        simp only [R]; ring
      rw [this]
      exact dvd_add (dvd_add h1 h2) h3

  have hR2 : ∀ (e : Fin m) (d : ℕ), d + 1 ≠ M →
      2 * R e (d + 1) - R e d - R e (d + 2) = 0 := by
    intro e d hdM
    simp only [R]
    by_cases h1 : d + 2 ≤ M
    · rw [if_pos (by omega : d + 1 ≤ M), if_pos (by omega : d ≤ M), if_pos h1]
      push_cast; ring
    · by_cases h2 : d ≤ M
      ·
        have hdM' : d = M := by omega
        rw [if_neg (by omega : ¬ d + 1 ≤ M), if_pos h2, if_neg h1, hdM']
        push_cast; ring
      · rw [if_neg (by omega : ¬ d + 1 ≤ M), if_neg h2, if_neg h1]
        push_cast; ring
  have hLr : ∀ (e : Fin m) (d : Fin (w e - 1)), (d : ℕ) + 1 ≠ M →
      (∑ u, r u • lap u) (Sum.inr ⟨e, d⟩) = 0 := by
    intro e d hdM
    have hd := d.2
    rw [heval r e d, ← hposinr e d, hrpos e _ (by omega), hrpos e _ (by omega), hrpos e _ (by omega)]
    exact hR2 e d hdM

  let χ : V → ℤ := fun v => (φ v - r v) / (q : ℤ)
  have hχ : ∀ v, (q : ℤ) * χ v = φ v - r v := fun v => Int.mul_ediv_cancel' (hcong v)
  refine ⟨fun v => x v - (∑ u, χ u • lap u) v, χ, fun v => by ring, ?_⟩
  intro e d hy
  by_contra hdM
  have hne : (d : ℕ) + 1 ≠ M := fun h => hdM (h ▸ dvd_refl _)
  apply hy
  have hqy : (q : ℤ) * (x (Sum.inr ⟨e, d⟩) - (∑ u, χ u • lap u) (Sum.inr ⟨e, d⟩)) = 0 := by
    rw [mul_sub, hx, ← potential_mul lap (q : ℤ) χ]
    have : (∑ u, ((q : ℤ) * χ u) • lap u) = ∑ u, (φ u - r u) • lap u :=
      Finset.sum_congr rfl fun u _ => by rw [hχ u]
    rw [this, potential_sub, sub_sub_cancel, hLr e d hne]
  exact (mul_eq_zero.mp hqy).resolve_left hq0

namespace P2mWs20FiniteRep

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem mem_and_isUnit_of_pow_eq {x : L} {N : ℕ} (hN : N ≠ 0) {v : A} (hv : IsUnit v) (hx : x ^ N = (v : L)) :
    ∃ hxA : x ∈ A, IsUnit (⟨x, hxA⟩ : A) := by
  have hv1 : A.valuation (v : L) = 1 := (A.valuation_eq_one_iff v).mp hv
  have hx1 : A.valuation x = 1 := by
    have h : A.valuation x ^ N = 1 := by rw [← map_pow, hx, hv1]
    exact (pow_eq_one_iff.mp h).resolve_right hN
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx1.le
  exact ⟨hxA, (A.valuation_eq_one_iff ⟨x, hxA⟩).mpr hx1⟩

theorem mem_and_mem_maximalIdeal_of_pow_eq {x : L} {N : ℕ} (hN : N ≠ 0) {π : A} (hπ : π ∈ maximalIdeal A)
    (hx : x ^ N = (π : L)) : ∃ hxA : x ∈ A, (⟨x, hxA⟩ : A) ∈ maximalIdeal A := by
  have hπ1 : A.valuation (π : L) < 1 := (A.valuation_lt_one_iff π).mp hπ
  have hx1 : A.valuation x < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ A.valuation x ^ N := one_le_pow₀ h
    rw [← map_pow, hx] at this
    exact not_lt.mpr this hπ1
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx1.le
  exact ⟨hxA, (A.valuation_lt_one_iff ⟨x, hxA⟩).mpr hx1⟩

end P2mWs20FiniteRep

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Divisor Divisor.degree Divisor.degZero Divisor.mem_degZero Divisor.principal Divisor.mem_principal HasPrincipalDivisors Pic0 Pic0.mk Pic0.mk_surjective HasPrincipalDivisors.exists_divisor genusFF IsCurveOver SemistableModel exists_multidegree_of_semistableCovering exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_coe_unit algebraMap_mem' toValuationSubring mk IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero_mp (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra hnu
    apply hres
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

p2m_export "AlgebraicCurve.Place" "ord_eq_zero_of_evalAt_ne_zero_mp"

private theorem _root_.AlgebraicCurve.Place.evalAt_sub_of_mem_mp (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, v.algebraMap_evalAt hv (sub_mem hf hg),
    ← map_sub]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_sub_of_mem_mp"

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap_mp (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have : IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩ =
      algebraMap K v.ResidueField a := rfl
  rw [this, v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_algebraMap_mp"

theorem deg_eq_one_of_isRational_mp {v : Place K F} (hv : v.IsRational) : v.deg = 1 := by
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    ⟨v.algebraMap_residueField_injective, hv⟩
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem mk dom mem_dom param ord_param_sub"
p2m_open "AlgebraicCurve.Annulus"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem ord_param_eq_zero_mp (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.ord An.param = 0 := by
  obtain ⟨-, hz, -, hne, -⟩ := An.mem_dom P hP
  exact P.ord_eq_zero_of_evalAt_ne_zero_mp hz hne

theorem ord_param_sub_evalAt_mp (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.ord (An.param - algebraMap L F (P.evalAt An.param)) = 1 :=
  An.ord_param_sub P hP

theorem ord_param_sub_evalAt_mp_of_ne (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom)
    (hQ : Q ∈ An.dom) (hPQ : P ≠ Q) : Q.ord (An.param - algebraMap L F (P.evalAt An.param)) = 0 := by
  obtain ⟨hQrat, hzQ, -, -, -⟩ := An.mem_dom Q hQ
  obtain ⟨-, -, ⟨hPA, hPm⟩, hP0, hPmod⟩ := An.mem_dom P hP
  refine Q.ord_eq_zero_of_evalAt_ne_zero_mp (sub_mem hzQ (Q.algebraMap_mem' _)) ?_
  rw [Q.evalAt_sub_of_mem_mp hQrat hzQ (Q.algebraMap_mem' _), Q.evalAt_algebraMap_mp, sub_ne_zero]
  intro hEq
  obtain ⟨R, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨P.evalAt An.param, hPA⟩ hPm hP0 hPmod
  exact hPQ ((huniq P ⟨hP, rfl⟩).trans (huniq Q ⟨hQ, hEq⟩).symm)

private theorem _root_.AlgebraicCurve.Annulus.depth_pos_and_lt_mp (An : Annulus A F) {π : A} (hπ0 : π ≠ 0)
    {w : ℕ} (hw : ∃ u : Aˣ, An.modulus = u * π ^ w)
    {P : Place L F} (hP : P ∈ An.dom) {d : ℕ} {u : Aˣ} {h : P.evalAt An.param ∈ A}
    (hd : (⟨P.evalAt An.param, h⟩ : A) = u * π ^ d) : 0 < d ∧ d < w := by
  obtain ⟨-, -, ⟨hA, hm⟩, hne, m', hm', hmod⟩ := An.mem_dom P hP
  obtain ⟨u', hu'⟩ := hw
  have hAeq : (⟨P.evalAt An.param, hA⟩ : A) = u * π ^ d := hd
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exfalso
      rw [pow_zero, mul_one] at hAeq
      rw [hAeq] at hm
      exact (IsLocalRing.mem_maximalIdeal _).mp hm u.isUnit
    · exact hd0
  refine ⟨hd0, ?_⟩
  by_contra hdw
  push Not at hdw

  have hmodA : (u' : A) * π ^ w = (u * π ^ d) * m' := by
    rw [← hu', ← hAeq]
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    exact hmod
  have hsplit : (π : A) ^ d = π ^ (d - w) * π ^ w := by rw [← pow_add, Nat.sub_add_cancel hdw]
  rw [hsplit] at hmodA
  have hu'eq : (u' : A) = u * π ^ (d - w) * m' := by
    apply mul_right_cancel₀ (pow_ne_zero w hπ0)
    rw [hmodA]; ring
  apply (IsLocalRing.mem_maximalIdeal _).mp _ u'.isUnit
  rw [hu'eq]
  exact Ideal.mul_mem_left _ _ hm'

p2m_export "AlgebraicCurve.Annulus" "depth_pos_and_lt_mp"

theorem depth_unique_mp {π : A} (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
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

end Annulus

end AlgebraicCurve

theorem FiniteRep.muPot
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
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
    (q Mdiv : ℕ) (hq : 0 < q) (hMdiv : 0 < Mdiv)
    (ϖ : A) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖ0 : ϖ ≠ 0)
    (hWmod : ∀ e, ∃ u : Aˣ, (An e).modulus = u * ϖ ^ (q * Mdiv * w e))
    (D₀ : Divisor L F)
    (hD₀lat : ∀ P ∈ D₀.support, (∃ i, P ∈ (C i).dom) ∨
      ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d)
    (f₀ : F) (hf₀ : f₀ ≠ 0) (hdiv : ∀ P, ((q : ℤ) • D₀) P = P.ord f₀)
    :
    let W : Fin m → ℕ := fun e => q * Mdiv * w e
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∃ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) ∧
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d → ∀ (hd0 : 0 < d) (hdw : d < W e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) ∧
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) → μ (Finsupp.single P 1) = 0) ∧
      (∃ φc : V → ℤ, ∀ v, (q : ℤ) * μ D₀ v = (∑ u, φc u • lap u) v) ∧
      (∑ v, μ D₀ v = Divisor.degree D₀) := by
  intro W V ends lap
  classical
  have _ := hratBar; have _ := hq; have _ := hMdiv

  have hV : ∀ P : Place L F, ∃ v : V → ℤ,
      (∀ i, P ∈ (C i).dom → v = Pi.single (Sum.inl i) 1) ∧
      (∀ e, P ∈ (An e).dom → ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d → ∀ (hd0 : 0 < d) (hdw : d < W e),
          v = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) ∧
      (∀ e, P ∈ (An e).dom → (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) → v = 0) ∧
      ((∃ i, P ∈ (C i).dom) ∨ (∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) → ∑ x, v x = 1) := by
    intro P
    rcases hcover P with ⟨i, hi, huniq, hnot⟩ | ⟨e, he, huniq, hnot⟩
    · refine ⟨Pi.single (Sum.inl i) 1, fun j hj => by rw [huniq j hj], fun e he => absurd he (hnot e),
        fun e he => absurd he (hnot e), fun _ => by simp⟩
    · by_cases hlat : ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d
      · obtain ⟨d, u, h, hd⟩ := hlat
        obtain ⟨hd0, hdw⟩ := (An e).depth_pos_and_lt_mp hϖ0 (hWmod e) he hd
        have hdwW : d < W e := hdw
        refine ⟨Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1, fun j hj => absurd hj (hnot j), ?_, ?_, fun _ => by simp⟩
        · intro e' he' d' u' h' hd' hd0' hdw'
          obtain rfl : e' = e := huniq e' he'
          obtain rfl : d = d' := Annulus.depth_unique_mp hϖ hϖ0 hd hd'
          rfl
        · intro e' he' hno
          obtain rfl : e' = e := huniq e' he'
          exact absurd ⟨d, u, h, hd⟩ hno
      · refine ⟨0, fun j hj => absurd hj (hnot j), ?_, fun _ _ _ => rfl, ?_⟩
        · intro e' he' d' u' h' hd' _ _
          obtain rfl : e' = e := huniq e' he'
          exact absurd ⟨d', u', h', hd'⟩ hlat
        · rintro (⟨i, hi⟩ | ⟨e', he', hlat'⟩)
          · exact absurd hi (hnot i)
          · obtain rfl : e' = e := huniq e' he'
            exact absurd hlat' hlat
  choose vec hvecC hvecA hvec0 hvecsum using hV

  let μ : Divisor L F →+ (V → ℤ) := Finsupp.liftAddHom fun P => zmultiplesHom (V → ℤ) (vec P)
  have hμ_single : ∀ P (k : ℤ), μ (Finsupp.single P k) = k • vec P := by
    intro P k
    simp only [μ, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
  have hμC : ∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1 := by
    intro i P hP; rw [hμ_single, one_smul, hvecC P i hP]
  have hμA : ∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d → ∀ (hd0 : 0 < d) (hdw : d < W e),
        μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1 := by
    intro e P hP d u h hd hd0 hdw; rw [hμ_single, one_smul, hvecA P e hP d u h hd hd0 hdw]
  have hμ0 : ∀ e, ∀ P ∈ (An e).dom, (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) → μ (Finsupp.single P 1) = 0 := by
    intro e P hP hno; rw [hμ_single, one_smul, hvec0 P e hP hno]

  obtain ⟨φ, hφC, hφA, hφ0, hφdiv⟩ :=
    AlgebraicCurve.exists_multidegree_of_semistableCovering A ϖ hϖ hϖ0 F n m Fbar hratBar C hratF An An' src tgt
      xs xt W hpair hWmod hatt hnodes hcover
  have hφμ : φ = (QuotientAddGroup.mk' _).comp μ := by
    refine Finsupp.addHom_ext' fun P => AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, QuotientAddGroup.mk'_apply]
    rcases hcover P with ⟨i, hi, -, -⟩ | ⟨e, he, -, -⟩
    · rw [hφC i P hi, hμC i P hi]
    · by_cases hlat : ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d
      · obtain ⟨d, u, h, hd⟩ := hlat
        obtain ⟨hd0, hdw⟩ := (An e).depth_pos_and_lt_mp hϖ0 (hWmod e) he hd
        have hdwW : d < W e := hdw
        rw [hφA e P he d u h hd hd0 hdwW, hμA e P he d u h hd hd0 hdwW]
      · rw [hφ0 e P he hlat, hμ0 e P he hlat, QuotientAddGroup.mk_zero]

  have hlatq : ∀ P ∈ (((q : ℤ) • D₀)).support, (∃ i, P ∈ (C i).dom) ∨
      ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d := by
    intro P hP
    exact hD₀lat P (Finsupp.support_smul hP)
  have hφq : φ ((q : ℤ) • D₀) = 0 := hφdiv f₀ hf₀ _ hdiv hlatq
  have hmem : μ ((q : ℤ) • D₀) ∈ AddSubgroup.closure (Set.range lap) := by
    rw [← QuotientAddGroup.eq_zero_iff]
    have := hφq
    rw [hφμ] at this
    exact this
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem

  have hμ_sum : ∀ X : Divisor L F, μ X = X.sum fun P k => k • vec P := by
    intro X
    simp only [μ, Finsupp.liftAddHom_apply, Finsupp.sum, zmultiplesHom_apply]
  have hrat : ∀ P ∈ D₀.support, P.IsRational := by
    intro P hP
    rcases hD₀lat P hP with ⟨i, hi⟩ | ⟨e, he, -⟩
    · exact hratF i P hi
    · exact ((An e).mem_dom P he).1
  have hdeg : (∑ v, μ D₀ v) = Divisor.degree D₀ := by
    rw [hμ_sum, Finsupp.sum]
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    have hdegD : Divisor.degree D₀ = D₀.sum fun P k => k * (P.deg : ℤ) := by
      simp only [Divisor.degree, Finsupp.liftAddHom_apply]
      rfl
    rw [hdegD, Finsupp.sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [hvecsum P (hD₀lat P hP), Place.deg_eq_one_of_isRational_mp (hrat P hP)]
    simp
  refine ⟨μ, hμC, hμA, hμ0, ⟨c, fun v => ?_⟩, hdeg⟩
  have : (q : ℤ) * μ D₀ v = (μ ((q : ℤ) • D₀)) v := by
    rw [map_zsmul, Pi.smul_apply, smul_eq_mul]
  rw [this, ← hc]

namespace KLB45

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem exists_latticePlace (An : Annulus A F) (ϖ : A) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖ0 : ϖ ≠ 0)
    (N t : ℕ) (u : Aˣ) (hmod : An.modulus = u * ϖ ^ N) (ht0 : 0 < t) (htN : t < N) :
    ∃ P : Place L F, P ∈ An.dom ∧ P.evalAt An.param = ((ϖ ^ t : A) : L) := by
  have hmem : ϖ ^ t ∈ IsLocalRing.maximalIdeal A := Ideal.pow_mem_of_mem _ hϖ t ht0
  have hne : ((ϖ ^ t : A) : L) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ (fun h => hϖ0 (Subtype.ext h))
  have hdiv : ∃ m ∈ IsLocalRing.maximalIdeal A, (An.modulus : L) = ((ϖ ^ t : A) : L) * m := by
    obtain ⟨s, rfl, hs0⟩ : ∃ s, N = t + s ∧ 0 < s := ⟨N - t, by omega, by omega⟩
    refine ⟨(u : A) * ϖ ^ s, Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hϖ s hs0), ?_⟩
    rw [hmod, pow_add]
    push_cast
    ring
  obtain ⟨P, hP, -⟩ := An.existsUnique_evalAt_eq (ϖ ^ t) hmem hne hdiv
  exact ⟨P, hP⟩

end KLB45

theorem FiniteRep.step45
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
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
    (q Mdiv : ℕ) (hq : 0 < q) (hMdiv : 0 < Mdiv)
    (ϖ : A) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖ0 : ϖ ≠ 0) (hϖπ : ϖ ^ (q * Mdiv) = π)
    (D₀ : Divisor L F) (hD₀ : Divisor.degree D₀ = 0)
    (hD₀lat : ∀ P ∈ D₀.support, (∃ i, P ∈ (C i).dom) ∨
      ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d)
    :
    let W : Fin m → ℕ := fun e => q * Mdiv * w e
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d → ∀ (hd0 : 0 < d) (hdw : d < W e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) → μ (Finsupp.single P 1) = 0) →
      ∀ (y χ : V → ℤ),
        (∀ v, μ D₀ v - y v = (∑ u, χ u • lap u) v) →
        (∀ (e : Fin m) (d : Fin (W e - 1)), y (Sum.inr ⟨e, d⟩) ≠ 0 → Mdiv ∣ (d : ℕ) + 1) →
        (∑ v, y v) = 0 →
        ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
          D₀ - D ∈ Divisor.principal (K := L) (F := F) ∧
          ∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
            ∃ e, P ∈ (An e).dom ∧ ∃ (v : Aˣ) (j : ℕ),
              (P.evalAt (An e).param) ^ q = ((v : A) : L) * (π : L) ^ j := by
  intro W V ends lap μ hμC hμL hμN y χ hcomb hyM hysum
  classical

  have hwϖ : ∀ e, ∃ u : Aˣ, (An e).modulus = u * ϖ ^ W e := by
    intro e
    obtain ⟨u, hu⟩ := hw e
    refine ⟨u, ?_⟩
    show (An e).modulus = u * ϖ ^ (q * Mdiv * w e)
    rw [hu, ← hϖπ, ← pow_mul]

  have hENG := AlgebraicCurve.exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
      A ϖ hϖ hϖ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt W hpair hwϖ hatt hnodes hcover hdisc hgenus

  have hadm : ∀ v : (Σ e : Fin m, Fin (W e - 1)),
      ∃ P : Place L F, P ∈ (An v.1).dom ∧ P.evalAt (An v.1).param = ((ϖ ^ (v.2.1 + 1) : A) : L) := by
    intro v
    obtain ⟨u, hu⟩ := hwϖ v.1
    have hv := v.2.isLt
    exact KLB45.exists_latticePlace (An v.1) ϖ hϖ hϖ0 (W v.1) (v.2.1 + 1) u hu (by omega) (by omega)
  choose Pl hPl using hadm
  have hPl_dom : ∀ v, Pl v ∈ (An v.1).dom := fun v => (hPl v).1
  have hPl_val : ∀ v, (Pl v).evalAt (An v.1).param = ((ϖ ^ (v.2.1 + 1) : A) : L) := fun v => (hPl v).2
  have hPl_mem : ∀ v, (Pl v).evalAt (An v.1).param ∈ A := fun v => by rw [hPl_val v]; exact (ϖ ^ (v.2.1 + 1)).2
  have hPl_lat : ∀ v, (⟨(Pl v).evalAt (An v.1).param, hPl_mem v⟩ : A) = (1 : Aˣ) * ϖ ^ (v.2.1 + 1) := by
    intro v
    apply Subtype.ext
    simp only [Units.val_one, one_mul]
    exact hPl_val v
  have hμPl : ∀ v, μ (Finsupp.single (Pl v) 1) = Pi.single (Sum.inr v) 1 := by
    intro v
    have hv := v.2.isLt
    rw [hμL v.1 (Pl v) (hPl_dom v) (v.2.1 + 1) 1 (hPl_mem v) (hPl_lat v) (by omega) (by omega)]
    have hfin : (⟨v.2.1 + 1 - 1, by omega⟩ : Fin (W v.1 - 1)) = v.2 := Fin.ext (by simp)
    rw [hfin]

  let isA : Place L F → Prop := fun P => ∃ e, P ∈ (An e).dom
  let D0a : Divisor L F := D₀.filter isA
  let D1a : Divisor L F := ∑ v : (Σ e : Fin m, Fin (W e - 1)), y (Sum.inr v) • Finsupp.single (Pl v) 1
  have hμD1a : ∀ v' : (Σ e : Fin m, Fin (W e - 1)), μ D1a (Sum.inr v') = y (Sum.inr v') := by
    intro v'
    show μ (∑ v : (Σ e : Fin m, Fin (W e - 1)), y (Sum.inr v) • Finsupp.single (Pl v) 1) (Sum.inr v') = y (Sum.inr v')
    rw [map_sum, Finset.sum_apply]
    simp_rw [map_zsmul, hμPl, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single v']
    · simp
    · intro v _ hv
      rw [if_neg (fun h => hv (Sum.inr_injective h).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ v') h
  have hμD0c : ∀ v' : (Σ e : Fin m, Fin (W e - 1)), μ (D₀.filter (fun P => ¬ isA P)) (Sum.inr v') = 0 := by
    intro v'
    have hsum : D₀.filter (fun P => ¬ isA P) =
        ∑ P ∈ (D₀.filter (fun P => ¬ isA P)).support, Finsupp.single P ((D₀.filter (fun P => ¬ isA P)) P) :=
      (Finsupp.sum_single _).symm
    rw [hsum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun P hP => ?_)
    rw [Finsupp.support_filter, Finset.mem_filter] at hP
    obtain ⟨hP0, hPc⟩ := hP
    rcases hD₀lat P hP0 with ⟨i, hi⟩ | ⟨e, he, -⟩
    · rw [← Finsupp.smul_single_one, map_zsmul, hμC i P hi]
      simp [Pi.single_apply]
    · exact absurd ⟨e, he⟩ hPc
  have hμD0a : ∀ v' : (Σ e : Fin m, Fin (W e - 1)), μ D0a (Sum.inr v') = μ D₀ (Sum.inr v') := by
    intro v'
    conv_rhs => rw [← Finsupp.filter_add_filter_not D₀ isA]
    rw [map_add, Pi.add_apply, hμD0c, add_zero]

  let Dan : Divisor L F := D0a - D1a
  have hDanlat : ∀ P ∈ Dan.support, ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d := by
    intro P hP
    have hP' := Finsupp.support_sub (f := D0a) (g := D1a) hP
    rcases Finset.mem_union.mp hP' with h0 | h1
    · have h0' : P ∈ D₀.support ∧ isA P := by
        have := h0; rw [Finsupp.support_filter, Finset.mem_filter] at this; exact this
      obtain ⟨e, he⟩ := h0'.2
      rcases hD₀lat P h0'.1 with ⟨i, hi⟩ | h
      · rcases hcover P with ⟨i', -, -, hno⟩ | ⟨e', -, -, hno⟩
        · exact absurd he (hno e)
        · exact absurd hi (hno i)
      · exact h
    · have h1' := Finsupp.support_finsetSum
        (s := (Finset.univ : Finset (Σ e : Fin m, Fin (W e - 1))))
        (f := fun v => y (Sum.inr v) • Finsupp.single (Pl v) 1) h1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h1'
      obtain ⟨v, hv⟩ := h1'
      have hPv : P = Pl v := by
        have := Finsupp.support_smul hv
        exact Finset.mem_singleton.mp (Finsupp.support_single_subset this)
      subst hPv
      exact ⟨v.1, hPl_dom v, v.2.1 + 1, 1, hPl_mem v, hPl_lat v⟩
  have hmass : ∀ v : (Σ e : Fin m, Fin (W e - 1)), μ Dan (Sum.inr v) = (∑ u, χ u • lap u) (Sum.inr v) := by
    intro v
    show μ (D0a - D1a) (Sum.inr v) = (∑ u, χ u • lap u) (Sum.inr v)
    rw [map_sub, Pi.sub_apply, hμD0a, hμD1a]
    exact hcomb (Sum.inr v)

  obtain ⟨f, Df, hf0, hDf, hDfan, -⟩ := hENG μ hμC hμL hμN χ Dan hDanlat hmass
  have hDfdeg : Divisor.degree Df = 0 := by
    obtain ⟨E, hE, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) f hf0
    have : Df = E := Finsupp.ext (fun P => by rw [hDf P, hE P])
    rw [this]; exact hEdeg
  refine ⟨D₀ - Df, ?_, ?_, ?_⟩
  · rw [Divisor.mem_degZero, map_sub, hD₀, hDfdeg, sub_zero]
  · rw [sub_sub_cancel]
    exact ⟨f, hf0, hDf⟩
  · intro P hP
    rcases hcover P with ⟨i, hi, -, -⟩ | ⟨e, he, huniq, hnoC⟩
    · exact Or.inl ⟨i, hi⟩
    · right

      have hval : (D₀ - Df) P = D1a P := by
        rw [Finsupp.sub_apply, hDfan e P he]
        show D₀ P - (D0a - D1a) P = D1a P
        rw [Finsupp.sub_apply]
        have : D0a P = D₀ P := by
          show (D₀.filter isA) P = D₀ P
          rw [Finsupp.filter_apply, if_pos ⟨e, he⟩]
        rw [this]; ring
      have hP1 : P ∈ D1a.support := by
        rw [Finsupp.mem_support_iff] at hP ⊢
        rwa [hval] at hP
      have h1' := Finsupp.support_finsetSum
        (s := (Finset.univ : Finset (Σ e : Fin m, Fin (W e - 1))))
        (f := fun v => y (Sum.inr v) • Finsupp.single (Pl v) 1) hP1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h1'
      obtain ⟨v, hv⟩ := h1'
      have hy : y (Sum.inr v) ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hv; simp at hv
      have hPv : P = Pl v := by
        have := Finsupp.support_smul hv
        exact Finset.mem_singleton.mp (Finsupp.support_single_subset this)

      obtain ⟨j, hj⟩ := hyM v.1 v.2 (by
        have : (⟨v.1, v.2⟩ : (Σ e : Fin m, Fin (W e - 1))) = v := rfl
        rw [this]; exact hy)
      refine ⟨v.1, hPv ▸ (hPv.symm ▸ hPl_dom v), 1, j, ?_⟩
      have hϖπL : ((ϖ : A) : L) ^ (q * Mdiv) = ((π : A) : L) := by
        rw [← hϖπ]; push_cast; rfl
      rw [hPv, hPl_val v]
      push_cast
      rw [← pow_mul, hj, show Mdiv * j * q = (q * Mdiv) * j by ring, pow_mul, hϖπL, one_mul]

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.AlgebraicCurve P2mWs20FiniteRep IsLocalRing in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
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
    (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ c : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • c = 0 →
      ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
        Pic0.mk ⟨D, hD⟩ = c ∧
        ∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (v : Aˣ) (j : ℕ),
            (P.evalAt (An e).param) ^ (ℓ ^ k) = ((v : A) : L) * (π : L) ^ j := by
  intro c hc
  classical
  haveI := D.isAlgebraic

  obtain ⟨⟨D₀, hD₀⟩, rfl⟩ := Pic0.mk_surjective c
  have hprin : (((ℓ ^ k : ℕ) : ℤ) • D₀) ∈ Divisor.principal (K := L) (F := F) := by
    have h : Pic0.mk (((ℓ ^ k : ℕ) : ℤ) • (⟨D₀, hD₀⟩ : Divisor.degZero (K := L) (F := F))) = 0 := by
      rw [← hc]; rfl
    have h2 := (QuotientAddGroup.eq_zero_iff _).mp h
    rw [AddSubgroup.mem_addSubgroupOf] at h2
    simpa using h2
  obtain ⟨f₀, hf₀, hdiv₀⟩ := Divisor.mem_principal.mp hprin

  have hrat := ValuationSubring.exists_pow_eq_unit_mul_zpow_of_isAlgebraic_of_isNoetherianRing
    A D.A₀ D.ι D.ι_injective D.K₀ D.range_ι π hπ hπ0

  let zOf : Place L F → L := fun P =>
    if h : ∃ e, P ∈ (An e).dom then P.evalAt (An (Classical.choose h)).param else 1
  have hzOf : ∀ (e : Fin m) (P : Place L F), P ∈ (An e).dom → zOf P = P.evalAt (An e).param := by
    intro e P hP
    have h : ∃ e, P ∈ (An e).dom := ⟨e, hP⟩
    simp only [zOf, dif_pos h]
    rcases hcover P with ⟨i, -, -, hnot⟩ | ⟨e', -, huniq, -⟩
    · exact absurd hP (hnot e)
    · rw [huniq _ (Classical.choose_spec h), huniq e hP]
  have hzOf0 : ∀ P, zOf P ≠ 0 := by
    intro P
    by_cases h : ∃ e, P ∈ (An e).dom
    · obtain ⟨e, hP⟩ := h
      rw [hzOf e P hP]
      exact ((An e).mem_dom P hP).2.2.2.1
    · simp only [zOf, dif_neg h]; exact one_ne_zero
  choose NP aP uP hNP hzpow using fun P => hrat (zOf P) (hzOf0 P)

  let Mₙ : ℕ := ∏ P ∈ D₀.support, NP P
  have hMₙ : 0 < Mₙ := Finset.prod_pos fun P _ => hNP P
  have hNPdvd : ∀ P ∈ D₀.support, NP P ∣ Mₙ := fun P hP => Finset.dvd_prod_of_mem _ hP
  let N : ℕ := ℓ ^ k * Mₙ
  have hℓk : 0 < ℓ ^ k := pow_pos (Fact.out : ℓ.Prime).pos k
  have hN : 0 < N := Nat.mul_pos hℓk hMₙ

  obtain ⟨π₁, hπ₁⟩ := IsAlgClosed.exists_pow_nat_eq (π : L) hN
  obtain ⟨hπ₁A, hπ₁m⟩ := mem_and_mem_maximalIdeal_of_pow_eq A hN.ne' hπ hπ₁
  set ϖ : A := ⟨π₁, hπ₁A⟩ with hϖdef
  have hϖm : ϖ ∈ maximalIdeal A := hπ₁m
  have hϖN : ϖ ^ N = π := Subtype.ext (by simp [hϖdef, hπ₁])
  have hϖL : ((ϖ : A) : L) = π₁ := rfl
  have hπ₁0 : π₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hπ₁
    exact hπ0 (Subtype.ext hπ₁.symm)
  have hϖ0 : ϖ ≠ 0 := fun h => hπ₁0 (by rw [← hϖL, h]; rfl)
  have hw₁ : ∀ e, ∃ u : Aˣ, (An e).modulus = u * ϖ ^ (N * w e) := by
    intro e
    obtain ⟨u, hu⟩ := hw e
    exact ⟨u, by rw [hu, pow_mul, hϖN]⟩

  have hlat : ∀ P ∈ D₀.support, ∀ e, P ∈ (An e).dom →
      ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A), (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d := by
    intro P hPD e hP
    obtain ⟨hrat', hzA, ⟨hzA', hzm⟩, hz0, -⟩ := (An e).mem_dom P hP
    have hpow := hzpow P
    rw [hzOf e P hP] at hpow
    set z := P.evalAt (An e).param with hz

    have ha : 0 < aP P := by
      by_contra hle
      push Not at hle
      have hv1 : A.valuation (z ^ NP P) < 1 := by
        rw [map_pow]
        exact pow_lt_one₀ zero_le' ((A.valuation_lt_one_iff ⟨z, hzA'⟩).mp hzm) (hNP P).ne'
      have hv2 : 1 ≤ A.valuation (((uP P : A) : L) * (π : L) ^ aP P) := by
        rw [map_mul, (A.valuation_eq_one_iff _).mp (uP P).isUnit, one_mul, map_zpow₀]
        have hπv : A.valuation (π : L) < 1 := (A.valuation_lt_one_iff π).mp hπ
        have hπv0 : 0 < A.valuation (π : L) :=
          (Valuation.pos_iff _).mpr (fun h => hπ0 (Subtype.ext h))
        exact one_le_zpow_of_nonpos₀ hπv0 hπv.le hle
      rw [hpow] at hv1
      exact not_lt.mpr hv2 hv1
    obtain ⟨a, ha'⟩ := Int.eq_ofNat_of_zero_le ha.le
    obtain ⟨t, ht⟩ : NP P ∣ N := dvd_trans (hNPdvd P hPD) (dvd_mul_left Mₙ (ℓ ^ k))
    refine ⟨a * t, ?_⟩

    have hzN : z ^ N = (((uP P : A) ^ t : A) : L) * (π₁ ^ (a * t)) ^ N := by
      have e1 : z ^ N = (z ^ NP P) ^ t := by rw [← pow_mul, ← ht]
      rw [e1, hpow, ha', zpow_natCast, ← hπ₁]
      push_cast
      ring
    have hq : (z * (π₁ ^ (a * t))⁻¹) ^ N = (((uP P : A) ^ t : A) : L) := by
      rw [mul_pow, inv_pow, hzN, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hπ₁0)), mul_one]
    obtain ⟨hqA, hqu⟩ := mem_and_isUnit_of_pow_eq A hN.ne' ((uP P) ^ t).isUnit hq
    refine ⟨hqu.unit, hzA', Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, IsUnit.unit_spec, hϖL]
    show z = z * (π₁ ^ (a * t))⁻¹ * π₁ ^ (a * t)
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hπ₁0), mul_one]

  have hlat' : ∀ P ∈ D₀.support, (∃ i, P ∈ (C i).dom) ∨
      ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d := by
    intro P hP
    rcases hcover P with ⟨i, hi, -, -⟩ | ⟨e, he, -, -⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨e, he, hlat P hP e he⟩
  have hϖN' : ϖ ^ (ℓ ^ k * Mₙ) = π := hϖN
  have hw₁' : ∀ e, ∃ u : Aˣ, (An e).modulus = u * ϖ ^ (ℓ ^ k * Mₙ * w e) := hw₁
  have hD₀deg : Divisor.degree D₀ = 0 := hD₀
  obtain ⟨μ, hμC, hμA, hμ0, ⟨φc, hφc⟩, hμdeg⟩ :=
    FiniteRep.muPot A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover
      hdisc hgenus (ℓ ^ k) Mₙ hℓk hMₙ ϖ hϖm hϖ0 hw₁' D₀ hlat' f₀ hf₀ hdiv₀

  have hwpos : ∀ e, w e ≠ 0 := by
    intro e hwe
    obtain ⟨u, hu⟩ := hw e
    rw [hwe, pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).mp (hu ▸ (An e).modulus_mem) u.isUnit
  have hqM : ∀ e, ℓ ^ k * Mₙ ∣ ℓ ^ k * Mₙ * w e := fun e => Dvd.intro _ rfl
  have hW0 : ∀ e, ℓ ^ k * Mₙ * w e ≠ 0 := fun e => Nat.mul_ne_zero (Nat.mul_ne_zero hℓk.ne' hMₙ.ne') (hwpos e)
  obtain ⟨y, χ, hyχ, hysupp⟩ :=
    KummerLevel.comb_exists_sub_eq_laplacian_support_dvd n m src tgt (fun e => ℓ ^ k * Mₙ * w e) (ℓ ^ k) Mₙ hℓk hMₙ
      hqM hW0 (μ D₀) φc hφc
  have hysum : (∑ v, y v) = 0 := by
    have h1 : ∑ v, y v = ∑ v, μ D₀ v - ∑ v, (μ D₀ v - y v) := by
      rw [← Finset.sum_sub_distrib]; simp
    rw [h1, hμdeg, hD₀deg, Finset.sum_congr rfl fun v _ => hyχ v]
    rw [KummerLevelComb.potential_sum_eq_zero]
    simp

  obtain ⟨D, hD, hprinD, hsupp⟩ :=
    FiniteRep.step45 A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover
      hdisc hgenus (ℓ ^ k) Mₙ hℓk hMₙ ϖ hϖm hϖ0 hϖN' D₀ hD₀deg hlat' μ hμC hμA hμ0 y χ hyχ hysupp hysum
  refine ⟨D, hD, ?_, hsupp⟩
  apply (QuotientAddGroup.eq).mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  have : -D + D₀ = D₀ - D := by abel
  simpa [this] using hprinD

end S_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel (solution)
