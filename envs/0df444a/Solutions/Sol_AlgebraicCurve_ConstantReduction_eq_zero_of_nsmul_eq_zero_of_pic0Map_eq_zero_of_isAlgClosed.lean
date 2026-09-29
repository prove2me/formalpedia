-- Prove2me | solution 1 for AlgebraicCurve.ConstantReduction.eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0aaa4972-fdf8-59a3-8abe-7a9670043e6d

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_transcendental_residue
import Theorems.Thm_AlgebraicCurve_ConstantReduction_finiteDimensional_and_finrank_adjoin_residue_le
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_transcendental_residue_finrank_adjoin_eq_of_isGood
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ConstantReduction_eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ValuationSubring.coe_toResidueValuationSubring ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

p2m_open "AlgebraicCurve~genus"

set_option autoImplicit false

namespace TorsionInjectsUnderGoodReduction

open IsLocalRing

section Classes

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mk_nsmul (n : ℕ) (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk (n • D) = n • Pic0.mk D := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, Pic0.mk_add, ih]

private theorem mk_eq_zero_iff (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ (D : Divisor K F) ∈ Divisor.principal (K := K) (F := F) :=
  (QuotientAddGroup.eq_zero_iff D).trans AddSubgroup.mem_addSubgroupOf

private theorem nsmul_apply (n : ℕ) (D : Divisor K F) (v : Place K F) : (n • D) v = (n : ℤ) * D v := by
  rw [Finsupp.smul_apply, nsmul_eq_mul]

private theorem ord_pow (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

private theorem mem_torsion_iff (n : ℕ) (x : Pic0 K F) : x ∈ Pic0.torsion K F n ↔ n • x = 0 := by
  rw [Pic0.mem_torsion, natCast_zsmul]

end Classes

section Injective

variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
  (F : Type*) [Field F] [Algebra L F]
  (hF : ∃ x : F, Transcendental L x ∧ FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
  (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
  (R : ConstantReduction A F Fbar) (hR : R.IsGood)

include hF hR

private theorem eq_zero_of_prime {q : ℕ} [hq : Fact q.Prime] (hqk : (q : ResidueField A) ≠ 0)
    (xr : R.integers) (hxr : Transcendental (ResidueField A) (R.residue xr))
    [FiniteDimensional (IntermediateField.adjoin (ResidueField A) ({R.residue xr} : Set Fbar)) Fbar]
    (z : Pic0 L F) (hz : q • z = 0) (h0 : R.pic0Map z = 0) : z = 0 := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hqpos : 0 < q := hq.out.pos
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z

  have hqD : ((q • D : Divisor.degZero (K := L) (F := F)) : Divisor L F) ∈ Divisor.principal (K := L) (F := F) := by
    rw [← mk_eq_zero_iff, mk_nsmul]; exact hz
  rw [AddSubmonoidClass.coe_nsmul] at hqD
  obtain ⟨u, hu0, huD⟩ := hqD

  have hD0 : Finsupp.mapDomain R.placeMap (D : Divisor L F) ∈
      Divisor.principal (K := ResidueField A) (F := Fbar) := by
    have h := h0
    rw [R.pic0Map_mk, mk_eq_zero_iff, R.coe_degZeroMap] at h
    exact h
  obtain ⟨wbar, hwbar0, hwD⟩ := hD0

  obtain ⟨c, hcu, hres⟩ := R.exists_smul_mem u hu0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • u, hcu⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  set u₁ : R.integers := ⟨c • u, hcu⟩ with hu₁
  have hu₁D : ∀ P : Place L F, (q : ℤ) * (D : Divisor L F) P = P.ord (u₁ : F) := fun P => by
    rw [← nsmul_apply, huD P]
    exact (ConstantReduction.ord_smul P hc0 u).symm
  have hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (u₁ : F) := fun P => ⟨(D : Divisor L F) P, (hu₁D P).symm⟩

  have hred : ∀ Q : Place (ResidueField A) Fbar, Q.ord (R.residue u₁) = (q : ℤ) * Q.ord wbar := fun Q => by
    have h := R.mapDomain_placeMap u₁ hres (q • (D : Divisor L F)) (fun P => by rw [nsmul_apply, hu₁D P]) Q
    rw [Finsupp.mapDomain_smul, nsmul_apply, hwD Q] at h
    exact h.symm
  have hres0 : R.residue u₁ ≠ 0 := hres
  set r : Fbar := R.residue u₁ * (wbar ^ q)⁻¹ with hr
  have hr0 : r ≠ 0 := mul_ne_zero hres0 (inv_ne_zero (pow_ne_zero _ hwbar0))
  have hrord : ∀ Q : Place (ResidueField A) Fbar, Q.ord r = 0 := fun Q => by
    rw [hr, Q.ord_mul hres0 (inv_ne_zero (pow_ne_zero _ hwbar0)), Q.ord_inv, ord_pow, hred Q]
    ring
  obtain ⟨a, ha⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (R.residue xr) hxr hrord
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hqpos
  set w : Fbar := algebraMap (ResidueField A) Fbar b * wbar with hw
  have hwq : w ^ q = R.residue u₁ := by
    rw [hw, mul_pow, ← map_pow, hb, ha, hr, inv_mul_cancel_right₀ (pow_ne_zero _ hwbar0)]
  have hw0 : w ≠ 0 := by
    intro h
    apply hres0
    rw [← hwq, h, zero_pow hq.out.ne_zero]

  obtain ⟨x, hx, hxpos, hxdeg⟩ := ConstantReduction.exists_transcendental_residue_finrank_adjoin_eq_of_isGood A F hF Fbar R hR
  obtain ⟨h, hh⟩ : ∃ h : F, h ^ q = (u₁ : F) :=
    RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed A hF R.toRegularProlongation
      ((R.isGood_iff).mp hR) ⟨x, hx, hxpos, hxdeg⟩ hqk u₁ hdvd w hw0 hwq

  have hh0 : h ≠ 0 := by
    rintro rfl
    apply hres0
    have : (u₁ : F) = 0 := by rw [← hh, zero_pow hq.out.ne_zero]
    have h' : u₁ = 0 := Subtype.ext this
    rw [h', map_zero]
  rw [mk_eq_zero_iff]
  refine ⟨h, hh0, fun P => ?_⟩
  have h1 := hu₁D P
  rw [← hh, ord_pow] at h1
  exact mul_left_cancel₀ hqZ h1

private theorem eq_zero_of_nsmul_eq_zero
    (xr : R.integers) (hxr : Transcendental (ResidueField A) (R.residue xr))
    [FiniteDimensional (IntermediateField.adjoin (ResidueField A) ({R.residue xr} : Set Fbar)) Fbar] :
    ∀ (n : ℕ), (n : ResidueField A) ≠ 0 → ∀ z : Pic0 L F, n • z = 0 → R.pic0Map z = 0 → z = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn z hz h0
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · interval_cases n
      · exact absurd Nat.cast_zero hn
      · simpa using hz
    · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨n', rfl⟩ := hqn
      haveI : Fact q.Prime := ⟨hq⟩
      have hcast : (q : ResidueField A) * n' ≠ 0 := by exact_mod_cast hn
      have hqk : (q : ResidueField A) ≠ 0 := left_ne_zero_of_mul hcast
      have hn'k : (n' : ResidueField A) ≠ 0 := right_ne_zero_of_mul hcast
      have hn'lt : n' < q * n' := by
        have : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; exact hn'k Nat.cast_zero)
        nlinarith [hq.two_le]

      have hz' : q • (n' • z) = 0 := by rwa [← mul_smul]
      have h0' : R.pic0Map (n' • z) = 0 := by rw [map_nsmul, h0, smul_zero]
      have hz'' : n' • z = 0 := eq_zero_of_prime A F hF Fbar R hR hqk xr hxr (n' • z) hz' h0'
      exact ih n' hn'lt hn'k z hz'' h0

end Injective

end TorsionInjectsUnderGoodReduction

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧ FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (m : ℕ) (hm : (m : IsLocalRing.ResidueField A) ≠ 0)
    (z : Pic0 L F) (hmz : m • z = 0) (hz : R.pic0Map z = 0) :
    z = 0 := by

  rcases isEmpty_or_nonempty (Place L F) with hE | ⟨⟨P⟩⟩
  · obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
    have hD0 : (D : Divisor L F) = 0 := Subsingleton.elim _ _
    rw [show D = 0 from Subtype.ext hD0]
    rfl
  haveI : Nonempty (Place L F) := ⟨P⟩
  have hF' := hF
  obtain ⟨x₀, -, hfd₀⟩ := hF'
  haveI := hfd₀
  obtain ⟨xr, hxr, hxrL⟩ := ConstantReduction.exists_transcendental_residue R
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(xr : F)} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental x₀ hxrL
  obtain ⟨hfin, -⟩ := ConstantReduction.finiteDimensional_and_finrank_adjoin_residue_le R xr hxr
  haveI := hfin
  exact TorsionInjectsUnderGoodReduction.eq_zero_of_nsmul_eq_zero A F hF Fbar R hR xr hxr m hm z hmz hz

end S_AlgebraicCurve_ConstantReduction_eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_ConstantReduction_eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed (solution)
