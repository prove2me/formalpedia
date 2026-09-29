-- Prove2me | solution 1 for AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3c279e5c-7192-5072-a9e8-5f3eb4ded211

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_card_sub_one_mul_card_effectiveDivisors_eq
import Theorems.Thm_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve Polynomial

namespace P2mClassNumberFormula

def geom (r : ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => r ^ n

theorem one_sub_mul_geom (r : ℤ) :
    (1 - PowerSeries.C r * PowerSeries.X) * geom r = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [geom]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp [geom, pow_succ, mul_comm]

theorem mk_eq_head_add_tail (a : ℕ → ℤ) (N : ℕ) :
    PowerSeries.mk a =
      ((∑ n ∈ Finset.range N, C (a n) * X ^ n : ℤ[X]) : PowerSeries ℤ) +
        PowerSeries.X ^ N * PowerSeries.mk (fun m => a (N + m)) := by
  ext n
  rw [PowerSeries.coeff_mk, map_add, Polynomial.coeff_coe, PowerSeries.coeff_X_pow_mul',
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n < N
  · rw [Finset.sum_eq_single n (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd
      (Finset.mem_range.mpr hn) h), if_pos rfl, if_neg (not_le.mpr hn), add_zero]
  · push Not at hn
    rw [Finset.sum_eq_zero (fun b hb => if_neg (by
        have := Finset.mem_range.mp hb; omega)), zero_add, if_pos hn, PowerSeries.coeff_mk,
      Nat.add_sub_cancel' hn]

theorem eval_one_eq (q h : ℤ) (hq1 : q - 1 ≠ 0) (a : ℕ → ℤ) (N e : ℕ) (L : ℤ[X])
    (hL : (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) * PowerSeries.mk a =
      (L : PowerSeries ℤ))
    (ha : ∀ m : ℕ, (q - 1) * a (N + m) = h * (q ^ (e + m) - 1)) :
    L.eval 1 = h := by

  have hT : PowerSeries.C (q - 1) * PowerSeries.mk (fun m => a (N + m)) =
      PowerSeries.C h * (PowerSeries.C (q ^ e) * geom q - geom 1) := by
    ext m
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, map_sub,
      PowerSeries.coeff_C_mul]
    simp only [geom, PowerSeries.coeff_mk, one_pow, ha m, pow_add]
  have hgq := one_sub_mul_geom q
  have hg1 : (1 - PowerSeries.X) * geom 1 = 1 := by simpa using one_sub_mul_geom 1
  have hZ := mk_eq_head_add_tail a N
  set A : ℤ[X] := ∑ n ∈ Finset.range N, C (a n) * X ^ n with hA

  set R : ℤ[X] := C (q - 1) * ((1 - X) * (1 - C q * X)) * A +
    C h * X ^ N * (C (q ^ e) * (1 - X) - (1 - C q * X)) with hR
  have hRcoe : (R : PowerSeries ℤ) =
      PowerSeries.C (q - 1) * ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) *
          (A : PowerSeries ℤ) +
        PowerSeries.C h * PowerSeries.X ^ N *
          (PowerSeries.C (q ^ e) * (1 - PowerSeries.X) -
            (1 - PowerSeries.C q * PowerSeries.X)) := by
    simp only [hR, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  have hPS : ((C (q - 1) * L : ℤ[X]) : PowerSeries ℤ) = (R : PowerSeries ℤ) := by
    rw [Polynomial.coe_mul, Polynomial.coe_C, hRcoe]
    linear_combination (PowerSeries.C (q - 1)) * hL.symm +
      (PowerSeries.C (q - 1) * ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) *
        hZ +
      ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) * PowerSeries.X ^ N) * hT +
      (PowerSeries.C h * PowerSeries.X ^ N * PowerSeries.C (q ^ e) * (1 - PowerSeries.X)) * hgq -
      (PowerSeries.C h * PowerSeries.X ^ N * (1 - PowerSeries.C q * PowerSeries.X)) * hg1
  have hpoly : C (q - 1) * L = R := Polynomial.coe_inj.mp hPS
  have hev := congrArg (Polynomial.eval 1) hpoly
  simp only [hR, eval_mul, eval_C, eval_add, eval_sub, eval_one, eval_X, eval_pow, one_pow,
    mul_one, sub_self, mul_zero, zero_sub] at hev

  have : (q - 1) * (L.eval 1 - h) = 0 := by linear_combination hev
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hq1
  · linear_combination h0

end P2mClassNumberFormula

end

open AlgebraicCurve in

theorem solution
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) (L : Polynomial ℤ)
    (hL : (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n : ℕ =>
            (Nat.card {D : AlgebraicCurve.Divisor k F //
                0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)} : ℤ)) =
        (L : PowerSeries ℤ)) :
    L.eval 1 = Nat.card (AlgebraicCurve.Pic0 k F) := by
  classical

  set q : ℕ := Nat.card k with hq
  set h : ℕ := Nat.card (Pic0 k F) with hh
  set g : ℕ := genusFF k F with hg
  set A : ℕ → ℕ := fun n => Nat.card {D : Divisor k F // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)}
    with hAdef

  have hq2 : 1 < q := by
    haveI := Fintype.ofFinite k
    rw [hq, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card

  obtain ⟨D₁, hD₁⟩ := AlgebraicCurve.exists_divisor_degree_eq_one_of_finite k F hC
  have hdeg : ∀ n : ℕ, ∃ D : Divisor k F, Divisor.degree D = (n : ℤ) := fun n =>
    ⟨n • D₁, by rw [map_nsmul, hD₁]; simp⟩

  obtain ⟨N, hgN, hAN⟩ := AlgebraicCurve.card_sub_one_mul_card_effectiveDivisors_eq k F hC

  have ha : ∀ m : ℕ, ((q : ℤ) - 1) * ((A (N + m) : ℕ) : ℤ) =
      (h : ℤ) * ((q : ℤ) ^ (N + 1 - g + m) - 1) := by
    intro m
    have h1 := hAN (N + m) (Nat.le_add_right N m) (hdeg (N + m))
    have hgN' : g ≤ N := hgN
    have h2 : N + m + 1 - genusFF k F = N + 1 - g + m := by rw [← hg]; omega
    rw [h2] at h1
    have h3 := congrArg (Nat.cast : ℕ → ℤ) h1
    push_cast [Nat.cast_sub hq2.le, Nat.cast_sub (Nat.one_le_pow _ q (by omega))] at h3
    simpa [hAdef] using h3
  have hq1 : (q : ℤ) - 1 ≠ 0 := by
    have : (1 : ℤ) < q := by exact_mod_cast hq2
    omega
  have hmain := P2mClassNumberFormula.eval_one_eq (q : ℤ) (h : ℤ) hq1
    (fun n => ((A n : ℕ) : ℤ)) N (N + 1 - g) L (by simpa [hAdef] using hL) ha
  rw [hmain]

end S_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0
end P2MW
export P2MW.S_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0 (solution)
