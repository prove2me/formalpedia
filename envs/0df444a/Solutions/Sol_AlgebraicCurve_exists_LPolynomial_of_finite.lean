-- Prove2me | solution 1 for AlgebraicCurve.exists_LPolynomial_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4c959670-3e3d-5a51-95cd-d74500e42947

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite
import Theorems.Thm_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite
import Theorems.Thm_AlgebraicCurve_Pic0_finite_of_finite
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Theorems.Thm_AlgebraicCurve_one_le_deg
import Theorems.Thm_AlgebraicCurve_Divisor_degree_nonneg_of_nonneg
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.ord_inv Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.IsPrincipal Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective Pic0.mk_add HasPrincipalDivisors.exists_divisor LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase H1 genusFF exists_weilCanonical_riemannRoch card_effective_sub_isPrincipal_of_finite exists_divisor_degree_eq_one_of_finite Pic0.finite_of_finite ell_eq_zero_of_degree_neg one_le_deg Divisor.degree_nonneg_of_nonneg finiteDimensional_lSpace mul_mem_lSpace_add"
namespace LPolynomialSol
p2m_open "AlgebraicCurve"

section Algebra

open Polynomial

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

theorem reflect_comp_eq (q : ℤ) (g' : ℕ) (P : ℤ[X]) (hP : P.natDegree ≤ 2 * g')
    (H3 : ∀ n, n ≤ 2 * g' → q ^ g' * P.coeff n = q ^ n * P.coeff (2 * g' - n)) :
    (reflect (2 * g') P).comp (C q * X) = C (q ^ g') * P := by
  ext n
  rw [comp_C_mul_X_coeff, coeff_reflect, coeff_C_mul]
  by_cases hn : n ≤ 2 * g'
  · rw [revAt_le hn, mul_comm, ← H3 n hn]
  · push Not at hn
    have h1 : (revAt (2 * g')) n = n := by simp [revAt, hn]
    rw [h1, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hn), zero_mul, mul_zero]

theorem lpoly_of_counts (q h : ℤ) (hq1 : q - 1 ≠ 0) (g : ℕ) (A T : ℕ → ℤ)
    (H1 : ∀ n, (q - 1) * A n + h = T n)
    (H2 : ∀ n, 2 * g ≤ n + 1 → T n = h * q ^ (n + 1 - g))
    (H3 : ∀ n, n + 2 ≤ 2 * g → q ^ (g - 1) * T n = q ^ n * T (2 * g - 2 - n))
    (H4 : A 0 = 1) :
    ∃ L : Polynomial ℤ, L.natDegree ≤ 2 * g ∧ L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * g, L.coeff (2 * g - i) * q ^ i = q ^ g * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) * PowerSeries.mk A =
        (L : PowerSeries ℤ) := by

  set W : PowerSeries ℤ :=
    (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) * PowerSeries.mk A with hW
  have hZ : PowerSeries.C (q - 1) * PowerSeries.mk A =
      PowerSeries.mk T - PowerSeries.C h * geom 1 := by
    ext n
    rw [PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_C_mul]
    simp [geom, ← H1 n]
  have hg1 : (1 - PowerSeries.X) * geom 1 = 1 := by simpa using one_sub_mul_geom 1
  have hgq := one_sub_mul_geom q
  have hW0 : PowerSeries.coeff 0 W = 1 := by
    simp [hW, PowerSeries.coeff_zero_eq_constantCoeff_apply, H4]
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  ·
    subst hg0
    have hT : PowerSeries.mk T = PowerSeries.C h * PowerSeries.C q * geom q := by
      ext n
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
      simp [geom, H2 n (by omega), pow_succ, mul_comm, mul_left_comm]
    have hW1 : PowerSeries.C (q - 1) * W = PowerSeries.C (q - 1) * PowerSeries.C h := by
      rw [hW]
      linear_combination (norm := skip)
        ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) * hZ +
        ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) * hT +
        (PowerSeries.C h * PowerSeries.C q * (1 - PowerSeries.X)) * hgq -
        (PowerSeries.C h * (1 - PowerSeries.C q * PowerSeries.X)) * hg1
      simp only [map_sub, map_one]
      ring
    have hW2 : W = PowerSeries.C h := by
      ext n
      have h1 := congrArg (PowerSeries.coeff n) hW1
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at h1
      exact mul_left_cancel₀ hq1 h1
    have hh : h = 1 := by
      have := hW0
      rwa [hW2, PowerSeries.coeff_zero_C] at this
    refine ⟨1, by simp, by simp, fun i hi => ?_, ?_⟩
    · obtain rfl : i = 0 := by omega
      simp
    · rw [hW2, hh]; simp
  ·
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩

    set P : ℤ[X] := PowerSeries.trunc (2 * g' + 1) (PowerSeries.mk T) with hPdef
    have hPcoeff : ∀ n, P.coeff n = if n < 2 * g' + 1 then T n else 0 := fun n => by
      rw [hPdef, PowerSeries.coeff_trunc, PowerSeries.coeff_mk]
    have hPdeg : P.natDegree ≤ 2 * g' :=
      Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt _ _)
    set a : ℤ := h * q ^ (g' + 1) with ha
    have hT : PowerSeries.mk T =
        (P : PowerSeries ℤ) + PowerSeries.X ^ (2 * g' + 1) * (PowerSeries.C a * geom q) := by
      ext n
      rw [map_add, Polynomial.coeff_coe, hPcoeff, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      by_cases hn : n < 2 * g' + 1
      · rw [if_pos hn, if_neg (by omega), add_zero]
      · rw [if_neg hn, if_pos (by omega), zero_add, H2 n (by omega), ha, geom,
          PowerSeries.coeff_mk, mul_assoc, ← pow_add]
        congr 2
        omega

    set Up : ℤ[X] := C 1 * X ^ 0 + C (-(q + 1)) * X ^ 1 + C q * X ^ 2 with hUp
    set R : ℤ[X] := C a * X ^ (2 * g' + 1) + C (-a) * X ^ (2 * g' + 2) + C (-h) * X ^ 0 +
      C (h * q) * X ^ 1 with hR
    set M : ℤ[X] := Up * P + R with hM
    have hUpc :
        (Up : PowerSeries ℤ) = (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) := by
      simp only [hUp, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_X]
      simp only [map_neg, map_add, map_one]
      ring
    have hRc : (R : PowerSeries ℤ) = PowerSeries.C a * PowerSeries.X ^ (2 * g' + 1) -
        PowerSeries.C a * PowerSeries.X ^ (2 * g' + 2) - PowerSeries.C h +
        PowerSeries.C h * PowerSeries.C q * PowerSeries.X := by
      simp only [hR, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_X]
      simp only [map_neg, map_mul]
      ring
    have hMW : (M : PowerSeries ℤ) = PowerSeries.C (q - 1) * W := by
      rw [hM, Polynomial.coe_add, Polynomial.coe_mul, hUpc, hRc, hW]
      linear_combination (norm := skip)
        (-((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) * hZ +
        (-((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) * hT +
        (-(PowerSeries.C a * (1 - PowerSeries.X) * PowerSeries.X ^ (2 * g' + 1))) * hgq +
        (PowerSeries.C h * (1 - PowerSeries.C q * PowerSeries.X)) * hg1
      simp only [map_sub, map_one]
      ring

    have hUpdeg : Up.natDegree ≤ 2 := by
      rw [hUp]
      refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact natDegree_C_mul_X_pow_le _ _
    have hRdeg : R.natDegree ≤ 2 * g' + 2 := by
      rw [hR]
      refine natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact natDegree_C_mul_X_pow_le _ _
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    have hMdeg : M.natDegree ≤ 2 * g' + 2 := by
      rw [hM]
      refine natDegree_add_le_of_degree_le (natDegree_mul_le.trans ?_) hRdeg
      omega
    have hWcoeff : ∀ n, 2 * g' + 2 < n → PowerSeries.coeff n W = 0 := by
      intro n hn
      have h1 : PowerSeries.coeff n (M : PowerSeries ℤ) = 0 := by
        rw [Polynomial.coeff_coe]
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hMdeg hn)
      rw [hMW, PowerSeries.coeff_C_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hq1
    set L : ℤ[X] := PowerSeries.trunc (2 * g' + 2 + 1) W with hL
    have hLW : (L : PowerSeries ℤ) = W := by
      ext n
      rw [Polynomial.coeff_coe, hL, PowerSeries.coeff_trunc]
      split_ifs with hn
      · rfl
      · exact (hWcoeff n (by omega)).symm
    have hML : M = C (q - 1) * L := by
      rw [← Polynomial.coe_inj, hMW, Polynomial.coe_mul, Polynomial.coe_C, hLW]
    have hMLc : ∀ n, M.coeff n = (q - 1) * L.coeff n := fun n => by
      rw [hML, coeff_C_mul]

    have hP3 : (reflect (2 * g') P).comp (C q * X) = C (q ^ g') * P := by
      refine reflect_comp_eq q g' P hPdeg fun n hn => ?_
      rw [hPcoeff, hPcoeff, if_pos (by omega), if_pos (by omega)]
      have := H3 n (by omega)
      rwa [show g' + 1 - 1 = g' by omega, show 2 * (g' + 1) - 2 - n = 2 * g' - n by omega]
        at this
    have hρ : (reflect (2 * g' + 2) M).comp (C q * X) = C (q ^ (g' + 1)) * M := by
      have hrefl : reflect (2 * g' + 2) M =
          reflect 2 Up * reflect (2 * g') P + reflect (2 * g' + 2) R := by
        rw [hM, reflect_add, show 2 * g' + 2 = 2 + 2 * g' by ring, reflect_mul Up P hUpdeg hPdeg]
      have hUr : reflect 2 Up = C 1 * X ^ 2 + C (-(q + 1)) * X ^ 1 + C q * X ^ 0 := by
        rw [hUp, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
          reflect_C_mul_X_pow, revAt_le (by omega), revAt_le (by omega), revAt_le (by omega)]
      have hRr : reflect (2 * g' + 2) R = C a * X ^ 1 + C (-a) * X ^ 0 +
          C (-h) * X ^ (2 * g' + 2) + C (h * q) * X ^ (2 * g' + 1) := by
        rw [hR, reflect_add, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
          reflect_C_mul_X_pow, reflect_C_mul_X_pow, revAt_le (by omega), revAt_le (by omega),
          revAt_le (by omega), revAt_le (by omega)]
        congr 3 <;> [congr 2; skip] <;> [omega; congr 2] ; omega
      rw [hrefl, add_comp, mul_comp, hP3, hUr, hRr]
      simp only [add_comp, mul_comp, C_comp, pow_comp, X_comp]
      rw [hM, hUp, hR, ha]
      simp only [map_neg, map_add, map_one, map_mul, map_pow]
      ring
    have hFEM : ∀ i ≤ 2 * g' + 2,
        M.coeff (2 * g' + 2 - i) * q ^ i = q ^ (g' + 1) * M.coeff i := by
      intro i hi
      have := congrArg (fun f : ℤ[X] => f.coeff i) hρ
      simp only [comp_C_mul_X_coeff, coeff_reflect, coeff_C_mul, revAt_le hi] at this
      exact this
    refine ⟨L, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (g' + 1) = 2 * g' + 2 by ring]
      exact Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt _ _)
    · rw [hL, PowerSeries.coeff_trunc, if_pos (by omega), hW0]
    · intro i hi
      have h1 := hFEM i (by omega)
      rw [hMLc, hMLc, show 2 * g' + 2 - i = 2 * (g' + 1) - i by omega] at h1
      refine mul_left_cancel₀ hq1 ?_
      linear_combination h1
    · exact hLW.symm

end Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem self_mem_lSpace_neg {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z ∈ LSpace (-P) := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [hP v]

theorem inv_mem_lSpace {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z⁻¹ ∈ LSpace P := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [Place.ord_inv, hP v]

theorem ell_add_eq_of_ord_eq {z : F} (hz : z ≠ 0) {P : Divisor K F}
    (hP : ∀ v, P v = v.ord z) (A : Divisor K F) : ell (A + P) = ell A := by
  have h1 : ∀ f : F, f ∈ LSpace (A + P) → f * z ∈ LSpace A := fun f hf => by
    have := mul_mem_lSpace_add hf (self_mem_lSpace_neg hP)
    rwa [add_neg_cancel_right] at this
  have h2 : ∀ g : F, g ∈ LSpace A → g * z⁻¹ ∈ LSpace (A + P) := fun g hg =>
    mul_mem_lSpace_add hg (inv_mem_lSpace hP)
  let e : LSpace (A + P) ≃ₗ[K] LSpace A :=
    { toFun := fun f => ⟨f.1 * z, h1 f.1 f.2⟩
      map_add' := fun f g => by
        ext
        simp [add_mul]
      map_smul' := fun c f => by
        ext
        simp
      invFun := fun g => ⟨g.1 * z⁻¹, h2 g.1 g.2⟩
      left_inv := fun f => by
        ext
        simp [mul_inv_cancel_right₀ hz]
      right_inv := fun g => by
        ext
        simp [inv_mul_cancel_right₀ hz] }
  exact e.finrank_eq

theorem ell_eq_of_isPrincipal_sub {D E : Divisor K F} (h : Divisor.IsPrincipal (D - E)) :
    ell D = ell E := by
  obtain ⟨z, hz, hP⟩ := h
  have := ell_add_eq_of_ord_eq hz hP E
  rwa [add_sub_cancel] at this

theorem degree_eq_zero_of_isPrincipal [HasPrincipalDivisors K F] {P : Divisor K F}
    (h : Divisor.IsPrincipal P) : Divisor.degree P = 0 := by
  obtain ⟨z, hz, hP⟩ := h
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz
  have : D = P := Finsupp.ext fun v => by rw [hD v, hP v]
  rwa [this] at hdeg

theorem degree_pos_of_nonneg_of_ne_zero [IsCurveOver K F] {E : Divisor K F} (hE : 0 ≤ E)
    (hE0 : E ≠ 0) : 0 < Divisor.degree E := by
  classical
  have hEnn : ∀ w, 0 ≤ E w := fun w => by simpa using (Finsupp.le_def.mp hE) w
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE0 (Finsupp.ext h)
  have hEv : 1 ≤ E v := by
    have := hEnn v
    omega
  have hsplit : E = Finsupp.single v (E v) + Finsupp.erase v E :=
    (Finsupp.single_add_erase v E).symm
  have herase : ∀ w, 0 ≤ Finsupp.erase v E w := fun w => by
    rw [Finsupp.erase_apply]
    split_ifs
    · exact le_rfl
    · exact hEnn w
  have h1 : 0 ≤ Divisor.degree (Finsupp.erase v E) := Divisor.degree_nonneg_of_nonneg herase
  have h2 : (1 : ℤ) ≤ v.deg := by exact_mod_cast one_le_deg v
  rw [hsplit, map_add, Divisor.degree_single]
  nlinarith

theorem mk_eq_mk_iff (x y : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk x = Pic0.mk y ↔ Divisor.IsPrincipal ((x : Divisor K F) - (y : Divisor K F)) := by
  show (QuotientAddGroup.mk x : Pic0 K F) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  show -(x : Divisor K F) + y ∈ Divisor.principal ↔ _
  rw [neg_add_eq_sub, ← neg_sub, neg_mem_iff]
  rfl

section Count

variable [IsCurveOver K F]

abbrev Eff (n : ℕ) : Type _ :=
  {D : Divisor K F // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)}

abbrev LinSys (C : Divisor K F) : Type _ :=
  {D : Divisor K F // 0 ≤ D ∧ Divisor.IsPrincipal (D - C)}

theorem card_eff_zero : Nat.card (Eff (K := K) (F := F) 0) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun D E => Subtype.ext ?_⟩, ⟨⟨0, le_rfl, by simp⟩⟩⟩
  have hD : (D : Divisor K F) = 0 := by
    by_contra h
    have := degree_pos_of_nonneg_of_ne_zero D.2.1 h
    rw [D.2.2] at this
    simp at this
  have hE : (E : Divisor K F) = 0 := by
    by_contra h
    have := degree_pos_of_nonneg_of_ne_zero E.2.1 h
    rw [E.2.2] at this
    simp at this
  rw [hD, hE]

theorem finite_linSys [Finite K] (hC : ConstantsAreBase K F) (C : Divisor K F) :
    Finite (LinSys C) := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  have h := card_effective_sub_isPrincipal_of_finite K F hC C
  rw [@Nat.card_eq_zero_of_infinite _ hinf, mul_zero, zero_add] at h
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hell : ell C = 0 := by
    rcases Nat.pow_eq_one.mp h.symm with h1 | h1
    · omega
    · exact h1
  obtain ⟨⟨D, hD0, f, hf, hfD⟩⟩ := (inferInstance : Nonempty (LinSys C))
  have hmem : f ∈ LSpace C := by
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    have h1 := (Finsupp.le_def.mp hD0) v
    have h2 := hfD v
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 h2
    linarith
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := by
    have hC' : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
    rw [hC']
    infer_instance
  haveI : FiniteDimensional K (LSpace C) := finiteDimensional_lSpace C
  have hpos : 0 < ell C :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨f, hmem⟩, fun h0 => hf (congrArg Subtype.val h0)⟩
  omega

theorem exists_W [PerfectField K] [Algebra.EssFiniteType K F] (hC : ConstantsAreBase K F) :
    ∃ W : Divisor K F, Divisor.degree W = 2 * (genusFF K F : ℤ) - 2 ∧
      ∀ D : Divisor K F, (ell D : ℤ) - (ell (W - D) : ℤ) =
        Divisor.degree D + 1 - (genusFF K F : ℤ) := by
  obtain ⟨W, hW⟩ := exists_weilCanonical_riemannRoch K F hC
  refine ⟨W, ?_, hW⟩
  have h0 := hW 0
  have hW' := hW W
  rw [sub_zero, map_zero, ell_zero_eq_one_of_constantsAreBase hC] at h0
  rw [sub_self, ell_zero_eq_one_of_constantsAreBase hC] at hW'
  push_cast at h0 hW'
  linarith

variable (D₁ : {D : Divisor K F // Divisor.degree D = 1})

def toDegZero (D : Divisor K F) : Divisor.degZero (K := K) (F := F) :=
  ⟨D - Divisor.degree D • (D₁ : Divisor K F), by
    rw [Divisor.mem_degZero, map_sub, map_zsmul, D₁.2, smul_eq_mul, mul_one, sub_self]⟩

omit [IsCurveOver K F] in
@[scoped simp] theorem coe_toDegZero (D : Divisor K F) :
    (toDegZero D₁ D : Divisor K F) = D - Divisor.degree D • (D₁ : Divisor K F) := rfl

def cls (D : Divisor K F) : Pic0 K F := Pic0.mk (toDegZero D₁ D)

def rep (c : Pic0 K F) (n : ℤ) : Divisor K F :=
  ((Pic0.mk_surjective c).choose : Divisor K F) + n • (D₁ : Divisor K F)

omit [IsCurveOver K F] in
theorem degree_rep (c : Pic0 K F) (n : ℤ) : Divisor.degree (rep D₁ c n) = n := by
  have h : Divisor.degree ((Pic0.mk_surjective c).choose : Divisor K F) = 0 :=
    (Pic0.mk_surjective c).choose.2
  rw [rep, map_add, map_zsmul, D₁.2, h, smul_eq_mul, mul_one, zero_add]

omit [IsCurveOver K F] in

theorem cls_eq_iff {D : Divisor K F} {n : ℤ} (hD : Divisor.degree D = n) (c : Pic0 K F) :
    cls D₁ D = c ↔ Divisor.IsPrincipal (D - rep D₁ c n) := by
  conv_lhs => rw [← (Pic0.mk_surjective c).choose_spec]
  rw [cls, mk_eq_mk_iff, coe_toDegZero, hD, rep]
  congr! 1
  abel

def effEquiv (n : ℕ) :
    Eff (K := K) (F := F) n ≃ Σ c : Pic0 K F, LinSys (rep D₁ c n) :=
  (Equiv.sigmaFiberEquiv fun D : Eff (K := K) (F := F) n => cls D₁ (D : Divisor K F)).symm.trans
    (Equiv.sigmaCongrRight fun c =>
      { toFun := fun D => ⟨(D.1 : Divisor K F), D.1.2.1, (cls_eq_iff D₁ D.1.2.2 c).mp D.2⟩
        invFun := fun D =>
          have hdeg : Divisor.degree (D.1 : Divisor K F) = n := by
            have := degree_eq_zero_of_isPrincipal D.2.2
            rw [map_sub, degree_rep] at this
            linarith
          ⟨⟨D.1, D.2.1, hdeg⟩, (cls_eq_iff D₁ hdeg c).mpr D.2.2⟩
        left_inv := fun D => Subtype.ext (Subtype.ext rfl)
        right_inv := fun D => Subtype.ext rfl })

theorem card_eff_eq_sum [Finite K] [Fintype (Pic0 K F)] (hC : ConstantsAreBase K F) (n : ℕ) :
    Nat.card (Eff (K := K) (F := F) n) = ∑ c : Pic0 K F, Nat.card (LinSys (rep D₁ c n)) := by
  haveI : ∀ c : Pic0 K F, Finite (LinSys (rep D₁ c (n : ℤ))) := fun c => finite_linSys hC _
  rw [Nat.card_congr (effEquiv D₁ n), Nat.card_sigma]

theorem H1 [Finite K] [Fintype (Pic0 K F)] (hC : ConstantsAreBase K F) (n : ℕ) :
    ((Nat.card K : ℤ) - 1) * Nat.card (Eff (K := K) (F := F) n) + Nat.card (Pic0 K F) =
      ∑ c : Pic0 K F, (Nat.card K : ℤ) ^ ell (rep D₁ c n) := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hc : ∀ c : Pic0 K F,
      ((Nat.card K : ℤ) - 1) * Nat.card (LinSys (rep D₁ c (n : ℤ))) + 1 =
        (Nat.card K : ℤ) ^ ell (rep D₁ c n) := fun c => by
    have := card_effective_sub_isPrincipal_of_finite K F hC (rep D₁ c n)
    have h2 : ((Nat.card K - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) - 1 := by push_cast [hq]; ring
    rw [← h2]
    exact_mod_cast this
  rw [card_eff_eq_sum D₁ hC n, Nat.cast_sum, Finset.mul_sum,
    Nat.card_eq_fintype_card (α := Pic0 K F), ← Finset.sum_congr rfl fun c _ => hc c,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem H2 [PerfectField K] [Algebra.EssFiniteType K F] (hC : ConstantsAreBase K F)
    [Fintype (Pic0 K F)] (n : ℕ) (hn : 2 * genusFF K F ≤ n + 1) :
    ∑ c : Pic0 K F, (Nat.card K : ℤ) ^ ell (rep D₁ c n) =
      Nat.card (Pic0 K F) * (Nat.card K : ℤ) ^ (n + 1 - genusFF K F) := by
  obtain ⟨W, hdegW, hRR⟩ := exists_W hC
  have hc : ∀ c : Pic0 K F, ell (rep D₁ c n) = n + 1 - genusFF K F := fun c => by
    have h1 := hRR (rep D₁ c n)
    have h2 : ell (W - rep D₁ c n) = 0 := by
      apply ell_eq_zero_of_degree_neg
      rw [map_sub, hdegW, degree_rep]
      omega
    rw [h2, degree_rep] at h1
    push_cast at h1
    omega
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card (α := Pic0 K F)]

theorem H3 [PerfectField K] [Algebra.EssFiniteType K F] (hC : ConstantsAreBase K F)
    [Fintype (Pic0 K F)] (n : ℕ) (hn : n + 2 ≤ 2 * genusFF K F) :
    (Nat.card K : ℤ) ^ (genusFF K F - 1) *
        ∑ c : Pic0 K F, (Nat.card K : ℤ) ^ ell (rep D₁ c n) =
      (Nat.card K : ℤ) ^ n *
        ∑ c : Pic0 K F,
          (Nat.card K : ℤ) ^ ell (rep D₁ c ((2 * genusFF K F - 2 - n : ℕ) : ℤ)) := by
  obtain ⟨W, hdegW, hRR⟩ := exists_W hC
  set g := genusFF K F with hg
  set m : ℕ := 2 * g - 2 - n with hm
  have hmn : (m : ℤ) + n = 2 * (g : ℤ) - 2 := by rw [hm]; omega

  set w₀ : Pic0 K F := cls D₁ W with hw₀
  have hkey : ∀ c : Pic0 K F, ell (rep D₁ (w₀ - c) m) = ell (W - rep D₁ c n) := by
    intro c
    apply ell_eq_of_isPrincipal_sub

    have h1 : cls D₁ (rep D₁ (w₀ - c) (m : ℤ) + rep D₁ c n) = w₀ := by
      have e1 := (cls_eq_iff D₁ (degree_rep D₁ (w₀ - c) (m : ℤ)) (w₀ - c)).mpr
        (by rw [sub_self]; exact ⟨1, one_ne_zero, fun v => by simp⟩)
      have e2 := (cls_eq_iff D₁ (degree_rep D₁ c (n : ℤ)) c).mpr
        (by rw [sub_self]; exact ⟨1, one_ne_zero, fun v => by simp⟩)
      have hadd : cls D₁ (rep D₁ (w₀ - c) (m : ℤ) + rep D₁ c n) =
          cls D₁ (rep D₁ (w₀ - c) (m : ℤ)) + cls D₁ (rep D₁ c n) := by
        rw [cls, cls, cls, ← Pic0.mk_add]
        congr 1
        apply Subtype.ext
        simp only [coe_toDegZero, AddSubgroup.coe_add, map_add, degree_rep]
        rw [add_smul]
        abel
      rw [hadd, e1, e2, sub_add_cancel]
    have h2 := (cls_eq_iff D₁ (n := 2 * (g : ℤ) - 2) (by
      rw [map_add, degree_rep, degree_rep, hmn]) w₀).mp h1
    have h3 : Divisor.IsPrincipal (W - rep D₁ w₀ (2 * (g : ℤ) - 2)) :=
      (cls_eq_iff D₁ hdegW w₀).mp rfl
    obtain ⟨f₂, hf₂, hP₂⟩ := h2
    obtain ⟨f₃, hf₃, hP₃⟩ := h3
    refine ⟨f₂ * f₃⁻¹, mul_ne_zero hf₂ (inv_ne_zero hf₃), fun v => ?_⟩
    rw [v.ord_mul hf₂ (inv_ne_zero hf₃), Place.ord_inv, ← hP₂ v, ← hP₃ v]
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply]
    ring

  have hexp : ∀ c : Pic0 K F, (g - 1) + ell (rep D₁ c n) = n + ell (rep D₁ (w₀ - c) m) := by
    intro c
    have h1 := hRR (rep D₁ c n)
    rw [degree_rep, ← hkey c] at h1
    omega
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft w₀) _ _ fun c => ?_
  rw [← pow_add, ← pow_add, hexp c, Equiv.subLeft_apply]

end Count

theorem main [Finite K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) :
    ∃ L : Polynomial ℤ,
      L.natDegree ≤ 2 * genusFF K F ∧
      L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * genusFF K F,
        L.coeff (2 * genusFF K F - i) * (Nat.card K : ℤ) ^ i =
          (Nat.card K : ℤ) ^ genusFF K F * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card K : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n : ℕ =>
            (Nat.card {D : Divisor K F // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)} : ℤ)) =
        (L : PowerSeries ℤ) := by
  haveI : Finite (Pic0 K F) := Pic0.finite_of_finite K F hC
  letI : Fintype (Pic0 K F) := Fintype.ofFinite _
  obtain ⟨D₁, hD₁⟩ := exists_divisor_degree_eq_one_of_finite K F hC
  have hq1 : (Nat.card K : ℤ) - 1 ≠ 0 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  exact lpoly_of_counts (Nat.card K : ℤ) (Nat.card (Pic0 K F)) hq1 (genusFF K F)
    (fun n => (Nat.card (Eff (K := K) (F := F) n) : ℤ))
    (fun n => ∑ c : Pic0 K F, (Nat.card K : ℤ) ^ ell (rep ⟨D₁, hD₁⟩ c n))
    (fun n => H1 ⟨D₁, hD₁⟩ hC n) (fun n hn => H2 ⟨D₁, hD₁⟩ hC n hn)
    (fun n hn => H3 ⟨D₁, hD₁⟩ hC n hn)
    (show (Nat.card (Eff (K := K) (F := F) 0) : ℤ) = 1 by exact_mod_cast card_eff_zero)

end AlgebraicCurve.LPolynomialSol
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite.AlgebraicCurve.LPolynomialSol"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite.AlgebraicCurve.LPolynomialSol"

theorem solution
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) :
    ∃ L : Polynomial ℤ,
      L.natDegree ≤ 2 * AlgebraicCurve.genusFF k F ∧
      L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * AlgebraicCurve.genusFF k F,
        L.coeff (2 * AlgebraicCurve.genusFF k F - i) * (Nat.card k : ℤ) ^ i =
          (Nat.card k : ℤ) ^ AlgebraicCurve.genusFF k F * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n : ℕ =>
            (Nat.card {D : AlgebraicCurve.Divisor k F //
                0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)} : ℤ)) =
        (L : PowerSeries ℤ) :=
  AlgebraicCurve.LPolynomialSol.main hC

end S_AlgebraicCurve_exists_LPolynomial_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_exists_LPolynomial_of_finite (solution)
