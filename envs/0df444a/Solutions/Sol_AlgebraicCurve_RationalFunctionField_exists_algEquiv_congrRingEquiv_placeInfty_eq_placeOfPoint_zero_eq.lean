-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.exists_algEquiv_congrRingEquiv_placeInfty_eq_placeOfPoint_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4c1911ca-6b71-5856-be2f-d5a20b9c8e8e

import Mathlib
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_RatFunc_exists_algEquiv_apply_X_eq_moebius
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_exists_algEquiv_congrRingEquiv_placeInfty_eq_placeOfPoint_zero_eq
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve

namespace LMOB
open AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K]

theorem ord_C (v : Place K (RatFunc K)) {a : K} (ha : a ≠ 0) : v.ord (RatFunc.C a) = 0 := by
  have hmem : ∀ b : K, (RatFunc.C b : RatFunc K) ∈ v.toValuationSubring := fun b => v.algebraMap_mem' b
  let u : (v.toValuationSubring)ˣ :=
    ⟨⟨RatFunc.C a, hmem a⟩, ⟨RatFunc.C a⁻¹, hmem a⁻¹⟩,
      Subtype.ext (show RatFunc.C a * RatFunc.C a⁻¹ = 1 by rw [← map_mul, mul_inv_cancel₀ ha, map_one]),
      Subtype.ext (show RatFunc.C a⁻¹ * RatFunc.C a = 1 by rw [← map_mul, inv_mul_cancel₀ ha, map_one])⟩
  exact v.ord_coe_unit u

theorem ord_congr_symm (ψ : RatFunc K ≃ₐ[K] RatFunc K) (u : Place K (RatFunc K)) (g : RatFunc K) :
    (Place.congrRingEquiv ψ.symm.toRingEquiv (fun a => ψ.symm.commutes a) u).ord g = u.ord (ψ g) := by
  have h := Place.ord_congrRingEquiv ψ.symm.toRingEquiv (fun a => ψ.symm.commutes a) u (ψ g)
  have e : ψ.symm.toRingEquiv (ψ g) = g := ψ.symm_apply_apply g
  rw [e] at h
  exact h

theorem algebraMap_X_sub_C (b : K) :
    algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C b) = RatFunc.X - RatFunc.C b := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

variable [DecidableEq (RatFunc K)]

theorem ord_X_sub_C' (b : K) (v : Place K (RatFunc K)) :
    v.ord (RatFunc.X - RatFunc.C b) =
      (Finsupp.single (placeOfPoint K b) (1 : ℤ) + Finsupp.single (placeInfty K) (-1 : ℤ)) v := by
  rw [← algebraMap_X_sub_C]; exact AlgebraicCurve.RationalFunctionField.ord_X_sub_C K b v

theorem ord_placeOfPoint_X_sub_C_self (b : K) : (placeOfPoint K b).ord (RatFunc.X - RatFunc.C b) = 1 := by
  rw [ord_X_sub_C', Finsupp.add_apply]
  have h := AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty K b
  simp [h]

theorem ord_placeOfPoint_zero_X : (placeOfPoint K (0 : K)).ord (RatFunc.X : RatFunc K) = 1 := by
  have h := ord_placeOfPoint_X_sub_C_self (K := K) (0 : K)
  rwa [map_zero, sub_zero] at h

theorem ord_placeInfty_X_sub_C (b : K) : (placeInfty K).ord (RatFunc.X - RatFunc.C b) = -1 := by
  rw [ord_X_sub_C', Finsupp.add_apply]
  have h := AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty K b
  simp [h.symm]

theorem ord_placeOfPoint_X_sub_C_of_ne {b b' : K} (hb : b ≠ b') :
    (placeOfPoint K b').ord (RatFunc.X - RatFunc.C b) = 0 := by
  rw [ord_X_sub_C', Finsupp.add_apply]
  have h := AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty K b'
  have h1 : placeOfPoint K b ≠ placeOfPoint K b' := fun e => hb (AlgebraicCurve.RationalFunctionField.placeOfPoint_injective K e)
  simp [h, h1.symm]

theorem X_sub_C_ne_zero (b : K) : (RatFunc.X - RatFunc.C b : RatFunc K) ≠ 0 := by
  intro h0
  have h := ord_placeInfty_X_sub_C (K := K) b
  rw [h0, Place.ord_zero] at h
  norm_num at h

theorem eq_placeOfPoint_of_ord_pos (u : Place K (RatFunc K)) (b : K)
    (hu : 0 < u.ord (RatFunc.X - RatFunc.C b)) : u = placeOfPoint K b := by
  classical
  by_contra hne
  rw [ord_X_sub_C', Finsupp.add_apply] at hu
  have h1 : (Finsupp.single (placeOfPoint K b) (1 : ℤ)) u = 0 := by
    rw [Finsupp.single_apply, if_neg (Ne.symm hne)]
  have h2 : (Finsupp.single (placeInfty K) (-1 : ℤ)) u ≤ 0 := by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  omega

end LMOB

theorem solution
    (k : Type*) [Field k] [DecidableEq (RatFunc k)]
    (v w : Place k (RatFunc k)) (hvw : v ≠ w)
    (hv : v = RationalFunctionField.placeInfty k ∨ ∃ c : k, v = RationalFunctionField.placeOfPoint k c)
    (hw : w = RationalFunctionField.placeInfty k ∨ ∃ c : k, w = RationalFunctionField.placeOfPoint k c) :
    ∃ φ : RatFunc k ≃ₐ[k] RatFunc k,
      Place.congrRingEquiv φ.toRingEquiv (fun a => φ.commutes a) (RationalFunctionField.placeInfty k) = v ∧
      Place.congrRingEquiv φ.toRingEquiv (fun a => φ.commutes a) (RationalFunctionField.placeOfPoint k 0) = w := by
  classical

  suffices H : ∃ ψ : RatFunc k ≃ₐ[k] RatFunc k,
      Place.congrRingEquiv ψ.symm.toRingEquiv (fun a => ψ.symm.commutes a) (RationalFunctionField.placeInfty k) = v ∧
      Place.congrRingEquiv ψ.symm.toRingEquiv (fun a => ψ.symm.commutes a) (RationalFunctionField.placeOfPoint k 0) = w by
    obtain ⟨ψ, h⟩ := H
    exact ⟨ψ.symm, h⟩
  have hX0 : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  have hC : ∀ (ψ : RatFunc k ≃ₐ[k] RatFunc k) (a : k), ψ (RatFunc.C a) = RatFunc.C a := fun ψ a => ψ.commutes a
  have hX1 : (RatFunc.X + 1 : RatFunc k) = RatFunc.X - RatFunc.C (-1) := by rw [map_neg, map_one, sub_neg_eq_add]
  have hX1ne : (RatFunc.X + 1 : RatFunc k) ≠ 0 := by rw [hX1]; exact LMOB.X_sub_C_ne_zero (-1)
  rcases hv with rfl | ⟨c, rfl⟩ <;> rcases hw with rfl | ⟨d, rfl⟩
  · exact absurd rfl hvw
  ·
    obtain ⟨ψ, hψ⟩ := RatFunc.exists_algEquiv_apply_X_eq_moebius (1 : k) d 0 1 (by norm_num)
    have hψX : ψ RatFunc.X = RatFunc.X + RatFunc.C d := by
      rw [hψ, map_one, map_zero, one_mul, zero_mul, zero_add, div_one]
    refine ⟨ψ, ?_, ?_⟩
    · apply RationalFunctionField.eq_placeInfty_of_ord_X_neg
      rw [LMOB.ord_congr_symm, hψX,
        show (RatFunc.X + RatFunc.C d : RatFunc k) = RatFunc.X - RatFunc.C (-d) by rw [map_neg, sub_neg_eq_add],
        LMOB.ord_placeInfty_X_sub_C]
      norm_num
    · apply LMOB.eq_placeOfPoint_of_ord_pos
      rw [LMOB.ord_congr_symm, map_sub, hC, hψX, add_sub_cancel_right, LMOB.ord_placeOfPoint_zero_X]
      norm_num
  ·
    obtain ⟨ψ, hψ⟩ := RatFunc.exists_algEquiv_apply_X_eq_moebius c (1 : k) 1 0 (by norm_num)
    have hψX : ψ RatFunc.X = (RatFunc.C c * RatFunc.X + 1) / RatFunc.X := by
      rw [hψ, map_one, map_zero, one_mul, add_zero]
    refine ⟨ψ, ?_, ?_⟩
    · apply LMOB.eq_placeOfPoint_of_ord_pos
      rw [LMOB.ord_congr_symm, map_sub, hC, hψX]
      have hid : ((RatFunc.C c * RatFunc.X + 1) / RatFunc.X - RatFunc.C c : RatFunc k) = (RatFunc.X)⁻¹ := by
        field_simp
        ring
      rw [hid, Place.ord_inv, RationalFunctionField.ord_placeInfty_X]
      norm_num
    · apply RationalFunctionField.eq_placeInfty_of_ord_X_neg
      rw [LMOB.ord_congr_symm, hψX]
      by_cases hc : c = 0
      · subst hc
        rw [map_zero, zero_mul, zero_add, one_div, Place.ord_inv, LMOB.ord_placeOfPoint_zero_X]
        norm_num
      · have hCc : (RatFunc.C c : RatFunc k) ≠ 0 := (map_ne_zero RatFunc.C).mpr hc
        have hfac : (RatFunc.C c * RatFunc.X + 1 : RatFunc k) = RatFunc.C c * (RatFunc.X - RatFunc.C (-c⁻¹)) := by
          rw [map_neg, map_inv₀, sub_neg_eq_add, mul_add, mul_inv_cancel₀ hCc]
        have hnum : (RatFunc.C c * RatFunc.X + 1 : RatFunc k) ≠ 0 := by
          rw [hfac]; exact mul_ne_zero hCc (LMOB.X_sub_C_ne_zero _)
        rw [div_eq_mul_inv, Place.ord_mul _ hnum (inv_ne_zero hX0), Place.ord_inv, hfac,
          Place.ord_mul _ hCc (LMOB.X_sub_C_ne_zero _), LMOB.ord_C _ hc,
          LMOB.ord_placeOfPoint_X_sub_C_of_ne (b := -c⁻¹) (b' := 0) (neg_ne_zero.mpr (inv_ne_zero hc)),
          LMOB.ord_placeOfPoint_zero_X]
        norm_num
  ·
    have hcd : c ≠ d := fun h => hvw (by rw [h])
    obtain ⟨ψ, hψ⟩ := RatFunc.exists_algEquiv_apply_X_eq_moebius c d 1 1
      (by rw [mul_one, mul_one]; exact sub_ne_zero.mpr hcd)
    have hψX : ψ RatFunc.X = (RatFunc.C c * RatFunc.X + RatFunc.C d) / (RatFunc.X + 1) := by
      rw [hψ, map_one, one_mul]
    have hcd' : (RatFunc.C (d - c) : RatFunc k) ≠ 0 := (map_ne_zero RatFunc.C).mpr (sub_ne_zero.mpr (Ne.symm hcd))
    have hcd'' : (RatFunc.C (c - d) : RatFunc k) ≠ 0 := (map_ne_zero RatFunc.C).mpr (sub_ne_zero.mpr hcd)
    refine ⟨ψ, ?_, ?_⟩
    · apply LMOB.eq_placeOfPoint_of_ord_pos
      rw [LMOB.ord_congr_symm, map_sub, hC, hψX]
      have hid : ((RatFunc.C c * RatFunc.X + RatFunc.C d) / (RatFunc.X + 1) - RatFunc.C c : RatFunc k)
          = RatFunc.C (d - c) * (RatFunc.X + 1)⁻¹ := by
        rw [map_sub]
        field_simp
        ring
      rw [hid, Place.ord_mul _ hcd' (inv_ne_zero hX1ne), Place.ord_inv, LMOB.ord_C _ (sub_ne_zero.mpr (Ne.symm hcd)),
        hX1, LMOB.ord_placeInfty_X_sub_C]
      norm_num
    · apply LMOB.eq_placeOfPoint_of_ord_pos
      rw [LMOB.ord_congr_symm, map_sub, hC, hψX]
      have hid : ((RatFunc.C c * RatFunc.X + RatFunc.C d) / (RatFunc.X + 1) - RatFunc.C d : RatFunc k)
          = RatFunc.C (c - d) * RatFunc.X * (RatFunc.X + 1)⁻¹ := by
        rw [map_sub]
        field_simp
        ring
      rw [hid, Place.ord_mul _ (mul_ne_zero hcd'' hX0) (inv_ne_zero hX1ne), Place.ord_mul _ hcd'' hX0, Place.ord_inv,
        LMOB.ord_C _ (sub_ne_zero.mpr hcd), hX1,
        LMOB.ord_placeOfPoint_X_sub_C_of_ne (b := -1) (b' := 0) (neg_ne_zero.mpr one_ne_zero),
        LMOB.ord_placeOfPoint_zero_X]
      norm_num

end S_AlgebraicCurve_RationalFunctionField_exists_algEquiv_congrRingEquiv_placeInfty_eq_placeOfPoint_zero_eq
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_exists_algEquiv_congrRingEquiv_placeInfty_eq_placeOfPoint_zero_eq (solution)
