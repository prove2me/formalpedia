-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2ead6451-88b8-5b4f-af04-e79cd8ad8fb3

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve
namespace Ws49
namespace N3

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_eq_zero_of_mem_of_inv_mem (v : Place K F) {x : F}
    (hx : x ∈ v.toValuationSubring) (hx' : x⁻¹ ∈ v.toValuationSubring) : v.ord x = 0 := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact v.ord_zero
  · have h1 : 0 ≤ v.ord x := (v.mem_iff_ord_nonneg h0).mp hx
    have h2 : 0 ≤ v.ord x⁻¹ := (v.mem_iff_ord_nonneg (inv_ne_zero h0)).mp hx'
    rw [v.ord_inv] at h2
    omega

theorem inv_mem_and_valuation_lt_one_of_not_mem (v : Place K F) {j : F}
    (hj : j ∉ v.toValuationSubring) :
    j⁻¹ ∈ v.toValuationSubring ∧ v.toValuationSubring.valuation j⁻¹ < 1 := by
  have hmem : j⁻¹ ∈ v.toValuationSubring := by
    rcases v.toValuationSubring.mem_or_inv_mem j with h | h
    · exact absurd h hj
    · exact h
  refine ⟨hmem, ?_⟩
  have hle : v.toValuationSubring.valuation j⁻¹ ≤ 1 :=
    (v.toValuationSubring.valuation_le_one_iff _).mpr hmem
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hj (zero_mem _)
    rw [← v.toValuationSubring.valuation_le_one_iff]
    have : v.toValuationSubring.valuation j = 1 := by
      have h := map_inv₀ v.toValuationSubring.valuation j
      rw [heq] at h
      exact inv_eq_one.mp h.symm
    exact this.le

theorem valuation_algebraMap_eq_one (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.toValuationSubring.valuation (algebraMap K F c) = 1 := by
  have h1 : v.toValuationSubring.valuation (algebraMap K F c) ≤ 1 :=
    (v.toValuationSubring.valuation_le_one_iff _).mpr (v.algebraMap_mem' c)
  have h2 : v.toValuationSubring.valuation (algebraMap K F c⁻¹) ≤ 1 :=
    (v.toValuationSubring.valuation_le_one_iff _).mpr (v.algebraMap_mem' c⁻¹)
  have hc0 : algebraMap K F c ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc
  have hprod : v.toValuationSubring.valuation (algebraMap K F c) *
      v.toValuationSubring.valuation (algebraMap K F c⁻¹) = 1 := by
    rw [← map_mul, map_inv₀ (algebraMap K F), mul_inv_cancel₀ hc0, map_one]
  by_contra hne
  have hlt : v.toValuationSubring.valuation (algebraMap K F c) < 1 := lt_of_le_of_ne h1 hne
  have : v.toValuationSubring.valuation (algebraMap K F c) *
      v.toValuationSubring.valuation (algebraMap K F c⁻¹) < 1 :=
    calc v.toValuationSubring.valuation (algebraMap K F c) *
          v.toValuationSubring.valuation (algebraMap K F c⁻¹)
        ≤ v.toValuationSubring.valuation (algebraMap K F c) * 1 := by gcongr
      _ = v.toValuationSubring.valuation (algebraMap K F c) := mul_one _
      _ < 1 := hlt
  rw [hprod] at this
  exact lt_irrefl _ this

theorem aeval_mem (v : Place K F) {u : F} (hu : u ∈ v.toValuationSubring) (r : K[X]) :
    aeval u r ∈ v.toValuationSubring := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact mul_mem (v.algebraMap_mem' a) (pow_mem hu n)

theorem valuation_aeval_eq_one (v : Place K F) {u : F} (hu : u ∈ v.toValuationSubring)
    (hu1 : v.toValuationSubring.valuation u < 1) (q : K[X]) (hq : q.coeff 0 ≠ 0) :
    v.toValuationSubring.valuation (aeval u q) = 1 := by

  obtain ⟨r, hr⟩ : ∃ r : K[X], q = C (q.coeff 0) + X * r := ⟨q.divX, by
    conv_lhs => rw [← q.divX_mul_X_add]
    ring⟩
  have hval_r : v.toValuationSubring.valuation (aeval u r) ≤ 1 :=
    (v.toValuationSubring.valuation_le_one_iff _).mpr (aeval_mem v hu r)
  have hsmall : v.toValuationSubring.valuation (u * aeval u r) < 1 := by
    rw [map_mul]
    calc v.toValuationSubring.valuation u * v.toValuationSubring.valuation (aeval u r)
        ≤ v.toValuationSubring.valuation u * 1 := by gcongr
      _ = v.toValuationSubring.valuation u := mul_one _
      _ < 1 := hu1
  have hconst : v.toValuationSubring.valuation (algebraMap K F (q.coeff 0)) = 1 :=
    valuation_algebraMap_eq_one v hq
  have hq' : aeval u q = algebraMap K F (q.coeff 0) + u * aeval u r := by
    conv_lhs => rw [hr]
    simp [map_add, map_mul, aeval_C, aeval_X]
  rw [hq']
  rw [Valuation.map_add_eq_of_lt_left]
  · exact hconst
  · rw [hconst]; exact hsmall

theorem aeval_div_aeval_mem (v : Place K F) {u : F} (hu : u ∈ v.toValuationSubring)
    (hu1 : v.toValuationSubring.valuation u < 1) (p q : K[X]) (hq : q.coeff 0 ≠ 0) :
    aeval u p / aeval u q ∈ v.toValuationSubring := by
  rw [← v.toValuationSubring.valuation_le_one_iff, map_div₀, valuation_aeval_eq_one v hu hu1 q hq,
    div_one, v.toValuationSubring.valuation_le_one_iff]
  exact aeval_mem v hu p

theorem mem_of_monic_of_coeff_eq_aeval_div (v : Place K F) {u : F} (hu : u ∈ v.toValuationSubring)
    (hu1 : v.toValuationSubring.valuation u < 1) {P : F[X]} (hP : P.Monic)
    (hcoeff : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ P.coeff i = aeval u p / aeval u q)
    {x : F} (hx : P.eval x = 0) : x ∈ v.toValuationSubring := by
  refine v.mem_of_eval_monic_eq_zero hP (fun i => ?_) hx
  obtain ⟨p, q, hq, hi⟩ := hcoeff i
  rw [hi]
  exact aeval_div_aeval_mem v hu hu1 p q hq

theorem ord_eq_zero_of_not_mem (v : Place K F) {j : F} (hj : j ∉ v.toValuationSubring)
    {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ P.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    (hQc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ Q.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    {x : F} (hx : P.eval x = 0) (hx' : Q.eval x⁻¹ = 0) : v.ord x = 0 := by
  obtain ⟨hu, hu1⟩ := inv_mem_and_valuation_lt_one_of_not_mem v hj
  exact ord_eq_zero_of_mem_of_inv_mem v
    (mem_of_monic_of_coeff_eq_aeval_div v hu hu1 hP hPc hx)
    (mem_of_monic_of_coeff_eq_aeval_div v hu hu1 hQ hQc hx')

end ModularCurve.Ws49.N3

end

open Polynomial in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {j : F} (hj : j ∉ v.toValuationSubring)
    {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ P.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    (hQc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ Q.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    {x : F} (hx : P.eval x = 0) (hx' : Q.eval x⁻¹ = 0) :
    v.ord x = 0 :=
  ModularCurve.Ws49.N3.ord_eq_zero_of_not_mem v hj hP hQ hPc hQc hx hx'

end S_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div (solution)
