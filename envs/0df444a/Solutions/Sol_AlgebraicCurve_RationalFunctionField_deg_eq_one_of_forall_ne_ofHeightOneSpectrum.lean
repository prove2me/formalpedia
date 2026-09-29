-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3628b5d2-e5eb-58c7-9f12-396ee2671750

import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum.AlgebraicCurve"
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.deg Place.ofHeightOneSpectrum RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum Place.mem_maximalIdeal_iff_adicValuation_lt_one"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField AlgebraicCurve"

namespace WFg
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩
  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]
  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt

end WFg

end AlgebraicCurve.RationalFunctionField

end

theorem solution {K : Type*} [Field K] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.deg = 1 := by
  classical
  have hvS : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring :=
    AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum v hv
  have hequiv : (RatFunc.inftyValuation K).IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hvS.symm
  have hbij : Function.Bijective (Algebra.ofId K v.ResidueField) := by
    constructor
    · exact fun a b h => (algebraMap K v.ResidueField).injective h
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
      have hx' : RatFunc.inftyValuation K x ≤ 1 := by
        rw [hvS] at hx
        exact (Valuation.mem_valuationSubring_iff _ _).mp hx
      obtain ⟨c, hc⟩ :=
        AlgebraicCurve.RationalFunctionField.WFg.exists_sub_algebraMap_intDegree_neg K hx'
      refine ⟨c, ?_⟩
      show IsLocalRing.residue _ (algebraMap K v.toValuationSubring c) = _
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        Place.mem_maximalIdeal_iff_adicValuation_lt_one]
      show v.adicValuation (algebraMap K (RatFunc K) c - x) < 1
      rw [← hequiv.lt_one_iff_lt_one,
        show algebraMap K (RatFunc K) c - x = -(x - algebraMap K (RatFunc K) c) from
          (neg_sub _ _).symm, Valuation.map_neg]
      rcases hc with hc | hc
      · rw [hc, map_zero]
        exact zero_lt_one
      · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]
        split
        · exact zero_lt_one
        · rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
          exact hc
  rw [Place.deg, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

end S_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum (solution)
