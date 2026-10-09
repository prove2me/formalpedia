-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialComparisonFactorPair_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialComparisonFactorPair_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:52:45.170989+00:00
-- url     : https://prove2.me/theorems/31b13417-d742-47d7-a85c-ae336b38d450
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialComparisonFactorPair source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialComparisonFactorPair

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialComparisonFactorPair
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CoherentChartComparison_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Every degree-four special comparison supplies an actual affine factor pair
whose product is a monic polynomial of degree at most eight. The factors
represent the same numerator/denominator as the input comparison, after
clearing only the explicit rational-point fibre polynomials. This removes
arbitrary affine denominators without assuming a principal-code law.
-/

namespace MazurProof.N13SpecialComparisonFactorPair

noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2

abbrev R := N13GoodCoordinateRingTwo.CoordinateRing
abbrev xClass := N13GoodCoordinateRingTwo.xClass

def pointPolynomial : CurvePoint → K[X]
  | Sum.inl P => X - C P.1.1
  | Sum.inr _ => 1

theorem pointPolynomial_monic (P : CurvePoint) : (pointPolynomial P).Monic := by
  cases P
  · exact monic_X_sub_C _
  · exact monic_one

theorem pointPolynomial_degree (P : CurvePoint) : (pointPolynomial P).natDegree ≤ 1 := by
  cases P <;> simp [pointPolynomial]

theorem pointPolynomial_mem (P : CurvePoint) : xClass (pointPolynomial P) ∈ (point P).affineIdeal := by
  cases P with
  | inl P =>
    simp only [point]
    split_ifs with hx
    · exact N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal (X - C P.1.1) (C P.1.2)
    · exact N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal (X - C P.1.1) (C P.1.2)
  | inr P => exact Submodule.mem_top

def divisorPolynomial : EffectiveDivisorTwo → K[X] :=
  Sym2.lift ⟨fun P Q => pointPolynomial P * pointPolynomial Q, fun P Q => mul_comm _ _⟩

@[simp] theorem divisorPolynomial_mk (P Q : CurvePoint) :
    divisorPolynomial s(P, Q) = pointPolynomial P * pointPolynomial Q := rfl

theorem divisorPolynomial_monic (D : EffectiveDivisorTwo) : (divisorPolynomial D).Monic := by
  refine Sym2.inductionOn D ?_
  intro P Q
  exact (pointPolynomial_monic P).mul (pointPolynomial_monic Q)

theorem divisorPolynomial_degree (D : EffectiveDivisorTwo) : (divisorPolynomial D).natDegree ≤ 2 := by
  refine Sym2.inductionOn D ?_
  intro P Q
  rw [divisorPolynomial_mk, Polynomial.natDegree_mul
    (pointPolynomial_monic P).ne_zero (pointPolynomial_monic Q).ne_zero]
  have hp := pointPolynomial_degree P
  have hq := pointPolynomial_degree Q
  omega

theorem divisorPolynomial_mem (D : EffectiveDivisorTwo) :
    xClass (divisorPolynomial D) ∈ (ofDivisor D).affineIdeal := by
  refine Sym2.inductionOn D ?_
  intro P Q
  change xClass (pointPolynomial P * pointPolynomial Q) ∈
    (point P).affineIdeal * (point Q).affineIdeal
  simp only [xClass, N13GoodCoordinateRingTwo.xClass_mul]
  exact Ideal.mul_mem_mul (pointPolynomial_mem P) (pointPolynomial_mem Q)

def tensorPolynomial (D E : EffectiveDivisorTwo) : K[X] := divisorPolynomial D * divisorPolynomial E

theorem tensorPolynomial_monic (D E : EffectiveDivisorTwo) : (tensorPolynomial D E).Monic :=
  (divisorPolynomial_monic D).mul (divisorPolynomial_monic E)

theorem tensorPolynomial_degree (D E : EffectiveDivisorTwo) : (tensorPolynomial D E).natDegree ≤ 4 := by
  rw [tensorPolynomial, Polynomial.natDegree_mul
    (divisorPolynomial_monic D).ne_zero (divisorPolynomial_monic E).ne_zero]
  have hd := divisorPolynomial_degree D
  have he := divisorPolynomial_degree E
  omega

theorem tensorPolynomial_mem (D E : EffectiveDivisorTwo) :
    xClass (tensorPolynomial D E) ∈ (tensor (ofDivisor D) (ofDivisor E)).affineIdeal := by
  change xClass (divisorPolynomial D * divisorPolynomial E) ∈
    (ofDivisor D).affineIdeal * (ofDivisor E).affineIdeal
  simp only [xClass, N13GoodCoordinateRingTwo.xClass_mul]
  exact Ideal.mul_mem_mul (divisorPolynomial_mem D) (divisorPolynomial_mem E)

theorem pointPolynomial_fibres (P : CurvePoint) :
    ∃ i j : ℕ, i + j ≤ 1 ∧ pointPolynomial P = X ^ i * (X - 1) ^ j := by
  cases P with
  | inl P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.1 (ZMod.pow_card P.1.1) with hx | hx
    · exact ⟨1, 0, by decide, by simp [pointPolynomial, hx]⟩
    · exact ⟨0, 1, by decide, by simp [pointPolynomial, hx]⟩
  | inr P => exact ⟨0, 0, by decide, by simp [pointPolynomial]⟩

theorem divisorPolynomial_fibres (D : EffectiveDivisorTwo) :
    ∃ i j : ℕ, i + j ≤ 2 ∧ divisorPolynomial D = X ^ i * (X - 1) ^ j := by
  refine Sym2.inductionOn D ?_
  intro P Q
  obtain ⟨i, j, hij, hp⟩ := pointPolynomial_fibres P
  obtain ⟨k, l, hkl, hq⟩ := pointPolynomial_fibres Q
  refine ⟨i + k, j + l, by omega, ?_⟩
  rw [divisorPolynomial_mk, hp, hq, pow_add, pow_add]
  ring

theorem tensorPolynomial_fibres (D E : EffectiveDivisorTwo) :
    ∃ i j : ℕ, i + j ≤ 4 ∧ tensorPolynomial D E = X ^ i * (X - 1) ^ j := by
  obtain ⟨i, j, hij, hd⟩ := divisorPolynomial_fibres D
  obtain ⟨k, l, hkl, he⟩ := divisorPolynomial_fibres E
  refine ⟨i + k, j + l, by omega, ?_⟩
  rw [tensorPolynomial, hd, he, pow_add, pow_add]
  ring

/-- The full special comparison, rather than an arbitrary guessed small
function, supplies the regular factor pair and the exact two cross-products. -/
theorem exists_factor_pair_of_comparison
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ z w : R,
      z ∈ (tensor (ofDivisor F) (ofDivisor H)).affineIdeal ∧
      w ∈ (tensor (ofDivisor D) (ofDivisor E)).affineIdeal ∧
      h.aNum * xClass (tensorPolynomial D E) = h.aDen * z ∧
      h.aDen * xClass (tensorPolynomial F H) = h.aNum * w ∧
      z * w = xClass (tensorPolynomial D E * tensorPolynomial F H) ∧ z ≠ 0 ∧ w ≠ 0 := by
  have hz : h.aNum * xClass (tensorPolynomial D E) ∈
      Ideal.span ({h.aDen} : Set R) * (tensor (ofDivisor F) (ofDivisor H)).affineIdeal := by
    rw [← h.affine_eq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨_, tensorPolynomial_mem D E, rfl⟩
  have hw : h.aDen * xClass (tensorPolynomial F H) ∈
      Ideal.span ({h.aNum} : Set R) * (tensor (ofDivisor D) (ofDivisor E)).affineIdeal := by
    rw [h.affine_eq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨_, tensorPolynomial_mem F H, rfl⟩
  obtain ⟨z, hzmem, hzeq⟩ := Ideal.mem_span_singleton_mul.mp hz
  obtain ⟨w, hwmem, hweq⟩ := Ideal.mem_span_singleton_mul.mp hw
  have hprod : z * w = xClass (tensorPolynomial D E * tensorPolynomial F H) := by
    apply mul_left_cancel₀ (mul_ne_zero h.aNum_ne h.aDen_ne)
    simp only [xClass, N13GoodCoordinateRingTwo.xClass_mul]
    calc
      (h.aNum * h.aDen) * (z * w) = (h.aDen * z) * (h.aNum * w) := by ring
      _ = (h.aNum * xClass (tensorPolynomial D E)) *
          (h.aDen * xClass (tensorPolynomial F H)) := by rw [hzeq, hweq]
      _ = _ := by ring
  have hnonzero : z * w ≠ 0 := by
    rw [hprod]
    exact N13GoodCoordinateRingTwo.xClass_ne_zero
      (mul_ne_zero (tensorPolynomial_monic D E).ne_zero (tensorPolynomial_monic F H).ne_zero)
  exact ⟨z, w, hzmem, hwmem, hzeq.symm, hweq.symm, hprod,
    left_ne_zero_of_mul hnonzero, right_ne_zero_of_mul hnonzero⟩

theorem factor_pair_polynomial_degree (D E F H : EffectiveDivisorTwo) :
    (tensorPolynomial D E * tensorPolynomial F H).natDegree ≤ 8 := by
  rw [Polynomial.natDegree_mul (tensorPolynomial_monic D E).ne_zero (tensorPolynomial_monic F H).ne_zero]
  have hleft := tensorPolynomial_degree D E
  have hright := tensorPolynomial_degree F H
  omega

end
end MazurProof.N13SpecialComparisonFactorPair


