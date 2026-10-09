-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveVerticalPresentation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveVerticalPresentation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:34:06.020744+00:00
-- url     : https://prove2.me/theorems/c56bfeb1-c689-41a4-a7fa-0e159599c286
-- title:
--   FLT.Assumptions.MazurProof.N13PrimitiveVerticalPresentation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13PrimitiveVerticalPresentation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13PrimitiveVerticalPresentation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InvertibleReductionSaturation_p0
import Mathlib.RingTheory.Filtration

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Mathlib pin: 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Krull intersection gives an actual primitive factorization of every
nonzero integral chart function. A rational function therefore has a
numerator and denominator with nonzero reductions after removing the two
explicit vertical powers. Transport to the other chart remains separate.
-/

namespace MazurProof.N13PrimitiveVerticalPresentation

noncomputable section
open scoped nonZeroDivisors

variable {A S : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing S] [Nontrivial S]

/-- In a Noetherian domain, a nonzero element has a last divisible power
of a proper principal reduction kernel. The remaining factor has nonzero
reduction. The exponent and factor are actual witnesses. -/
theorem exists_primitive_factor
    (red : A →+* S) (p : A)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (z : A) (hz : z ≠ 0) :
    ∃ n : ℕ, ∃ a : A, red a ≠ 0 ∧ z = p ^ n * a := by
  classical
  have hproper : Ideal.span ({p} : Set A) ≠ ⊤ := by
    intro htop
    have hmem : (1 : A) ∈ RingHom.ker red := by
      rw [hker, htop]
      exact Submodule.mem_top
    have hzero := RingHom.mem_ker.mp hmem
    simpa using hzero
  have hex : ∃ n : ℕ, ¬p ^ n ∣ z := by
    by_contra h
    push_neg at h
    have hm : z ∈ ⨅ n : ℕ, Ideal.span ({p} : Set A) ^ n := by
      refine (Submodule.mem_iInf _).mpr fun n => ?_
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h n
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hproper, Ideal.mem_bot] at hm
    exact hz hm
  have hnondvd := Nat.find_spec hex
  have hnpos : 0 < Nat.find hex := by
    by_contra h
    have hnzero : Nat.find hex = 0 := by omega
    simp [hnzero] at hnondvd
  have hdvd : p ^ (Nat.find hex - 1) ∣ z := by
    by_contra h
    have hh := Nat.find_min' hex h
    omega
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨Nat.find hex - 1, a, ?_, ha⟩
  intro hared
  have hpa : p ∣ a := by
    have hh : a ∈ RingHom.ker red := RingHom.mem_ker.mpr hared
    rwa [hker, Ideal.mem_span_singleton] at hh
  obtain ⟨b, hb⟩ := hpa
  apply hnondvd
  refine ⟨b, ?_⟩
  have hn : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  calc
    z = p ^ (Nat.find hex - 1) * a := ha
    _ = p ^ (Nat.find hex - 1) * (p * b) := by rw [hb]
    _ = (p ^ (Nat.find hex - 1) * p) * b := by rw [mul_assoc]
    _ = p ^ (Nat.find hex - 1 + 1) * b := by
      rw [← pow_succ]
      <;> simp [Nat.succ_pred_eq_of_pos hnpos]
    _ = p ^ Nat.find hex * b := by rw [hn]

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- Remove vertical powers from a numerator and denominator separately.
The displayed cross-multiplied equation records the exact normalization,
so no equality of fractions is silently changed. -/
theorem exists_primitive_fraction_presentation
    (red : A →+* S) (p : A)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (f : K) (hf : f ≠ 0) :
    ∃ n m : ℕ, ∃ a b : A,
      red a ≠ 0 ∧ red b ≠ 0 ∧
      (algebraMap A K p) ^ m * f * algebraMap A K b =
        (algebraMap A K p) ^ n * algebraMap A K a := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective A f
  have hy0 : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
  have hx0 : x ≠ 0 := by
    intro hx
    apply hf
    rw [← hxy, hx, map_zero, zero_div]
  obtain ⟨n, a, ha, hxa⟩ := exists_primitive_factor red p hker x hx0
  obtain ⟨m, b, hb, hyb⟩ := exists_primitive_factor red p hker y hy0
  refine ⟨n, m, a, b, ha, hb, ?_⟩
  have hyK : algebraMap A K y ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hmul : f * algebraMap A K y = algebraMap A K x := by
    rw [← hxy, div_mul_cancel₀ _ hyK]
  rw [hxa, hyb, map_mul, map_mul, map_pow, map_pow] at hmul
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

section N13Charts

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Affine := N13IntegralFractionalHull.IntegralRing
abbrev Infinity := N13IntegralInfinityPointSpread.InfinityCurve
abbrev CommonField := N13IntegralFractionalHull.FunctionField

local instance instAlgebraAffineRationalRing : Algebra Affine N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance instIsFractionRingAffineCommonField : IsFractionRing Affine CommonField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- Concrete primitive factorization on the ordinary affine N13 chart. -/
theorem exists_affine_primitive_factor (z : Affine) (hz : z ≠ 0) :
    ∃ n : ℕ, ∃ a : Affine,
      N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0 ∧ z = (2 : Affine) ^ n * a := by
  apply exists_primitive_factor N13GeneralizedMumfordReduction.reduceCoordinate
    (algebraMap N13GeneralizedMumfordReduction.R₂ Affine 2) _ z hz
  simpa only [N13GeneralizedMumfordReduction.ker_reduceCoordinate]

/-- Concrete primitive factorization on the ordinary infinity N13 chart. -/
theorem exists_infinity_primitive_factor (z : Infinity) (hz : z ≠ 0) :
    ∃ n : ℕ, ∃ a : Infinity,
      N13IntegralInfinityReduction.reduceCoordinate a ≠ 0 ∧ z = (2 : Infinity) ^ n * a := by
  apply exists_primitive_factor N13IntegralInfinityReduction.reduceCoordinate
    (algebraMap N13IntegralInfinityReduction.R₂ Infinity 2) _ z hz
  simpa only [N13IntegralInfinityReduction.ker_reduceCoordinate]

/-- Every nonzero N13 common-field function has primitive affine numerator
and denominator, with the exact removed powers of two recorded. -/
theorem exists_affine_primitive_fraction_presentation (f : CommonField) (hf : f ≠ 0) :
    ∃ n m : ℕ, ∃ a b : Affine,
      N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0 ∧
      N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0 ∧
      (algebraMap Affine CommonField 2) ^ m * f * algebraMap Affine CommonField b =
        (algebraMap Affine CommonField 2) ^ n * algebraMap Affine CommonField a := by
  simpa only [N13GeneralizedMumfordReduction.ker_reduceCoordinate] using
    exists_primitive_fraction_presentation
      N13GeneralizedMumfordReduction.reduceCoordinate 2
      N13GeneralizedMumfordReduction.ker_reduceCoordinate f hf

end N13Charts

end
end MazurProof.N13PrimitiveVerticalPresentation


