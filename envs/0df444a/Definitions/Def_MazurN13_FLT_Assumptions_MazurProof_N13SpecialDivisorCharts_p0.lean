-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorCharts_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorCharts_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:05:42.303993+00:00
-- url     : https://prove2.me/theorems/f0fa7b6e-8b7c-42c5-bfdf-dcfb08638490
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialDivisorCharts source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialDivisorCharts

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialDivisorCharts
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartSpecialRestriction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareTwo_p0

set_option autoImplicit false




/-!
# Canonical special-chart ideals of degree-two divisors

The completed special N13 curve is covered by its ordinary affine chart and
its infinity chart.  A finite point with horizontal coordinate zero is absent
from the overlap, a finite point with horizontal coordinate one lies on both
charts, and an infinity point is absent from the ordinary affine chart.

This file assigns to every completed point its compatible pair of chart
ideals.  Products of two point pairs then descend through the symmetric square
to give canonical chart ideals for every effective divisor of degree two.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialDivisorCharts

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The residue field of the special curve. -/
abbrev K : Type :=
  N13GoodModelTwo.F2

/-- Finite points on the special affine chart. -/
abbrev AffinePoint : Type :=
  N13GoodModelTwo.AffinePoint K

/-- Points on the divisor at infinity. -/
abbrev InfinityPoint : Type :=
  N13GoodModelTwo.InfinityPoint K

/-- Points on the completed special curve. -/
abbrev CurvePoint : Type :=
  N13SymmetricSquareTwo.CurvePoint

/-- Effective divisors of degree two on the completed special curve. -/
abbrev EffectiveDivisorTwo : Type :=
  N13SymmetricSquareTwo.EffectiveDivisorTwo

/-- The special affine coordinate ring. -/
abbrev SpecialAffine : Type :=
  N13TwoChartSpecialRestriction.SpecialAffine

/-- The special infinity-chart coordinate ring. -/
abbrev SpecialInfinity : Type :=
  N13TwoChartSpecialRestriction.SpecialInfinity

/-- The common special overlap ring. -/
abbrev SpecialOverlap : Type :=
  N13SpecialCurveOverlap.InfinityOverlap

/-- Compatible ideals on the two special charts. -/
abbrev ChartPair : Type :=
  N13TwoChartSpecialRestriction.ChartPair

/-- The point ideal of a finite special point on the ordinary affine chart. -/
def affinePointIdeal (P : AffinePoint) : Ideal SpecialAffine :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    (X - C P.1.1)
    (C P.1.2)

/-- The point ideal with coordinates `(t,v)` on the special infinity chart. -/
def infinityPointIdeal (t v : K) : Ideal SpecialInfinity :=
  Ideal.span
    {N13SpecialInfinityChart.tClass -
        algebraMap K[X] SpecialInfinity (C t),
      N13SpecialInfinityChart.vClass -
        algebraMap K[X] SpecialInfinity (C v)}

/-- Extension of a finite point ideal to the common overlap has the expected
two explicit generators. -/
theorem map_affinePointIdeal (P : AffinePoint) :
    Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (affinePointIdeal P) =
      Ideal.span
        {N13SpecialCurveOverlap.xOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.1,
          N13SpecialCurveOverlap.xOverlap ^ 3 *
              N13SpecialCurveOverlap.vOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.2} := by
  simp [affinePointIdeal, N13GoodCoordinateRingTwo.mumfordIdeal,
    N13GoodCoordinateRingTwo.ySubClass, Ideal.map_span, Set.image_pair,
    N13GoodCoordinateRingTwo.xClass, N13GoodCoordinateRingTwo.mk,
    N13SpecialCurveOverlap.affineCoeffMap]
  change
    Ideal.span
        {N13SpecialCurveOverlap.xOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.1,
          N13SpecialCurveOverlap.affineToInfinityOverlap
              N13SpecialCurveOverlap.yClass -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.2} =
      _
  rw [N13SpecialCurveOverlap.affineToInfinityOverlap_yClass]
  rfl

/-- Extension of an infinity-chart point ideal to the overlap has the
expected coordinate generators. -/
theorem map_infinityPointIdeal (t v : K) :
    Ideal.map
        (algebraMap SpecialInfinity SpecialOverlap)
        (infinityPointIdeal t v) =
      Ideal.span
        {N13SpecialCurveOverlap.tOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap t,
          N13SpecialCurveOverlap.vOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap v} := by
  simp [infinityPointIdeal, Ideal.map_span, Set.image_pair,
    N13SpecialCurveOverlap.tOverlap,
    N13SpecialCurveOverlap.vOverlap,
    N13SpecialCurveOverlap.coefficientToInfinityOverlap]

/-- On the overlap, the point ideals written in the coordinates
`x=t⁻¹` and `y=x³v` agree at `x=t=1`.

The first generators differ by the units `x` and `t`.  Once those generators
are identified, the difference between the second generators is a multiple
of `x³-1` or `t³-1`, respectively. -/
theorem overlap_unitPointIdeal
    (c : SpecialOverlap) :
    Ideal.span
        {N13SpecialCurveOverlap.xOverlap - 1,
          N13SpecialCurveOverlap.xOverlap ^ 3 *
              N13SpecialCurveOverlap.vOverlap - c} =
      Ideal.span
        {N13SpecialCurveOverlap.tOverlap - 1,
          N13SpecialCurveOverlap.vOverlap - c} := by
  let x := N13SpecialCurveOverlap.xOverlap
  let t := N13SpecialCurveOverlap.tOverlap
  let v := N13SpecialCurveOverlap.vOverlap
  let I : Ideal SpecialOverlap :=
    Ideal.span {x - 1, x ^ 3 * v - c}
  let J : Ideal SpecialOverlap :=
    Ideal.span {t - 1, v - c}
  change I = J
  have htx : t * x = 1 :=
    N13SpecialCurveOverlap.tOverlap_mul_xOverlap
  have hxI : x - 1 ∈ I :=
    Ideal.subset_span (by simp)
  have hxyI : x ^ 3 * v - c ∈ I :=
    Ideal.subset_span (by simp)
  have htJ : t - 1 ∈ J :=
    Ideal.subset_span (by simp)
  have hvJ : v - c ∈ J :=
    Ideal.subset_span (by simp)
  have hxJ : x - 1 ∈ J := by
    have hmem := Ideal.mul_mem_left J (-x) htJ
    convert hmem using 1
    linear_combination htx
  have hx3J : x ^ 3 - 1 ∈ J := by
    have hmem :=
      Ideal.mul_mem_left J (x ^ 2 + x + 1) hxJ
    convert hmem using 1
    ring
  have hxyJ : x ^ 3 * v - c ∈ J := by
    have h₁ := Ideal.mul_mem_left J (x ^ 3) hvJ
    have h₂ := Ideal.mul_mem_left J c hx3J
    have hmem := Ideal.add_mem J h₁ h₂
    convert hmem using 1
    ring
  have htI : t - 1 ∈ I := by
    have hmem := Ideal.mul_mem_left I (-t) hxI
    convert hmem using 1
    linear_combination htx
  have ht3I : t ^ 3 - 1 ∈ I := by
    have hmem :=
      Ideal.mul_mem_left I (t ^ 2 + t + 1) htI
    convert hmem using 1
    ring
  have hvI : v - c ∈ I := by
    have h₁ := Ideal.mul_mem_left I (t ^ 3) hxyI
    have h₂ := Ideal.mul_mem_left I c ht3I
    have hmem := Ideal.add_mem I h₁ h₂
    have htx3 : t ^ 3 * x ^ 3 = 1 := by
      calc
        t ^ 3 * x ^ 3 = (t * x) ^ 3 := by ring
        _ = 1 := by rw [htx, one_pow]
    have heq :
        t ^ 3 * (x ^ 3 * v - c) + c * (t ^ 3 - 1) =
          v - c := by
      calc
        _ = (t ^ 3 * x ^ 3) * v - c := by ring
        _ = v - c := by rw [htx3, one_mul]
    rw [heq] at hmem
    exact hmem
  apply le_antisymm
  · exact Ideal.span_le.mpr (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxJ
      · exact hxyJ)
  · exact Ideal.span_le.mpr (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact htI
      · exact hvI)

/-- A finite point with horizontal coordinate zero is absent from the
overlap, so its affine ideal extends to the unit ideal there. -/
def affineZeroPoint
    (P : AffinePoint)
    (hx : P.1.1 = 0) :
    ChartPair where
  affineIdeal := affinePointIdeal P
  infinityIdeal := ⊤
  overlap_eq := by
    rw [Ideal.map_top]
    apply
      (Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (affinePointIdeal P)).eq_top_of_isUnit_mem
    · apply Ideal.mem_map_of_mem
      exact
        N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
          (X - C P.1.1) (C P.1.2)
    · simpa [hx, N13GoodCoordinateRingTwo.xClass,
        N13GoodCoordinateRingTwo.mk,
        N13SpecialCurveOverlap.affineCoeffMap] using
        N13SpecialCurveOverlap.xOverlap_isUnit

/-- A finite point with horizontal coordinate one is represented on both
charts by the same point after the change of coordinates. -/
def affineOnePoint
    (P : AffinePoint)
    (hx : P.1.1 = 1) :
    ChartPair where
  affineIdeal := affinePointIdeal P
  infinityIdeal := infinityPointIdeal 1 P.1.2
  overlap_eq := by
    rw [map_affinePointIdeal, map_infinityPointIdeal, hx]
    simpa using
      overlap_unitPointIdeal
        (N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.2)

/-- An infinity point is absent from the ordinary affine chart.  Its
infinity ideal contains `t`, which becomes a unit on the overlap. -/
def infinityPoint (P : InfinityPoint) : ChartPair where
  affineIdeal := ⊤
  infinityIdeal := infinityPointIdeal 0 P.1
  overlap_eq := by
    rw [Ideal.map_top]
    symm
    apply
      (Ideal.map
        (algebraMap SpecialInfinity SpecialOverlap)
        (infinityPointIdeal 0 P.1)).eq_top_of_isUnit_mem
    · apply Ideal.mem_map_of_mem
      have ht :
          N13SpecialInfinityChart.tClass -
              algebraMap K[X] SpecialInfinity (C 0) ∈
            infinityPointIdeal 0 P.1 :=
        Ideal.subset_span (by simp)
      simpa using ht
    · simpa [N13SpecialCurveOverlap.tOverlap] using
        (IsLocalization.Away.algebraMap_isUnit
          N13SpecialInfinityChart.tClass :
          IsUnit N13SpecialCurveOverlap.tOverlap)

/-- Canonical compatible chart ideals of one completed special point. -/
def point (P : CurvePoint) : ChartPair :=
  match P with
  | Sum.inl P =>
      if hx : P.1.1 = 0 then
        affineZeroPoint P hx
      else
        affineOnePoint P
          ((N13GoodModelTwo.fixedTwo_eq_zero_or_one
            P.1.1 (ZMod.pow_card P.1.1)).resolve_left hx)
  | Sum.inr P =>
      infinityPoint P

/-- Tensor product of two compatible chart pairs. -/
def tensor (L M : ChartPair) : ChartPair where
  affineIdeal := L.affineIdeal * M.affineIdeal
  infinityIdeal := L.infinityIdeal * M.infinityIdeal
  overlap_eq := by
    rw [Ideal.map_mul, Ideal.map_mul, L.overlap_eq, M.overlap_eq]

/-- Tensoring chart pairs is commutative. -/
theorem tensor_comm (L M : ChartPair) :
    tensor L M = tensor M L := by
  cases L
  cases M
  simp [tensor, mul_comm]

/-- Canonical chart ideals of an unordered effective divisor of degree two.
Commutativity of ideal multiplication is exactly the descent condition
through `Sym2`. -/
def ofDivisor : EffectiveDivisorTwo → ChartPair :=
  Sym2.lift
    ⟨fun P Q => tensor (point P) (point Q),
      fun P Q => tensor_comm (point P) (point Q)⟩

@[simp] theorem ofDivisor_mk (P Q : CurvePoint) :
    ofDivisor s(P, Q) =
      tensor (point P) (point Q) :=
  rfl

end

end MazurProof.N13SpecialDivisorCharts


