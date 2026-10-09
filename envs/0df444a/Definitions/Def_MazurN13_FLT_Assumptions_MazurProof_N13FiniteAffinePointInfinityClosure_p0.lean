-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffinePointInfinityClosure_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffinePointInfinityClosure_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:52:21.647594+00:00
-- url     : https://prove2.me/theorems/9f76d30a-6b77-46ae-8087-e9c479e77cbf
-- title:
--   FLT.Assumptions.MazurProof.N13FiniteAffinePointInfinityClosure source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FiniteAffinePointInfinityClosure

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FiniteAffinePointInfinityClosure
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EscapingPointSpecialRestriction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralAffinePointSpecialClass_p0

set_option autoImplicit false




/-!
# Infinity closure of finite affine N13 point lines

For an integral affine point `(a,b)`, the same section on the infinity chart
is cut out by the weighted equations

`1 - a t = 0` and `v - b t³ = 0`.

The first equation makes `t` invertible modulo the weighted ideal, with
inverse `a`.  Hence the ideal is already saturated with respect to `t`;
contracting its extension from the overlap introduces no extra component.
This identifies the abstract `infinityClosure` with the explicit weighted
point ideal and makes its special reduction computable.
-/

open Polynomial

namespace MazurProof.N13FiniteAffinePointInfinityClosure

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Integral affine points of the good two-adic model. -/
abbrev IntegralPoint : Type :=
  N13IntegralAffinePointSpread.IntegralPoint

/-- The ordinary infinity-chart coordinate ring. -/
abbrev InfinityCurve : Type :=
  N13FiniteAffineTwoChart.InfinityCurve

/-- The ordinary common overlap ring. -/
abbrev InfinityOverlap : Type :=
  N13FiniteAffineTwoChart.InfinityOverlap

/-- An ideal containing `1-t a` is already saturated with respect to powers
of `t`.

Indeed, if `tⁿz` belongs to the ideal, multiplication by `aⁿ` recovers `z`
modulo the ideal because `(ta)ⁿ=1` there. -/
theorem under_map_eq_of_one_sub_t_mul_mem
    (J : Ideal InfinityCurve)
    (a : InfinityCurve)
    (hunit :
      1 - N13IntegralInfinityChart.tClass * a ∈ J) :
    (Ideal.map
      (algebraMap InfinityCurve InfinityOverlap) J).under
        InfinityCurve =
      J := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap InfinityCurve InfinityOverlap z ∈
        Ideal.map (algebraMap InfinityCurve InfinityOverlap) J at hz
    obtain ⟨m, hm, hmz⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Submonoid.powers N13IntegralInfinityChart.tClass)
        InfinityOverlap J z).mp hz
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff
        m N13IntegralInfinityChart.tClass).mp hm
    rw [← hn] at hmz
    have hpow_all :
        ∀ k : ℕ,
          1 - (N13IntegralInfinityChart.tClass * a) ^ k ∈ J := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          have hmul :=
            Ideal.mul_mem_left J
              ((N13IntegralInfinityChart.tClass * a) ^ k)
              hunit
          have hadd := Ideal.add_mem J ih hmul
          convert hadd using 1
          ring
    have hpow :=
      hpow_all n
    have hmultiple :=
      Ideal.mul_mem_left J (a ^ n) hmz
    have hcorrection :=
      Ideal.mul_mem_left J z hpow
    have hadd := Ideal.add_mem J hmultiple hcorrection
    convert hadd using 1
    ring
  · exact Ideal.le_comap_map

/-- Weighted infinity-chart ideal of an integral affine point. -/
def weightedInfinityIdeal (P : IntegralPoint) : Ideal InfinityCurve :=
  Ideal.span
    {1 -
        N13IntegralInfinityReduction.integralBaseClass (C P.1.1) *
          N13IntegralInfinityChart.tClass,
      N13IntegralInfinityChart.vClass -
        N13IntegralInfinityReduction.integralBaseClass (C P.1.2) *
          N13IntegralInfinityChart.tClass ^ 3}

/-- Multiplying two generators by units does not change the ideal they
generate. -/
private theorem span_pair_unit_mul
    {A : Type*} [CommRing A]
    (u v : Aˣ) (a b : A) :
    Ideal.span ({(u : A) * a, (v : A) * b} : Set A) =
      Ideal.span ({a, b} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have hmem :
          ((u⁻¹ : Aˣ) : A) * ((u : A) * a) ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (by simp))
      simpa [mul_assoc] using hmem
    · rw [hz]
      have hmem :
          ((v⁻¹ : Aˣ) : A) * ((v : A) * b) ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (by simp))
      simpa [mul_assoc] using hmem

/-- The weighted infinity ideal and the affine point ideal have the same
extension to the ordinary overlap. -/
theorem map_weightedInfinityIdeal (P : IntegralPoint) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (weightedInfinityIdeal P) =
      Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13IntegralAffinePointSpread.pointIdeal P) := by
  simp [weightedInfinityIdeal,
    N13IntegralAffinePointSpread.pointIdeal,
    N13IntegralAffinePointSpread.integralSemiGraph,
    N13IntegralAffinePointSpread.pointU,
    N13IntegralAffinePointSpread.pointV,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.ySubClass,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityReduction.integralBaseClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.mk,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.affineCoeffMap,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap]
  change
    Ideal.span
        {1 -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
              N13OrdinaryCurveOverlap.tOverlap,
          N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3} =
      Ideal.span
        {N13OrdinaryCurveOverlap.xOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1,
          N13OrdinaryCurveOverlap.xOverlap ^ 3 *
              N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2}
  let ux : InfinityOverlapˣ :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit
  have hux :
      (ux : InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit_spec
  have hfirst :
      N13OrdinaryCurveOverlap.xOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 =
        (ux : InfinityOverlap) *
          (1 -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
              N13OrdinaryCurveOverlap.tOverlap) := by
    rw [hux]
    linear_combination
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  have hsecond :
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 =
        ((ux ^ 3 : InfinityOverlapˣ) : InfinityOverlap) *
          (N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3) := by
    change
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 =
        (ux : InfinityOverlap) ^ 3 *
          (N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3)
    rw [hux]
    linear_combination
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
        (N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        N13OrdinaryCurveOverlap.tOverlap ^ 2 +
        N13OrdinaryCurveOverlap.xOverlap *
          N13OrdinaryCurveOverlap.tOverlap +
        1) *
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  rw [hfirst, hsecond]
  exact
    (span_pair_unit_mul
      ux (ux ^ 3)
      (1 -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
          N13OrdinaryCurveOverlap.tOverlap)
      (N13OrdinaryCurveOverlap.vOverlap -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
          N13OrdinaryCurveOverlap.tOverlap ^ 3)).symm

/-- The horizontal weighted equation explicitly makes `t` invertible modulo
the weighted ideal. -/
theorem one_sub_t_mul_mem_weightedInfinityIdeal
    (P : IntegralPoint) :
    1 -
        N13IntegralInfinityChart.tClass *
          N13IntegralInfinityReduction.integralBaseClass (C P.1.1) ∈
      weightedInfinityIdeal P := by
  have hgen :
      1 -
          N13IntegralInfinityReduction.integralBaseClass (C P.1.1) *
            N13IntegralInfinityChart.tClass ∈
        weightedInfinityIdeal P :=
    Ideal.subset_span (by simp)
  simpa [mul_comm] using hgen

/-- The weighted point ideal has no additional component supported at
`t=0`; extending to the overlap and contracting returns it unchanged. -/
theorem under_map_weightedInfinityIdeal
    (P : IntegralPoint) :
    (Ideal.map
      (algebraMap InfinityCurve InfinityOverlap)
      (weightedInfinityIdeal P)).under InfinityCurve =
        weightedInfinityIdeal P :=
  under_map_eq_of_one_sub_t_mul_mem
    (weightedInfinityIdeal P)
    (N13IntegralInfinityReduction.integralBaseClass (C P.1.1))
    (one_sub_t_mul_mem_weightedInfinityIdeal P)

/-- The abstract contracted infinity closure of a finite affine point is
exactly its explicit weighted infinity ideal. -/
theorem infinityClosure_pointIdeal
    (P : IntegralPoint) :
    N13FiniteAffineTwoChart.infinityClosure
        (N13IntegralAffinePointSpread.pointIdeal P) =
      weightedInfinityIdeal P := by
  rw [N13FiniteAffineTwoChart.infinityClosure,
    ← map_weightedInfinityIdeal P]
  exact under_map_weightedInfinityIdeal P

/-- Literal coefficientwise reduction of the weighted infinity ideal. -/
def reducedWeightedInfinityIdeal
    (P : IntegralPoint) :
    Ideal N13IntegralInfinityReduction.SpecialRing :=
  Ideal.span
    {1 -
        N13IntegralInfinityReduction.specialBaseClass
            (C (N13GeneralizedMumfordReduction.reduceBase P.1.1)) *
          N13SpecialInfinityChart.tClass,
      N13SpecialInfinityChart.vClass -
        N13IntegralInfinityReduction.specialBaseClass
            (C (N13GeneralizedMumfordReduction.reduceBase P.1.2)) *
          N13SpecialInfinityChart.tClass ^ 3}

/-- Reduction of the integral weighted ideal is exactly the weighted ideal
with reduced coordinates. -/
theorem map_weightedInfinityIdeal_reduce
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (weightedInfinityIdeal P) =
      reducedWeightedInfinityIdeal P := by
  simp [weightedInfinityIdeal, reducedWeightedInfinityIdeal,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityReduction.reduce_integralBaseClass,
    N13IntegralInfinityReduction.reducePoly,
    N13IntegralInfinityReduction.reduceBase,
    N13IntegralInfinityReduction.specialBaseClass]

/-- At the unit horizontal coordinate, the weighted point equations
`(1-t, v-bt³)` generate the same ideal as the ordinary point equations
`(t-1, v-b)`. -/
theorem reducedWeightedUnit_eq_infinityPointIdeal
    (b : N13GoodModelTwo.F2) :
    Ideal.span
        {1 - N13SpecialInfinityChart.tClass,
          N13SpecialInfinityChart.vClass -
            N13IntegralInfinityReduction.specialBaseClass (C b) *
              N13SpecialInfinityChart.tClass ^ 3} =
      N13SpecialDivisorCharts.infinityPointIdeal 1 b := by
  let t := N13SpecialInfinityChart.tClass
  let v := N13SpecialInfinityChart.vClass
  let c :=
    N13IntegralInfinityReduction.specialBaseClass (C b)
  let I : Ideal N13IntegralInfinityReduction.SpecialRing :=
    Ideal.span {1 - t, v - c * t ^ 3}
  let J : Ideal N13IntegralInfinityReduction.SpecialRing :=
    Ideal.span {t - 1, v - c}
  change I = J
  have honeI : 1 - t ∈ I :=
    Ideal.subset_span (by simp)
  have hvI : v - c * t ^ 3 ∈ I :=
    Ideal.subset_span (by simp)
  have htJ : t - 1 ∈ J :=
    Ideal.subset_span (by simp)
  have hvJ : v - c ∈ J :=
    Ideal.subset_span (by simp)
  have htI : t - 1 ∈ I := by
    have hmem := Ideal.mul_mem_left I (-1) honeI
    convert hmem using 1
    ring
  have honeJ : 1 - t ∈ J := by
    have hmem := Ideal.mul_mem_left J (-1) htJ
    convert hmem using 1
    ring
  have ht3I : t ^ 3 - 1 ∈ I := by
    have hmem :=
      Ideal.mul_mem_left I (t ^ 2 + t + 1) htI
    convert hmem using 1
    ring
  have hone3J : 1 - t ^ 3 ∈ J := by
    have hmem :=
      Ideal.mul_mem_left J (t ^ 2 + t + 1) honeJ
    convert hmem using 1
    ring
  have hvPlainI : v - c ∈ I := by
    have h₁ := hvI
    have h₂ := Ideal.mul_mem_left I c ht3I
    have hmem := Ideal.add_mem I h₁ h₂
    convert hmem using 1
    ring
  have hvWeightedJ : v - c * t ^ 3 ∈ J := by
    have h₁ := hvJ
    have h₂ := Ideal.mul_mem_left J c hone3J
    have hmem := Ideal.add_mem J h₁ h₂
    convert hmem using 1
    ring
  have hIJ : I = J := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact honeJ
        · exact hvWeightedJ)
    · exact Ideal.span_le.mpr (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact htI
        · exact hvPlainI)
  rw [hIJ]

/-- If the affine horizontal coordinate reduces to zero, the weighted
infinity ideal reduces to the unit ideal, as the point is absent from that
chart. -/
theorem reducedWeightedInfinityIdeal_eq_top
    (P : IntegralPoint)
    (ha :
      N13GeneralizedMumfordReduction.reduceBase P.1.1 = 0) :
    reducedWeightedInfinityIdeal P = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hgen :
      1 -
          N13IntegralInfinityReduction.specialBaseClass
              (C (N13GeneralizedMumfordReduction.reduceBase P.1.1)) *
            N13SpecialInfinityChart.tClass ∈
        reducedWeightedInfinityIdeal P :=
    Ideal.subset_span (by simp)
  simpa [ha, N13IntegralInfinityReduction.specialBaseClass] using hgen

/-- The infinity component of an integral affine point line reduces exactly
to the canonical infinity-chart ideal of its reduced special point. -/
theorem map_infinityClosure_pointIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.infinityClosure
          (N13IntegralAffinePointSpread.pointIdeal P)) =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal := by
  rw [infinityClosure_pointIdeal, map_weightedInfinityIdeal_reduce]
  let a :=
    N13GeneralizedMumfordReduction.reduceBase P.1.1
  let b :=
    N13GeneralizedMumfordReduction.reduceBase P.1.2
  have ha : a = 0 ∨ a = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one
      a (ZMod.pow_card a)
  rcases ha with ha | ha
  · rw [reducedWeightedInfinityIdeal_eq_top P ha]
    have ha0 :
        PadicInt.toZMod P.1.1 = 0 := by
      exact ha
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineZeroPoint, ha0]
  · have hweighted :
        reducedWeightedInfinityIdeal P =
          N13SpecialDivisorCharts.infinityPointIdeal 1 b := by
      simpa [reducedWeightedInfinityIdeal, a, b, ha,
        N13IntegralInfinityReduction.specialBaseClass] using
        reducedWeightedUnit_eq_infinityPointIdeal b
    rw [hweighted]
    have hb :
        b = PadicInt.toZMod P.1.2 := by
      rfl
    rw [hb]
    have ha1 :
        PadicInt.toZMod P.1.1 = 1 := by
      exact ha
    have ha0 :
        PadicInt.toZMod P.1.1 ≠ 0 := by
      rw [ha1]
      norm_num
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineOnePoint, ha0]

/-- The affine component of the integral point line reduces to the canonical
affine ideal of the same reduced point. -/
theorem restrict_integralPointTwoChartLine_affineIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).affineIdeal := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      _
  rw [
    N13IntegralAffinePointSpecialClass.map_integralPointTwoChartLine_affineIdeal]
  let a :=
    N13GeneralizedMumfordReduction.reduceBase P.1.1
  have ha : a = 0 ∨ a = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one
      a (ZMod.pow_card a)
  rcases ha with ha | ha
  · have ha0 :
        PadicInt.toZMod P.1.1 = 0 := by
      exact ha
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13IntegralAffinePointSpecialClass.reducedPointIdeal,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineZeroPoint,
      N13SpecialDivisorCharts.affinePointIdeal, ha0]
  · have ha1 :
        PadicInt.toZMod P.1.1 = 1 := by
      exact ha
    have ha0 :
        PadicInt.toZMod P.1.1 ≠ 0 := by
      rw [ha1]
      norm_num
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13IntegralAffinePointSpecialClass.reducedPointIdeal,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineOnePoint,
      N13SpecialDivisorCharts.affinePointIdeal, ha0]

/-- The infinity component of the integral point line reduces to the
canonical infinity ideal of the same reduced point. -/
theorem restrict_integralPointTwoChartLine_infinityIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.infinityClosure
          (N13IntegralAffinePointSpread.pointIdeal P)) =
      _
  exact map_infinityClosure_pointIdeal P

/-- Degree-two normalization of an integral affine point line by adjoining
the positive-infinity anchor once. -/
def anchoredPointLine
    (P : IntegralPoint) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  N13TwoChartLineTensor.withPositiveInfinityMultiplicity
    (N13FiniteAffineTwoChart.integralPointTwoChartLine P)
    1

/-- The affine restriction of the anchored integral point line is exactly
the affine chart ideal of its literal anchored special divisor. -/
theorem restrict_anchoredPointLine_affineIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine P)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13IntegralAffinePointSpecialClass.anchoredReducedDivisor P)).affineIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
    N13IntegralAffinePointSpecialClass.anchoredReducedDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).affineIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).affineIdeal =
      (N13SpecialDivisorCharts.point
          (N13IntegralAffinePointSpecialClass.reducedPoint P)).affineIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).affineIdeal
  rw [restrict_integralPointTwoChartLine_affineIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_affineIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]

/-- The infinity restriction of the anchored integral point line is exactly
the infinity chart ideal of the same literal anchored special divisor. -/
theorem restrict_anchoredPointLine_infinityIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine P)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13IntegralAffinePointSpecialClass.anchoredReducedDivisor P)).infinityIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
    N13IntegralAffinePointSpecialClass.anchoredReducedDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).infinityIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).infinityIdeal =
      (N13SpecialDivisorCharts.point
          (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).infinityIdeal
  rw [restrict_integralPointTwoChartLine_infinityIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_infinityIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]

end

end MazurProof.N13FiniteAffinePointInfinityClosure


