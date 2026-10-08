-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryCompletionCompatibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryCompletionCompatibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:48:36.901986+00:00
-- url     : https://prove2.me/theorems/637f2909-fa83-4c26-8184-94832b4cee76
-- title:
--   FLT.Assumptions.MazurProof.N13OrdinaryCompletionCompatibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13OrdinaryCompletionCompatibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13OrdinaryCompletionCompatibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryCurveOverlap_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinityChart_p0

set_option autoImplicit false




/-!
# Compatibility of the ordinary and formal N13 overlaps

The ordinary infinity overlap is obtained by inverting `t`.  Composing the
ordinary infinity chart with its completion and the formal restriction sends
`t` to a Laurent unit, so the universal property of `Localization.Away`
gives a canonical map to the formal overlap.

This file proves that the resulting map agrees with both ordinary chart
restrictions.  No flatness, injectivity of completion, or algebraization
theorem is used.
-/

namespace MazurProof.N13OrdinaryCompletionCompatibility

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev OrdinaryInfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev OrdinaryOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap

abbrev FormalInfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve

abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve

abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent

/-- Restrict an ordinary infinity-chart function to the punctured formal
overlap. -/
def infinityToFormalCurve :
    OrdinaryInfinityCurve →+* FormalCurve :=
  N13FormalInfinityChart.infinityToFormalCurve.comp
    N13IntegralInfinityChart.toFormalInfinity

@[simp] theorem toFormalInfinity_of
    (p : N13IntegralInfinityChart.Base) :
    N13IntegralInfinityChart.toFormalInfinity
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) =
      algebraMap
        N13IntegralInfinityChart.Power
        FormalInfinityCurve
        (N13IntegralInfinityChart.baseToPower p) := by
  exact
    AdjoinRoot.lift_of
      N13IntegralInfinityChart.formal_v_relation

@[simp] theorem infinityToFormalCurve_tClass :
    infinityToFormalCurve N13IntegralInfinityChart.tClass =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.tPow 1) := by
  rw [infinityToFormalCurve, RingHom.comp_apply,
    N13IntegralInfinityChart.toFormalInfinity_tClass,
    N13FormalInfinityChart.infinityToFormalCurve_of,
    N13FormalInfinityChart.includePowerRing_X]

@[simp] theorem infinityToFormalCurve_coefficient
    (r : R₂) :
    infinityToFormalCurve
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly
          (Polynomial.C r)) =
      algebraMap Laurent FormalCurve
        (algebraMap R₂ Laurent r) := by
  rw [infinityToFormalCurve, RingHom.comp_apply,
    toFormalInfinity_of,
    N13FormalInfinityChart.infinityToFormalCurve_of]
  simp [N13IntegralInfinityChart.baseToPower,
    N13FormalInfinityChart.includePowerRing]
  congr 1
  rw [HahnSeries.algebraMap_apply',
    ← PowerSeries.C_eq_algebraMap,
    HahnSeries.ofPowerSeries_C]
  rfl

@[simp] theorem infinityToFormalCurve_vClass :
    infinityToFormalCurve N13IntegralInfinityChart.vClass =
      N13FormalCurveOverlap.vClass := by
  simp [infinityToFormalCurve]

/-- Laurent monomials are units, with inverse exponent. -/
private def tPowUnit (n : ℤ) : Laurentˣ where
  val := N13FormalCurveOverlap.tPow n
  inv := N13FormalCurveOverlap.tPow (-n)
  val_inv := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp
  inv_val := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp

private theorem infinity_tClass_isUnit :
    IsUnit
      (infinityToFormalCurve
        N13IntegralInfinityChart.tClass) := by
  rw [infinityToFormalCurve_tClass]
  exact
    (tPowUnit 1).isUnit.map
      (algebraMap Laurent FormalCurve)

/-- Completion of the ordinary principal open to the punctured formal
overlap. -/
def ordinaryToFormalCurve :
    OrdinaryOverlap →+* FormalCurve :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    infinity_tClass_isUnit

/-- The completion map restricts to the prescribed infinity-chart map. -/
@[simp] theorem ordinaryToFormalCurve_comp_infinity :
    ordinaryToFormalCurve.comp
        (algebraMap OrdinaryInfinityCurve OrdinaryOverlap) =
      infinityToFormalCurve := by
  exact
    IsLocalization.Away.lift_comp
      N13IntegralInfinityChart.tClass
      infinity_tClass_isUnit

@[simp] theorem ordinaryToFormalCurve_algebraMap
    (z : OrdinaryInfinityCurve) :
    ordinaryToFormalCurve
        (algebraMap OrdinaryInfinityCurve OrdinaryOverlap z) =
      infinityToFormalCurve z :=
  DFunLike.congr_fun ordinaryToFormalCurve_comp_infinity z

@[simp] theorem ordinaryToFormalCurve_tOverlap :
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.tOverlap =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.tPow 1) := by
  rw [N13OrdinaryCurveOverlap.tOverlap,
    ordinaryToFormalCurve_algebraMap,
    infinityToFormalCurve_tClass]

@[simp] theorem ordinaryToFormalCurve_vOverlap :
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.vOverlap =
      N13FormalCurveOverlap.vClass := by
  rw [N13OrdinaryCurveOverlap.vOverlap,
    ordinaryToFormalCurve_algebraMap,
    infinityToFormalCurve_vClass]

/-- The distinguished ordinary inverse maps to the Laurent monomial
`t⁻¹`. -/
@[simp] theorem ordinaryToFormalCurve_xOverlap :
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.xOverlap =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.tPow (-1)) := by
  have hmul :
      infinityToFormalCurve N13IntegralInfinityChart.tClass *
          ordinaryToFormalCurve
            N13OrdinaryCurveOverlap.xOverlap = 1 := by
    calc
      infinityToFormalCurve N13IntegralInfinityChart.tClass *
            ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.xOverlap =
          ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.tOverlap *
            ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.xOverlap := by
                rw [ordinaryToFormalCurve_tOverlap,
                  infinityToFormalCurve_tClass]
      _ =
          ordinaryToFormalCurve
            (N13OrdinaryCurveOverlap.tOverlap *
              N13OrdinaryCurveOverlap.xOverlap) := by
                rw [map_mul]
      _ = 1 := by
        rw [N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap,
          map_one]
  calc
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.xOverlap =
        1 *
          ordinaryToFormalCurve
            N13OrdinaryCurveOverlap.xOverlap := by simp
    _ =
        (algebraMap Laurent FormalCurve
            (N13FormalCurveOverlap.tPow (-1)) *
          algebraMap Laurent FormalCurve
            (N13FormalCurveOverlap.tPow 1)) *
          ordinaryToFormalCurve
            N13OrdinaryCurveOverlap.xOverlap := by
              rw [← map_mul,
                N13FormalCurveOverlap.tPow_mul]
              norm_num
    _ =
        algebraMap Laurent FormalCurve
            (N13FormalCurveOverlap.tPow (-1)) *
          (infinityToFormalCurve
              N13IntegralInfinityChart.tClass *
            ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.xOverlap) := by
                rw [infinityToFormalCurve_tClass, mul_assoc]
    _ =
        algebraMap Laurent FormalCurve
          (N13FormalCurveOverlap.tPow (-1)) := by
            rw [hmul, mul_one]

/-- The formal affine map on the coefficient presentation. -/
@[simp] theorem affineToFormalCurve_of (p : Polynomial R₂) :
    N13FormalCurveOverlap.affineToFormalCurve
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)) p) =
      N13FormalCurveOverlap.affineCoeffMap p := by
  exact
    AdjoinRoot.lift_of
      N13FormalCurveOverlap.affineCurve_relation

/-- Completion agrees on constants of the affine presentation. -/
theorem ordinaryToFormalCurve_affine_coefficient
    (r : R₂) :
    ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap
          (AdjoinRoot.of
            (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
            (Polynomial.C r))) =
      N13FormalCurveOverlap.affineToFormalCurve
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
          (Polynomial.C r)) := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_of,
    affineToFormalCurve_of]
  simp [N13OrdinaryCurveOverlap.affineCoeffMap,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap,
    N13FormalCurveOverlap.affineCoeffMap,
    N13FormalCurveOverlap.polyAtTInv]

/-- Completion agrees on the affine coordinate `x`. -/
theorem ordinaryToFormalCurve_affine_x :
    ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap
          N13OrdinaryCurveOverlap.xClass) =
      N13FormalCurveOverlap.affineToFormalCurve
        N13OrdinaryCurveOverlap.xClass := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClass]
  change
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.xOverlap =
      N13FormalCurveOverlap.affineToFormalCurve
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) Polynomial.X)
  rw [ordinaryToFormalCurve_xOverlap,
    N13FormalCurveOverlap.affineToFormalCurve_xClass]
  simp [N13FormalCurveOverlap.polyAtTInv]

/-- Completion agrees on the affine coordinate `y`. -/
theorem ordinaryToFormalCurve_affine_y :
    ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap
          N13OrdinaryCurveOverlap.yClass) =
      N13FormalCurveOverlap.affineToFormalCurve
        N13OrdinaryCurveOverlap.yClass := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_yClass]
  change
      ordinaryToFormalCurve
          N13OrdinaryCurveOverlap.affineYImage =
        N13FormalCurveOverlap.affineToFormalCurve
          (N13GeneralizedMumfordIntegral.yClass (R := R₂))
  rw [N13FormalCurveOverlap.affineToFormalCurve_yClass]
  simp only [N13OrdinaryCurveOverlap.affineYImage,
    map_mul, map_pow, ordinaryToFormalCurve_xOverlap,
    ordinaryToFormalCurve_vOverlap,
    N13FormalCurveOverlap.yImage]
  rw [← map_pow]
  congr 1
  simp [N13FormalCurveOverlap.tPow, HahnSeries.single_pow]

/-- Completion is compatible with the ordinary affine restriction. -/
theorem ordinaryToFormalCurve_comp_affine :
    ordinaryToFormalCurve.comp
        N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      N13FormalCurveOverlap.affineToFormalCurve := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · exact ordinaryToFormalCurve_affine_coefficient
    · exact ordinaryToFormalCurve_affine_x
  · exact ordinaryToFormalCurve_affine_y

end

end MazurProof.N13OrdinaryCompletionCompatibility


