-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OverlapReductionCompatibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13OverlapReductionCompatibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:49:49.887324+00:00
-- url     : https://prove2.me/theorems/05b0ba01-4d99-49c3-bc5f-ad0980c0dfd9
-- title:
--   FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13OverlapReductionCompatibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryCurveOverlap_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCurveOverlap_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0

set_option autoImplicit false




/-!
# Reduction commutes with the N13 two-chart overlap

The ordinary affine and infinity reductions extend to their distinguished
principal opens.  The two resulting squares commute with the ordinary and
special overlap equivalences.

Everything is proved from localization and `AdjoinRoot` universal
properties.  No pointwise calculation on either special chart is used.
-/

open Polynomial

namespace MazurProof.N13OverlapReductionCompatibility

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev OrdinaryAffine :=
  N13OrdinaryCurveOverlap.AffineCurve

private abbrev OrdinaryInfinity :=
  N13OrdinaryCurveOverlap.InfinityCurve

private abbrev OrdinaryAffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap

private abbrev OrdinaryInfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap

private abbrev SpecialAffine :=
  N13SpecialCurveOverlap.AffineCurve

private abbrev SpecialInfinity :=
  N13SpecialCurveOverlap.CoordinateRing

private abbrev SpecialAffineOverlap :=
  N13SpecialCurveOverlap.AffineOverlap

private abbrev SpecialInfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap

/-- Affine reduction followed by restriction to the special principal
open. -/
private def affineReduceToOverlap :
    OrdinaryAffine →+* SpecialAffineOverlap :=
  (algebraMap SpecialAffine SpecialAffineOverlap).comp
    N13GeneralizedMumfordReduction.reduceCoordinate

@[simp] private theorem affineReduceToOverlap_x :
    affineReduceToOverlap N13OrdinaryCurveOverlap.xClass =
      algebraMap SpecialAffine SpecialAffineOverlap
        N13SpecialCurveOverlap.xClass := by
  simp [affineReduceToOverlap,
    N13OrdinaryCurveOverlap.xClass,
    N13SpecialCurveOverlap.xClass,
    RingHom.comp_apply,
    N13GeneralizedMumfordReduction.reducePoly]

@[simp] private theorem affineReduceToOverlap_y :
    affineReduceToOverlap N13OrdinaryCurveOverlap.yClass =
      algebraMap SpecialAffine SpecialAffineOverlap
        N13SpecialCurveOverlap.yClass := by
  simp [affineReduceToOverlap,
    N13OrdinaryCurveOverlap.yClass,
    N13SpecialCurveOverlap.yClass,
    RingHom.comp_apply]

private theorem affine_x_mapsToUnit :
    IsUnit
      (affineReduceToOverlap
        N13OrdinaryCurveOverlap.xClass) := by
  rw [affineReduceToOverlap_x]
  exact
    IsLocalization.Away.algebraMap_isUnit
      N13SpecialCurveOverlap.xClass

/-- Reduction on the affine distinguished principal open. -/
def reduceAffineOverlap :
    OrdinaryAffineOverlap →+* SpecialAffineOverlap :=
  IsLocalization.Away.lift
    N13OrdinaryCurveOverlap.xClass
    affine_x_mapsToUnit

@[simp] theorem reduceAffineOverlap_algebraMap
    (z : OrdinaryAffine) :
    reduceAffineOverlap
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap z) =
      affineReduceToOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13OrdinaryCurveOverlap.xClass
      affine_x_mapsToUnit z

/-- Restriction to the affine principal open commutes with reduction. -/
theorem reduceAffineOverlap_comp_algebraMap :
    reduceAffineOverlap.comp
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap) =
      (algebraMap SpecialAffine SpecialAffineOverlap).comp
        N13GeneralizedMumfordReduction.reduceCoordinate := by
  apply RingHom.ext
  intro z
  change
    reduceAffineOverlap
        (algebraMap OrdinaryAffine OrdinaryAffineOverlap z) =
      algebraMap SpecialAffine SpecialAffineOverlap
        (N13GeneralizedMumfordReduction.reduceCoordinate z)
  rw [reduceAffineOverlap_algebraMap]
  rfl

@[simp] theorem reduceAffineOverlap_x :
    reduceAffineOverlap
        N13OrdinaryCurveOverlap.xAffineOverlap =
      N13SpecialCurveOverlap.xAffineOverlap := by
  rw [N13OrdinaryCurveOverlap.xAffineOverlap,
    reduceAffineOverlap_algebraMap,
    affineReduceToOverlap_x]
  rfl

@[simp] theorem reduceAffineOverlap_y :
    reduceAffineOverlap
        N13OrdinaryCurveOverlap.yAffineOverlap =
      N13SpecialCurveOverlap.yAffineOverlap := by
  rw [N13OrdinaryCurveOverlap.yAffineOverlap,
    reduceAffineOverlap_algebraMap,
    affineReduceToOverlap_y]
  rfl

@[simp] theorem reduceAffineOverlap_t :
    reduceAffineOverlap
        N13OrdinaryCurveOverlap.tAffineOverlap =
      N13SpecialCurveOverlap.tAffineOverlap := by
  have hinv :
      N13SpecialCurveOverlap.xAffineOverlap *
          reduceAffineOverlap
            N13OrdinaryCurveOverlap.tAffineOverlap = 1 := by
    calc
      N13SpecialCurveOverlap.xAffineOverlap *
            reduceAffineOverlap
              N13OrdinaryCurveOverlap.tAffineOverlap =
          reduceAffineOverlap
              N13OrdinaryCurveOverlap.xAffineOverlap *
            reduceAffineOverlap
              N13OrdinaryCurveOverlap.tAffineOverlap := by
                rw [reduceAffineOverlap_x]
      _ = reduceAffineOverlap
          (N13OrdinaryCurveOverlap.xAffineOverlap *
            N13OrdinaryCurveOverlap.tAffineOverlap) := by
              rw [map_mul]
      _ = 1 := by
            rw [N13OrdinaryCurveOverlap.xAffineOverlap_mul_tAffineOverlap,
              map_one]
  calc
    reduceAffineOverlap
        N13OrdinaryCurveOverlap.tAffineOverlap =
      1 * reduceAffineOverlap
        N13OrdinaryCurveOverlap.tAffineOverlap := by simp
    _ =
      (N13SpecialCurveOverlap.tAffineOverlap *
          N13SpecialCurveOverlap.xAffineOverlap) *
        reduceAffineOverlap
          N13OrdinaryCurveOverlap.tAffineOverlap := by
            rw [show
              N13SpecialCurveOverlap.tAffineOverlap *
                    N13SpecialCurveOverlap.xAffineOverlap = 1 by
                simpa [mul_comm] using
                  N13SpecialCurveOverlap.xAffineOverlap_mul_tAffineOverlap]
    _ =
      N13SpecialCurveOverlap.tAffineOverlap *
        (N13SpecialCurveOverlap.xAffineOverlap *
          reduceAffineOverlap
            N13OrdinaryCurveOverlap.tAffineOverlap) := by
              rw [mul_assoc]
    _ = N13SpecialCurveOverlap.tAffineOverlap := by
          rw [hinv, mul_one]

/-- Infinity reduction followed by restriction to the special principal
open. -/
private def infinityReduceToOverlap :
    OrdinaryInfinity →+* SpecialInfinityOverlap :=
  (algebraMap SpecialInfinity SpecialInfinityOverlap).comp
    N13IntegralInfinityReduction.reduceCoordinate

@[simp] private theorem infinityReduceToOverlap_t :
    infinityReduceToOverlap
        N13IntegralInfinityChart.tClass =
      algebraMap SpecialInfinity SpecialInfinityOverlap
        N13SpecialInfinityChart.tClass := by
  simp [infinityReduceToOverlap, RingHom.comp_apply]

@[simp] private theorem infinityReduceToOverlap_v :
    infinityReduceToOverlap
        N13IntegralInfinityChart.vClass =
      algebraMap SpecialInfinity SpecialInfinityOverlap
        N13SpecialInfinityChart.vClass := by
  simp [infinityReduceToOverlap, RingHom.comp_apply]

private theorem infinity_t_mapsToUnit :
    IsUnit
      (infinityReduceToOverlap
        N13IntegralInfinityChart.tClass) := by
  rw [infinityReduceToOverlap_t]
  exact
    IsLocalization.Away.algebraMap_isUnit
      N13SpecialInfinityChart.tClass

/-- Reduction on the infinity distinguished principal open. -/
def reduceInfinityOverlap :
    OrdinaryInfinityOverlap →+* SpecialInfinityOverlap :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    infinity_t_mapsToUnit

@[simp] theorem reduceInfinityOverlap_algebraMap
    (z : OrdinaryInfinity) :
    reduceInfinityOverlap
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap z) =
      infinityReduceToOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13IntegralInfinityChart.tClass
      infinity_t_mapsToUnit z

/-- Restriction to the infinity principal open commutes with reduction. -/
theorem reduceInfinityOverlap_comp_algebraMap :
    reduceInfinityOverlap.comp
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap) =
      (algebraMap SpecialInfinity SpecialInfinityOverlap).comp
        N13IntegralInfinityReduction.reduceCoordinate := by
  apply RingHom.ext
  intro z
  change
    reduceInfinityOverlap
        (algebraMap OrdinaryInfinity OrdinaryInfinityOverlap z) =
      algebraMap SpecialInfinity SpecialInfinityOverlap
        (N13IntegralInfinityReduction.reduceCoordinate z)
  rw [reduceInfinityOverlap_algebraMap]
  rfl

@[simp] theorem reduceInfinityOverlap_t :
    reduceInfinityOverlap
        N13OrdinaryCurveOverlap.tOverlap =
      N13SpecialCurveOverlap.tOverlap := by
  rw [N13OrdinaryCurveOverlap.tOverlap,
    reduceInfinityOverlap_algebraMap,
    infinityReduceToOverlap_t]
  rfl

@[simp] theorem reduceInfinityOverlap_v :
    reduceInfinityOverlap
        N13OrdinaryCurveOverlap.vOverlap =
      N13SpecialCurveOverlap.vOverlap := by
  rw [N13OrdinaryCurveOverlap.vOverlap,
    reduceInfinityOverlap_algebraMap,
    infinityReduceToOverlap_v]
  rfl

@[simp] theorem reduceInfinityOverlap_x :
    reduceInfinityOverlap
        N13OrdinaryCurveOverlap.xOverlap =
      N13SpecialCurveOverlap.xOverlap := by
  have hinv :
      N13SpecialCurveOverlap.tOverlap *
          reduceInfinityOverlap
            N13OrdinaryCurveOverlap.xOverlap = 1 := by
    calc
      N13SpecialCurveOverlap.tOverlap *
            reduceInfinityOverlap
              N13OrdinaryCurveOverlap.xOverlap =
          reduceInfinityOverlap
              N13OrdinaryCurveOverlap.tOverlap *
            reduceInfinityOverlap
              N13OrdinaryCurveOverlap.xOverlap := by
                rw [reduceInfinityOverlap_t]
      _ = reduceInfinityOverlap
          (N13OrdinaryCurveOverlap.tOverlap *
            N13OrdinaryCurveOverlap.xOverlap) := by
              rw [map_mul]
      _ = 1 := by
            rw [N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap,
              map_one]
  calc
    reduceInfinityOverlap
        N13OrdinaryCurveOverlap.xOverlap =
      1 * reduceInfinityOverlap
        N13OrdinaryCurveOverlap.xOverlap := by simp
    _ =
      (N13SpecialCurveOverlap.xOverlap *
          N13SpecialCurveOverlap.tOverlap) *
        reduceInfinityOverlap
          N13OrdinaryCurveOverlap.xOverlap := by
            rw [show
              N13SpecialCurveOverlap.xOverlap *
                    N13SpecialCurveOverlap.tOverlap = 1 by
                rw [mul_comm]
                exact
                  N13SpecialCurveOverlap.tOverlap_mul_xOverlap]
    _ =
      N13SpecialCurveOverlap.xOverlap *
        (N13SpecialCurveOverlap.tOverlap *
          reduceInfinityOverlap
            N13OrdinaryCurveOverlap.xOverlap) := by
              rw [mul_assoc]
    _ = N13SpecialCurveOverlap.xOverlap := by
          rw [hinv, mul_one]

/-- The affine-to-infinity overlap square commutes under reduction. -/
theorem reduceInfinityOverlap_comp_affineOverlapToInfinityOverlap :
    reduceInfinityOverlap.comp
        N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap =
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap.comp
        reduceAffineOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13OrdinaryCurveOverlap.xClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineReduceToOverlap,
        infinityReduceToOverlap,
        N13GeneralizedMumfordReduction.reduceCoordinate,
        N13IntegralInfinityReduction.reduceCoordinate,
        N13SpecialCurveOverlap.affineToInfinityOverlap,
        N13OrdinaryCurveOverlap.affineCoeffMap,
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap,
        N13SpecialCurveOverlap.affineCoeffMap,
        N13SpecialCurveOverlap.coefficientToInfinityOverlap,
        N13GeneralizedMumfordReduction.reducePoly,
        N13GeneralizedMumfordReduction.reduceBase,
        N13IntegralInfinityReduction.reducePoly,
        N13IntegralInfinityReduction.reduceBase]
    · change
        reduceInfinityOverlap
            (N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap
              N13OrdinaryCurveOverlap.xAffineOverlap) =
          N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
            (reduceAffineOverlap
              N13OrdinaryCurveOverlap.xAffineOverlap)
      simp
  · change
      reduceInfinityOverlap
          (N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap
            N13OrdinaryCurveOverlap.yAffineOverlap) =
        N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
          (reduceAffineOverlap
            N13OrdinaryCurveOverlap.yAffineOverlap)
    simp

/-- The infinity-to-affine overlap square commutes under reduction. -/
theorem reduceAffineOverlap_comp_infinityOverlapToAffineOverlap :
    reduceAffineOverlap.comp
        N13OrdinaryCurveOverlap.infinityOverlapToAffineOverlap =
      N13SpecialCurveOverlap.infinityOverlapToAffineOverlap.comp
        reduceInfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers
      N13IntegralInfinityChart.tClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineReduceToOverlap,
        infinityReduceToOverlap,
        N13GeneralizedMumfordReduction.reduceCoordinate,
        N13IntegralInfinityReduction.reduceCoordinate,
        N13SpecialCurveOverlap.infinityToAffineOverlap,
        N13OrdinaryCurveOverlap.infinityCoeffMap,
        N13OrdinaryCurveOverlap.coefficientToAffineOverlap,
        N13SpecialCurveOverlap.infinityCoeffMap,
        N13SpecialCurveOverlap.coefficientToAffineOverlap,
        N13GeneralizedMumfordReduction.reducePoly,
        N13GeneralizedMumfordReduction.reduceBase,
        N13IntegralInfinityReduction.reducePoly,
        N13IntegralInfinityReduction.reduceBase]
    · change
        reduceAffineOverlap
            (N13OrdinaryCurveOverlap.infinityOverlapToAffineOverlap
              N13OrdinaryCurveOverlap.tOverlap) =
          N13SpecialCurveOverlap.infinityOverlapToAffineOverlap
            (reduceInfinityOverlap
              N13OrdinaryCurveOverlap.tOverlap)
      simp
  · change
      reduceAffineOverlap
          (N13OrdinaryCurveOverlap.infinityOverlapToAffineOverlap
            N13OrdinaryCurveOverlap.vOverlap) =
        N13SpecialCurveOverlap.infinityOverlapToAffineOverlap
          (reduceInfinityOverlap
            N13OrdinaryCurveOverlap.vOverlap)
    simp

/-- Equivalently, the forward square commutes with the two exported overlap
equivalences. -/
theorem reduceInfinityOverlap_comp_overlapEquiv :
    reduceInfinityOverlap.comp
        N13OrdinaryCurveOverlap.overlapEquiv.toRingHom =
      N13SpecialCurveOverlap.overlapEquiv.toRingHom.comp
        reduceAffineOverlap :=
  reduceInfinityOverlap_comp_affineOverlapToInfinityOverlap

end

end MazurProof.N13OverlapReductionCompatibility


