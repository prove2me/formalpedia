-- Prove2me | Definitions.Def_HuangN13_IntegralTensorDataCore
-- name    : HuangN13_IntegralTensorDataCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:43:22.726624+00:00
-- url     : https://prove2.me/theorems/c3f2e2cb-77b4-4c58-83f6-7bfb44d79d1b
-- title:
--   Two-chart tensor data and its integral comparison record
-- statement:
--   The original actual marked two-chart data, generic Picard realization, tensor operation, and integral comparison record, with exactly the map and reduction proofs needed to construct their types and values.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_of (p : R₂[X]) :
    affineToInfinityOverlap
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)) p) =
      affineCoeffMap p := by
  exact AdjoinRoot.lift_of affineCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_xClass :
    affineToInfinityOverlap xClass = xOverlap := by
  simp [affineToInfinityOverlap, xClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.mk, affineCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_yClass :
    affineToInfinityOverlap yClass = affineYImage := by
  exact AdjoinRoot.lift_root affineCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem affine_xClass_mapsToUnit :
    IsUnit (affineToInfinityOverlap xClass) := by
  rw [affineToInfinityOverlap_xClass]
  exact xOverlap_isUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The induced restriction from the affine principal open to the infinity
principal open. -/
def affineOverlapToInfinityOverlap :
    AffineOverlap →+* InfinityOverlap :=
  IsLocalization.Away.lift xClass affine_xClass_mapsToUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineOverlapToInfinityOverlap_algebraMap
    (z : AffineCurve) :
    affineOverlapToInfinityOverlap
        (algebraMap AffineCurve AffineOverlap z) =
      affineToInfinityOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      xClass affine_xClass_mapsToUnit z
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineOverlapToInfinityOverlap_xAffineOverlap :
    affineOverlapToInfinityOverlap xAffineOverlap = xOverlap := by
  rw [xAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_xClass]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineOverlapToInfinityOverlap_yAffineOverlap :
    affineOverlapToInfinityOverlap yAffineOverlap =
      xOverlap ^ 3 * vOverlap := by
  rw [yAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_yClass]
  rfl
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_vClass :
    reduceCoordinate N13IntegralInfinityChart.vClass =
      N13SpecialInfinityChart.vClass := by
  exact AdjoinRoot.map_root
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
abbrev TwoChartLine : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Tensor product in the explicit two-chart presentation. -/
def tensor (L M : TwoChartLine) : TwoChartLine where
  affineIdeal := L.affineIdeal * M.affineIdeal
  infinityIdeal := L.infinityIdeal * M.infinityIdeal
  affine_isUnit := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact L.affine_isUnit.mul M.affine_isUnit
  infinity_isUnit := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact L.infinity_isUnit.mul M.infinity_isUnit
  overlap_eq := by
    rw [Ideal.map_mul, Ideal.map_mul, L.overlap_eq, M.overlap_eq]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_xClass :
    affineToInfinityOverlap xClass = xOverlap := by
  simp [affineToInfinityOverlap, xClass,
    N13GoodCoordinateRingTwo.xClass,
    N13GoodCoordinateRingTwo.mk, affineCoeffMap]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
theorem affine_xClass_mapsToUnit :
    IsUnit (affineToInfinityOverlap xClass) := by
  rw [affineToInfinityOverlap_xClass]
  exact xOverlap_isUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The induced restriction from the affine principal open to the infinity
principal open. -/
def affineOverlapToInfinityOverlap :
    AffineOverlap →+* InfinityOverlap :=
  IsLocalization.Away.lift xClass affine_xClass_mapsToUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem affineOverlapToInfinityOverlap_algebraMap
    (z : AffineCurve) :
    affineOverlapToInfinityOverlap
        (algebraMap AffineCurve AffineOverlap z) =
      affineToInfinityOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      xClass affine_xClass_mapsToUnit z
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem affineOverlapToInfinityOverlap_xAffineOverlap :
    affineOverlapToInfinityOverlap xAffineOverlap = xOverlap := by
  rw [xAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_xClass]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem affineOverlapToInfinityOverlap_yAffineOverlap :
    affineOverlapToInfinityOverlap yAffineOverlap =
      xOverlap ^ 3 * vOverlap := by
  rw [yAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_yClass]
  rfl
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] private theorem affineReduceToOverlap_y :
    affineReduceToOverlap N13OrdinaryCurveOverlap.yClass =
      algebraMap SpecialAffine SpecialAffineOverlap
        N13SpecialCurveOverlap.yClass := by
  simp [affineReduceToOverlap,
    N13OrdinaryCurveOverlap.yClass,
    N13SpecialCurveOverlap.yClass,
    RingHom.comp_apply]
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceAffineOverlap_x :
    reduceAffineOverlap
        N13OrdinaryCurveOverlap.xAffineOverlap =
      N13SpecialCurveOverlap.xAffineOverlap := by
  rw [N13OrdinaryCurveOverlap.xAffineOverlap,
    reduceAffineOverlap_algebraMap,
    affineReduceToOverlap_x]
  rfl
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceAffineOverlap_y :
    reduceAffineOverlap
        N13OrdinaryCurveOverlap.yAffineOverlap =
      N13SpecialCurveOverlap.yAffineOverlap := by
  rw [N13OrdinaryCurveOverlap.yAffineOverlap,
    reduceAffineOverlap_algebraMap,
    affineReduceToOverlap_y]
  rfl
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] private theorem infinityReduceToOverlap_v :
    infinityReduceToOverlap
        N13IntegralInfinityChart.vClass =
      algebraMap SpecialInfinity SpecialInfinityOverlap
        N13SpecialInfinityChart.vClass := by
  simp [infinityReduceToOverlap, RingHom.comp_apply]
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceInfinityOverlap_t :
    reduceInfinityOverlap
        N13OrdinaryCurveOverlap.tOverlap =
      N13SpecialCurveOverlap.tOverlap := by
  rw [N13OrdinaryCurveOverlap.tOverlap,
    reduceInfinityOverlap_algebraMap,
    infinityReduceToOverlap_t]
  rfl
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceInfinityOverlap_v :
    reduceInfinityOverlap
        N13OrdinaryCurveOverlap.vOverlap =
      N13SpecialCurveOverlap.vOverlap := by
  rw [N13OrdinaryCurveOverlap.vOverlap,
    reduceInfinityOverlap_algebraMap,
    infinityReduceToOverlap_v]
  rfl
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
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
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OverlapReductionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
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
end
end MazurProof.N13OverlapReductionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
/-- Proper line data on the two ordinary charts. -/
abbrev Line : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Literal reduction of the affine-chart ideal. -/
def affineIdeal (L : Line) : Ideal SpecialAffine :=
  Ideal.map
    N13GeneralizedMumfordReduction.reduceCoordinate
    L.affineIdeal
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Literal reduction of the infinity-chart ideal. -/
def infinityIdeal (L : Line) : Ideal SpecialInfinity :=
  Ideal.map
    N13IntegralInfinityReduction.reduceCoordinate
    L.infinityIdeal
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Reducing the direct ordinary affine-to-infinity map gives the direct
special affine-to-infinity map.

The localized overlap square is already known.  Evaluating it on elements
coming from the unlocalized affine chart removes the intermediate affine
localization and yields precisely the direct chart map used by
`TwoChartLine.overlap_eq`. -/
theorem reduceInfinityOverlap_comp_affineToInfinityOverlap :
    N13OverlapReductionCompatibility.reduceInfinityOverlap.comp
        N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      N13SpecialCurveOverlap.affineToInfinityOverlap.comp
        N13GeneralizedMumfordReduction.reduceCoordinate := by
  apply DFunLike.ext _ _
  intro z
  have h :=
    DFunLike.congr_fun
      N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_affineOverlapToInfinityOverlap
      (algebraMap
        N13OrdinaryCurveOverlap.AffineCurve
        N13OrdinaryCurveOverlap.AffineOverlap z)
  calc
    _ =
        N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
          (N13OverlapReductionCompatibility.reduceAffineOverlap
            (algebraMap
              N13OrdinaryCurveOverlap.AffineCurve
              N13OrdinaryCurveOverlap.AffineOverlap z)) := by
      simpa only [RingHom.comp_apply,
        N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap]
        using h
    _ =
        N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
          (algebraMap SpecialAffine
            N13SpecialCurveOverlap.AffineOverlap
            (N13GeneralizedMumfordReduction.reduceCoordinate z)) := by
      exact congrArg
        N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
        (show
          N13OverlapReductionCompatibility.reduceAffineOverlap
              (algebraMap N13OrdinaryCurveOverlap.AffineCurve
                N13OrdinaryCurveOverlap.AffineOverlap z) =
            algebraMap SpecialAffine N13SpecialCurveOverlap.AffineOverlap
              (N13GeneralizedMumfordReduction.reduceCoordinate z) from
          DFunLike.congr_fun
            N13OverlapReductionCompatibility.reduceAffineOverlap_comp_algebraMap
            z)
    _ = _ :=
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap _
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Reducing an integral two-chart line gives two special ideals that still
agree after extension to the special overlap. -/
theorem overlap_eq (L : Line) :
    Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (affineIdeal L) =
      Ideal.map
        (algebraMap SpecialInfinity
          N13SpecialCurveOverlap.InfinityOverlap)
        (infinityIdeal L) := by
  have h :=
    congrArg
      (Ideal.map
        N13OverlapReductionCompatibility.reduceInfinityOverlap)
      L.overlap_eq
  simpa only [affineIdeal, infinityIdeal, Ideal.map_map,
    reduceInfinityOverlap_comp_affineToInfinityOverlap,
    N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap]
    using h
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
/-- Ring-level special restriction of a concrete integral two-chart line. -/
def restrict (L : Line) : ChartPair where
  affineIdeal := affineIdeal L
  infinityIdeal := infinityIdeal L
  overlap_eq := overlap_eq L
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Oriented generic fractional-ideal datum of a proper line.

The integer is explicit because the generic affine ideal alone cannot
distinguish the two points at infinity or record an infinity twist. -/
def genericRaw (L : Line) (infinityOrder : ℤ) :
    SexticMumford.OrientedFrac Model :=
  (genericIdealUnit L, Multiplicative.ofAdd infinityOrder)
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Oriented generic Picard class carried by a marked proper line. -/
def genericClass (L : Line) (infinityOrder : ℤ) :
    GenericPic :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (SexticMumford.principalOriented
        Model
        (N13Infinity.positiveInfinityOrder Q₂)).range
      (genericRaw L infinityOrder)
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
/-- One proper line together with exact interpretations on both fibres.

The special equalities retain both chart ideals.  Thus the special divisor
cannot be chosen merely from the affine support while silently forgetting
which infinity sheet or infinity multiplicity the proper line carries. -/
structure Data where
  charts : Line
  infinityOrder : ℤ
  specialDivisor : EffectiveDivisorTwo
  special_affine :
    (N13TwoChartSpecialRestriction.restrict charts).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor specialDivisor).affineIdeal
  special_infinity :
    (N13TwoChartSpecialRestriction.restrict charts).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor specialDivisor).infinityIdeal
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
namespace Data
/-- The oriented generic class represented by the proper line. -/
def toGenericPic (D : Data) : GenericPic :=
  genericClass D.charts D.infinityOrder
end Data
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13CoherentChartComparison
noncomputable section
abbrev Line := N13TwoChartPicardRealization.Line
end
end MazurProof.N13CoherentChartComparison
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13CoherentChartComparison
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- One common rational principal comparison whose two chart presentations
have nonzero reduction. The nonzero-reduction requirements exclude a
vertical factor being silently discarded in specialization. -/
structure IntegralComparison (L M : Line) where
  aNum : A
  aDen : A
  iNum : B
  iDen : B
  aNum_ne : N13GeneralizedMumfordReduction.reduceCoordinate aNum ≠ 0
  aDen_ne : N13GeneralizedMumfordReduction.reduceCoordinate aDen ≠ 0
  iNum_ne : N13IntegralInfinityReduction.reduceCoordinate iNum ≠ 0
  iDen_ne : N13IntegralInfinityReduction.reduceCoordinate iDen ≠ 0
  affine_eq :
    Ideal.span ({aNum} : Set A) * L.affineIdeal =
      Ideal.span ({aDen} : Set A) * M.affineIdeal
  infinity_eq :
    Ideal.span ({iNum} : Set B) * L.infinityIdeal =
      Ideal.span ({iDen} : Set B) * M.infinityIdeal
  overlap_eq :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap aNum * algebraMap B O iDen =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap aDen * algebraMap B O iNum
end
end MazurProof.N13CoherentChartComparison
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedTensorComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair N13IntegralPrincipalComparison
open scoped nonZeroDivisors
abbrev tensor := N13TwoChartLineTensor.tensor
end
end MazurProof.N13MarkedTensorComparison
end
end


