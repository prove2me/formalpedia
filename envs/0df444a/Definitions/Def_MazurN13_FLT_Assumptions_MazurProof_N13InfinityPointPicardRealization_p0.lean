-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityPointPicardRealization_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityPointPicardRealization_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:27:58.026045+00:00
-- url     : https://prove2.me/theorems/48de0058-b2d9-43bd-9824-69972f8a6bab
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityPointPicardRealization source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityPointPicardRealization

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityPointPicardRealization
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityLineSpecialRestriction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SplitQuadraticPicardRealization_p0

set_option autoImplicit false




/-!
# Picard realization of the two N13 infinity points

The positive infinity point is the Abel--Jacobi base point.  Two copies of
its proper point line therefore realize the identity class and reduce to the
doubled special anchor.  Tensoring the negative infinity line with the
positive anchor realizes the difference of the two infinity points and
retains both special sheets.

These are the two projective cases missing from the existing affine-point
realizations.  Both constructions use literal chart ideals and the standard
oriented Mumford representatives.
-/

open scoped Sym2

namespace MazurProof.N13InfinityPointPicardRealization

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The two-adic N13 sextic model. -/
abbrev Model : SexticMumford.Model
    N13TwoChartPicardRealization.Q₂ :=
  N13TwoChartPicardRealization.Model

/-- The doubled positive-infinity line used for the identity class. -/
def infinityPlusLine : N13TwoChartPicardRealization.Line :=
  N13TwoChartLineTensor.tensor
    N13TwoChartLineTensor.infinityPlusLine
    N13TwoChartLineTensor.infinityPlusLine

/-- The doubled positive-infinity line is vertically saturated on the
affine chart.  Both point factors are trivial there, so their tensor product
has the unit ideal and contains no vertical torsion. -/
theorem infinityPlusLine_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      infinityPlusLine := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_top
  simp [infinityPlusLine]

/-- The special divisor consisting of two copies of the positive anchor. -/
def infinityPlusDivisor :
    N13TwoChartPicardRealization.EffectiveDivisorTwo :=
  s(N13InfinityLineSpecialRestriction.specialInfinityPlusPoint,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint)

/-- The positive-infinity construction restricts to the exact chart pair of
the doubled special anchor. -/
theorem restrict_infinityPlusLine_eq_ofDivisor :
    N13TwoChartSpecialRestriction.restrict infinityPlusLine =
      N13SpecialDivisorCharts.ofDivisor infinityPlusDivisor := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · simp only [infinityPlusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
      infinityPlusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_affineIdeal]
  · simp only [infinityPlusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
      infinityPlusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_infinityIdeal]

/-- The doubled positive-infinity line has the unit generic affine ideal,
which is the Mumford ideal of the balanced identity representative. -/
theorem map_infinityPlusLine_affineIdeal :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        infinityPlusLine.affineIdeal =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.zero Model).u
        (SexticMumford.zero Model).v := by
  rw [infinityPlusLine,
    N13TwoChartLineTensor.tensor_affineIdeal,
    N13TwoChartLineTensor.infinityPlusLine_affineIdeal,
    Ideal.top_mul, Ideal.map_top]
  exact (SexticMumford.zero_mumfordIdeal Model).symm

/-- Complete two-fibre data for the positive infinity base point. -/
def infinityPlusData :
    N13TwoChartPicardRealization.Data :=
  N13SplitQuadraticPicardRealization.dataOfSpecialRealization
    (SexticMumford.zero Model)
    infinityPlusLine
    infinityPlusDivisor
    (congrArg
      (fun C => C.affineIdeal)
      restrict_infinityPlusLine_eq_ofDivisor)
    (congrArg
      (fun C => C.infinityIdeal)
      restrict_infinityPlusLine_eq_ofDivisor)

/-- The generic class of the positive-infinity data is the identity
Abel--Jacobi class. -/
theorem infinityPlusData_toGenericPic :
    infinityPlusData.toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (SexticMumford.zero Model) := by
  exact
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
      (SexticMumford.zero Model)
      infinityPlusLine
      infinityPlusDivisor
      (congrArg
        (fun C => C.affineIdeal)
        restrict_infinityPlusLine_eq_ofDivisor)
      (congrArg
        (fun C => C.infinityIdeal)
        restrict_infinityPlusLine_eq_ofDivisor)
      map_infinityPlusLine_affineIdeal

/-- The special class of the positive-infinity data is the doubled special
anchor used by the rational-point endgame. -/
theorem infinityPlusData_toSpecialPic :
    infinityPlusData.toSpecialPic =
      N13RationalPointEndgame.specialPointClass
        N13InfinityLineSpecialRestriction.specialInfinityPlusPoint := by
  rfl

/-- The anchored negative-infinity line remembers the two distinct infinity
sheets while presenting an effective divisor of degree two. -/
def infinityMinusLine : N13TwoChartPicardRealization.Line :=
  N13TwoChartLineTensor.tensor
    N13TwoChartLineTensor.infinityMinusLine
    N13TwoChartLineTensor.infinityPlusLine

/-- The anchored negative-infinity line is vertically saturated on the
affine chart.  As for the positive branch, all geometric information lives
on the infinity chart and the affine ideal is the unit ideal. -/
theorem infinityMinusLine_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      infinityMinusLine := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_top
  simp [infinityMinusLine]

/-- The special divisor formed by the negative infinity point and the fixed
positive anchor. -/
def infinityMinusDivisor :
    N13TwoChartPicardRealization.EffectiveDivisorTwo :=
  s(N13InfinityLineSpecialRestriction.specialInfinityMinusPoint,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint)

/-- The anchored negative-infinity construction restricts to the literal
chart pair retaining both special sheets. -/
theorem restrict_infinityMinusLine_eq_ofDivisor :
    N13TwoChartSpecialRestriction.restrict infinityMinusLine =
      N13SpecialDivisorCharts.ofDivisor infinityMinusDivisor := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · simp only [infinityMinusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
      infinityMinusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_affineIdeal,
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_affineIdeal]
  · simp only [infinityMinusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
      infinityMinusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_infinityIdeal,
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_infinityIdeal]

/-- The anchored negative-infinity line has the unit generic affine ideal,
matching the standard negative-infinity Mumford representative. -/
theorem map_infinityMinusLine_affineIdeal :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        infinityMinusLine.affineIdeal =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.infinityMinusMumford Model).u
        (SexticMumford.infinityMinusMumford Model).v := by
  rw [infinityMinusLine,
    N13TwoChartLineTensor.tensor_affineIdeal,
    N13TwoChartLineTensor.infinityMinusLine_affineIdeal,
    N13TwoChartLineTensor.infinityPlusLine_affineIdeal,
    Ideal.top_mul, Ideal.map_top]
  exact (SexticMumford.zero_mumfordIdeal Model).symm

/-- Complete two-fibre data for the negative infinity point. -/
def infinityMinusData :
    N13TwoChartPicardRealization.Data :=
  N13SplitQuadraticPicardRealization.dataOfSpecialRealization
    (SexticMumford.infinityMinusMumford Model)
    infinityMinusLine
    infinityMinusDivisor
    (congrArg
      (fun C => C.affineIdeal)
      restrict_infinityMinusLine_eq_ofDivisor)
    (congrArg
      (fun C => C.infinityIdeal)
      restrict_infinityMinusLine_eq_ofDivisor)

/-- The generic class of the negative-infinity data is the standard
difference of the two infinity points. -/
theorem infinityMinusData_toGenericPic :
    infinityMinusData.toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (SexticMumford.infinityMinusMumford Model) := by
  exact
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
      (SexticMumford.infinityMinusMumford Model)
      infinityMinusLine
      infinityMinusDivisor
      (congrArg
        (fun C => C.affineIdeal)
        restrict_infinityMinusLine_eq_ofDivisor)
      (congrArg
        (fun C => C.infinityIdeal)
        restrict_infinityMinusLine_eq_ofDivisor)
      map_infinityMinusLine_affineIdeal

/-- The special class of the negative-infinity data is its anchored proper
reduction. -/
theorem infinityMinusData_toSpecialPic :
    infinityMinusData.toSpecialPic =
      N13RationalPointEndgame.specialPointClass
        N13InfinityLineSpecialRestriction.specialInfinityMinusPoint := by
  rfl

end

end MazurProof.N13InfinityPointPicardRealization


