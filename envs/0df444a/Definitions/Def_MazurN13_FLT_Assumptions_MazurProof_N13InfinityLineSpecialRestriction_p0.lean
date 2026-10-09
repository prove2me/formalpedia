-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityLineSpecialRestriction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityLineSpecialRestriction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:44:51.875326+00:00
-- url     : https://prove2.me/theorems/643208e3-4343-4c46-aaca-ec958ce7e5e6
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityLineSpecialRestriction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityLineSpecialRestriction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityLineSpecialRestriction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartLineTensor_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RationalPointEndgame_p0

set_option autoImplicit false




/-!
# Special restriction of the two N13 infinity point lines

The integral infinity-chart point ideal has generators
`t-t₀` and `v-v₀`.  Coefficientwise reduction therefore sends it exactly to
the corresponding special point ideal.  In particular, the positive
infinity line restricts to the sheet-zero point used as the special Abel
anchor.

This is an equality of both chart ideals, not merely an equality of their
images in the special Picard quotient.
-/

open Polynomial

namespace MazurProof.N13InfinityLineSpecialRestriction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Integral points on the ordinary infinity chart. -/
abbrev IntegralInfinityPoint : Type :=
  N13IntegralInfinityPointSpread.IntegralInfinityPoint

/-- Points on the completed special curve. -/
abbrev CurvePoint : Type :=
  N13SymmetricSquareTwo.CurvePoint

/-- Reduction commutes with the horizontal polynomial map into the
infinity-chart coordinate ring. -/
@[simp] theorem reduce_xClassHom (p : N13IntegralInfinityPointSpread.Base) :
    N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.xClassHom p) =
      N13IntegralInfinityReduction.specialBaseClass
        (N13IntegralInfinityReduction.reducePoly p) := by
  change
    N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityReduction.integralBaseClass p) =
      N13IntegralInfinityReduction.specialBaseClass
        (N13IntegralInfinityReduction.reducePoly p)
  exact N13IntegralInfinityReduction.reduce_integralBaseClass p

/-- The special point ideal obtained by reducing an integral infinity point
has exactly the reduced coordinates of that point. -/
theorem map_pointIdeal (P : IntegralInfinityPoint) :
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal P) =
      N13SpecialDivisorCharts.infinityPointIdeal
        (N13IntegralInfinityReduction.reduceBase P.1.1)
        (N13IntegralInfinityReduction.reduceBase P.1.2) := by
  simp [N13IntegralInfinityPointSpread.pointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    N13IntegralInfinityPointSpread.pointU,
    N13IntegralInfinityPointSpread.pointV,
    N13SpecialDivisorCharts.infinityPointIdeal,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityPointSpread.yClass,
    N13IntegralInfinityReduction.specialBaseClass,
    N13IntegralInfinityReduction.reducePoly]

/-- The explicit special sheet-zero point at infinity. -/
def specialInfinityPlusPoint : CurvePoint :=
  Sum.inr
    ⟨0, by
      norm_num [N13GoodModelTwo.InfinityChartEquation]⟩

/-- The explicit sheet-zero point is the fixed special Abel anchor. -/
theorem specialInfinityPlusPoint_eq_specialAnchor :
    specialInfinityPlusPoint =
      N13RationalPointEndgame.specialAnchor := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  change
    (Sum.inr (), (0 : N13GoodModelTwo.F2)) =
      N13AbelFiberTwoModel.curvePointEquiv
        (N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityPlus)
  rw [N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  rfl

/-- The affine ideal of the restricted positive-infinity line is the unit
ideal, as is the affine ideal of its canonical special point pair. -/
theorem restrict_infinityPlusLine_affineIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityPlusLine).affineIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).affineIdeal := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        N13TwoChartLineTensor.infinityPlusLine.affineIdeal =
      ⊤
  rw [
    N13TwoChartLineTensor.infinityPlusLine_affineIdeal,
    Ideal.map_top]

/-- The infinity ideal of the restricted positive-infinity line is exactly
the canonical ideal of the special sheet-zero point. -/
theorem restrict_infinityPlusLine_infinityIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityPlusLine).infinityIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).infinityIdeal := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal
          N13TwoChartLineTensor.infinityPlusPoint) =
      N13SpecialDivisorCharts.infinityPointIdeal 0 0
  simpa [N13TwoChartLineTensor.infinityPlusPoint] using
    map_pointIdeal N13TwoChartLineTensor.infinityPlusPoint

/-- The explicit special sheet-one point at infinity. -/
def specialInfinityMinusPoint : CurvePoint :=
  Sum.inr
    ⟨1, by
      exact
        (N13GoodModelTwo.infinityChartEquation_zero_iff_fixed
          (K := N13GoodModelTwo.F2) 1).2 (by norm_num)⟩

/-- The explicit sheet-one point is the named negative-infinity cusp on the
special curve. -/
theorem specialInfinityMinusPoint_eq_specialCusp :
    specialInfinityMinusPoint =
      N13SpecialCuspReduction.specialCuspEquiv
        N13Mumford.Cusp13.infinityMinus := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  change
    (Sum.inr (), (1 : N13GoodModelTwo.F2)) =
      N13AbelFiberTwoModel.curvePointEquiv
        (N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityMinus)
  rw [N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  rfl

/-- The affine ideal of the restricted negative-infinity line is also the
unit ideal. -/
theorem restrict_infinityMinusLine_affineIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityMinusLine).affineIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityMinusPoint).affineIdeal := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        N13TwoChartLineTensor.infinityMinusLine.affineIdeal =
      ⊤
  rw [
    N13TwoChartLineTensor.infinityMinusLine_affineIdeal,
    Ideal.map_top]

/-- The negative-infinity line remembers its sheet: its ordinate `-1`
reduces to `1` in characteristic two. -/
theorem restrict_infinityMinusLine_infinityIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityMinusLine).infinityIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityMinusPoint).infinityIdeal := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal
          N13TwoChartLineTensor.infinityMinusPoint) =
      N13SpecialDivisorCharts.infinityPointIdeal 0 1
  simpa [N13TwoChartLineTensor.infinityMinusPoint,
    N13IntegralInfinityReduction.reduceBase,
    N13GeneralizedMumfordReduction.reduceBase] using
    map_pointIdeal N13TwoChartLineTensor.infinityMinusPoint

/-- Every natural positive-infinity tensor power restricts on the affine
chart to the corresponding power of the special anchor's unit ideal. -/
theorem restrict_positiveInfinityPowerLine_affineIdeal
    (n : ℕ) :
    (N13TwoChartSpecialRestriction.restrict
      (N13TwoChartLineTensor.positiveInfinityPowerLine n)).affineIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).affineIdeal ^ n := by
  rw [N13TwoChartLineTensor.positiveInfinityPowerLine,
    N13TwoChartSpecialRestriction.restrict_tensorPow_affineIdeal,
    restrict_infinityPlusLine_affineIdeal]

/-- Every natural positive-infinity tensor power restricts on the infinity
chart to the corresponding power of the special anchor point ideal. -/
theorem restrict_positiveInfinityPowerLine_infinityIdeal
    (n : ℕ) :
    (N13TwoChartSpecialRestriction.restrict
      (N13TwoChartLineTensor.positiveInfinityPowerLine n)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).infinityIdeal ^ n := by
  rw [N13TwoChartLineTensor.positiveInfinityPowerLine,
    N13TwoChartSpecialRestriction.restrict_tensorPow_infinityIdeal,
    restrict_infinityPlusLine_infinityIdeal]

end

end MazurProof.N13InfinityLineSpecialRestriction


