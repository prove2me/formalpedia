-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EscapingPointSpecialRestriction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13EscapingPointSpecialRestriction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:47:11.829376+00:00
-- url     : https://prove2.me/theorems/4186ab51-4f87-417b-8136-c434d2cd03a6
-- title:
--   FLT.Assumptions.MazurProof.N13EscapingPointSpecialRestriction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13EscapingPointSpecialRestriction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13EscapingPointSpecialRestriction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityLineSpecialRestriction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EscapingDegreeOneSpread_p0

set_option autoImplicit false




/-!
# Special restriction of escaping affine N13 point lines

An affine point with negative two-adic horizontal valuation is integral on
the infinity chart.  Its inverse horizontal coordinate reduces to zero, so
the proper line specializes to one of the two points at infinity on the
special curve.

The infinity-chart equality is coefficientwise graph reduction.  On the
ordinary affine chart the cleared horizontal equation is `1-t₀x`; its
reduction is `1`, hence that chart ideal becomes the unit ideal.  Together
these are the exact two chart equalities required by the special-divisor
realization.
-/

open scoped Sym2

namespace MazurProof.N13EscapingPointSpecialRestriction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The two-adic coefficient field. -/
abbrev Q₂ : Type :=
  N13ProperCurveReduction.Q₂

/-- The integral infinity-chart lift of an escaping affine point. -/
abbrev Lift
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13IntegralInfinityPointSpread.IntegralInfinityPoint :=
  N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy

/-- The reduced affine-chart ideal of an escaping point line is the unit
ideal because its horizontal generator `1-t₀x` reduces to `1`. -/
theorem restrict_nonintegralPointLine_affineIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy)).affineIdeal := by
  let P : N13IntegralInfinityPointSpread.IntegralInfinityPoint :=
    N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.affinePointIdeal P) =
      ⊤
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13IntegralInfinityPointSpread.affineU P)
          (N13IntegralInfinityPointSpread.affineV P)) =
      ⊤
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal]
  have ht :
      N13GeneralizedMumfordReduction.reduceBase P.1.1 = 0 := by
    exact
      N13IntegralInfinityPointSpread.nonintegralLift_t_residue_eq_zero
        x y hx hxy
  have hu :
      N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityPointSpread.affineU P) = 1 := by
    simp [N13IntegralInfinityPointSpread.affineU,
      N13GeneralizedMumfordReduction.reducePoly_apply, ht]
  rw [hu, Ideal.eq_top_iff_one]
  exact
    N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
      1
      (N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityPointSpread.affineV P))

/-- The reduced infinity-chart ideal is exactly the canonical ideal of the
properly reduced point at infinity. -/
theorem restrict_nonintegralPointLine_infinityIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy)).infinityIdeal := by
  let P : N13IntegralInfinityPointSpread.IntegralInfinityPoint :=
    N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal P) =
      N13SpecialDivisorCharts.infinityPointIdeal
        0
        (N13IntegralInfinityReduction.reduceBase P.1.2)
  rw [N13InfinityLineSpecialRestriction.map_pointIdeal]
  congr 2
  exact
    N13IntegralInfinityPointSpread.nonintegralLift_t_residue_eq_zero
      x y hx hxy

/-- Degree-two normalization of an escaping point line by adjoining the
positive-infinity anchor once. -/
def anchoredPointLine
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  N13TwoChartLineTensor.withPositiveInfinityMultiplicity
    (N13IntegralInfinityPointSpread.nonintegralPointLine
      x y hx hxy)
    1

/-- The intended special divisor of the anchored escaping point line. -/
def anchoredDivisor
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  s(N13ProperCurveReduction.reduceNonintegralAffine x y hx hxy,
    N13RationalPointEndgame.specialAnchor)

/-- The affine restriction of the anchored point line equals the affine
chart ideal of its literal anchored special divisor. -/
theorem restrict_anchoredPointLine_affineIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine x y hx hxy)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (anchoredDivisor x y hx hxy)).affineIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
    anchoredDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityPointSpread.nonintegralPointLine
          x y hx hxy)).affineIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).affineIdeal =
      (N13SpecialDivisorCharts.point
          (N13ProperCurveReduction.reduceNonintegralAffine
            x y hx hxy)).affineIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).affineIdeal
  rw [restrict_nonintegralPointLine_affineIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_affineIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]

/-- The infinity restriction of the anchored point line equals the infinity
chart ideal of the same literal anchored special divisor. -/
theorem restrict_anchoredPointLine_infinityIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine x y hx hxy)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (anchoredDivisor x y hx hxy)).infinityIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
    anchoredDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityPointSpread.nonintegralPointLine
          x y hx hxy)).infinityIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).infinityIdeal =
      (N13SpecialDivisorCharts.point
          (N13ProperCurveReduction.reduceNonintegralAffine
            x y hx hxy)).infinityIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).infinityIdeal
  rw [restrict_nonintegralPointLine_infinityIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_infinityIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]

end

end MazurProof.N13EscapingPointSpecialRestriction


