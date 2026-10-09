-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralAffinePointSpecialClass_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralAffinePointSpecialClass_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:28:16.806401+00:00
-- url     : https://prove2.me/theorems/0b0d31de-a7db-40aa-8da7-699d2c996293
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralAffinePointSpecialClass source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralAffinePointSpecialClass

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralAffinePointSpecialClass
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffineTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinitySpecialPointClass_p0

set_option autoImplicit false




/-!
# Special classes of integral affine N13 point lines

An integral point on the good two-adic affine chart has a literal monic graph
ideal and, by finite-support closure, an actual proper two-chart line.
Coefficientwise reduction sends that affine ideal exactly to the linear graph
of the reduced point on the special curve.

The special Abel model has degree two, so a reduced affine point is normalized
by adjoining the fixed positive-infinity anchor once.  This normalization is
kept explicit: the affine ideal alone cannot see it because the positive
infinity point line is trivial on the affine chart.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13IntegralAffinePointSpecialClass

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The two-adic coefficient ring of the integral point graph. -/
abbrev R₂ : Type :=
  N13GeneralizedMumfordReduction.R₂

/-- Integral affine points of the good N13 model. -/
abbrev IntegralPoint : Type :=
  N13IntegralAffinePointSpread.IntegralPoint

/-- Points of the six-point special curve. -/
abbrev SpecialCurvePoint : Type :=
  N13RationalPointEndgame.SpecialCurvePoint

/-- The set-valued special Picard model used by the N13 endgame. -/
abbrev SpecialSet : Type :=
  N13RationalPointEndgame.SpecialSet

/-- The special affine coordinate ring. -/
abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

/-- Coefficientwise reduction of an integral affine point.

The good-model equation is preserved by the residue map
`ℤ₂ → 𝔽₂`, so the two reduced coordinates define an affine point of the
special curve. -/
def reducedPoint (P : IntegralPoint) : SpecialCurvePoint :=
  Sum.inl
    ⟨(PadicInt.toZMod P.1.1, PadicInt.toZMod P.1.2),
      by
        simpa [N13GoodModelTwo.AffineEquation,
          N13GoodModelTwo.h, N13GoodModelTwo.rhs] using
          congrArg (PadicInt.toZMod (p := 2)) P.2⟩

/-- The finite base and sheet coordinates of the reduced point are the
coefficientwise residues of the integral coordinates. -/
@[simp] theorem curvePointEquiv_reducedPoint
    (P : IntegralPoint) :
    N13AbelFiberTwoModel.curvePointEquiv (reducedPoint P) =
      (Sum.inl (PadicInt.toZMod P.1.1),
        PadicInt.toZMod P.1.2) :=
  rfl

/-- The literal linear graph ideal of the reduced affine point. -/
def reducedPointIdeal (P : IntegralPoint) : Ideal SpecialRing :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    (X - C (PadicInt.toZMod P.1.1))
    (C (PadicInt.toZMod P.1.2))

/-- Reduction of the integral affine point ideal is exactly the linear
Mumford graph of the coefficientwise reduced point.

This is an equality of ideals after base change, rather than only a
containment or a comparison of quotient cardinalities. -/
theorem map_pointIdeal_eq_reducedPointIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralAffinePointSpread.pointIdeal P) =
      reducedPointIdeal P := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂)
          (N13IntegralAffinePointSpread.pointU P)
          (N13IntegralAffinePointSpread.pointV P)) =
      reducedPointIdeal P
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal]
  simp [reducedPointIdeal,
    N13IntegralAffinePointSpread.pointU,
    N13IntegralAffinePointSpread.pointV,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    N13GeneralizedMumfordReduction.reduceBase]

/-- Place the reduced point in the degree-two Abel model by adjoining the
chosen positive-infinity anchor exactly once. -/
def anchoredReducedDivisor
    (P : IntegralPoint) :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  s(reducedPoint P, N13RationalPointEndgame.specialAnchor)

/-- The concrete special class attached to the integral-point-line family.

The point parameter is retained as provenance because a raw two-chart line
does not yet carry a general Cartier-divisor specialization map. -/
def pointLineSpecialClass
    (P : IntegralPoint) : SpecialSet :=
  N13AbelFiberTwoModel.abel (anchoredReducedDivisor P)

/-- The concrete class uses exactly the anchored point-class normalization
of the rational-point endgame. -/
@[simp] theorem pointLineSpecialClass_eq_specialPointClass
    (P : IntegralPoint) :
    pointLineSpecialClass P =
      N13RationalPointEndgame.specialPointClass
        (reducedPoint P) := by
  rfl

/-- The affine component of the proper integral point line has the same exact
special graph as the stored integral point.

The contracted infinity ideal supplies proper gluing but does not alter this
affine reduction equality. -/
theorem map_integralPointTwoChartLine_affineIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      reducedPointIdeal P := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralAffinePointSpread.pointIdeal P) =
      reducedPointIdeal P
  exact map_pointIdeal_eq_reducedPointIdeal P

end

end MazurProof.N13IntegralAffinePointSpecialClass


