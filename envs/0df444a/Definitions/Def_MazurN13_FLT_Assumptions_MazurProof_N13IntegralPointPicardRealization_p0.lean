-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralPointPicardRealization_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralPointPicardRealization_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:57:41.509743+00:00
-- url     : https://prove2.me/theorems/9f471f54-14cc-4352-b15a-ab2e9f740c96
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralPointPicardRealization source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralPointPicardRealization

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralPointPicardRealization
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffinePointInfinityClosure_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartPicardRealization_p0

set_option autoImplicit false




/-!
# Picard realization of integral degree-one N13 points

An integral affine point has a proper two-chart closure whose two special
ideals are the canonical ideals of its coefficientwise reduction.  Adjoining
the positive-infinity line once places that point in the degree-two special
Abel model without changing its generic affine ideal.

The original point is affine, so its Mumford representative has `nInf = 0`.
Consequently the oriented generic exponent is `-1`, exactly as in the
escaping degree-one branch.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralPointPicardRealization

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Integral affine points of the good two-adic N13 model. -/
abbrev IntegralPoint : Type :=
  N13IntegralAffinePointSpread.IntegralPoint

/-- The good completed-square sextic model over the two-adic field. -/
abbrev Model : SexticMumford.Model
    N13TwoChartPicardRealization.Q₂ :=
  N13TwoChartPicardRealization.Model

/-- The degree-one Mumford representative of an integral affine point. -/
abbrev degreeOneMumford
    (P : IntegralPoint) :
    SexticMumford.Mumford Model :=
  SexticMumford.pointMumford Model
    (N13IntegralAffinePointSpread.curvePoint P)

/-- The literal integral affine-point line is vertically saturated.  Its
affine lattice is a monic generalized Mumford graph, whose quotient has the
standard free coefficient basis. -/
theorem integralPointTwoChartLine_affineVerticallySaturated
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P) := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_mumfordIdeal
      _ (N13IntegralAffinePointSpread.integralSemiGraph P)
  rfl

/-- The unanchored integral point line restricts to the canonical compatible
chart pair of the coefficientwise reduced point. -/
theorem restrict_integralPointTwoChartLine_eq_point
    (P : IntegralPoint) :
    N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P) =
      N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_affineIdeal
        P
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_infinityIdeal
        P

/-- The anchored integral line restricts to the literal degree-two divisor
formed by the reduced point and the fixed positive-infinity anchor. -/
theorem restrict_anchoredPointLine_eq_ofDivisor
    (P : IntegralPoint) :
    N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P) =
      N13SpecialDivisorCharts.ofDivisor
        (N13IntegralAffinePointSpecialClass.anchoredReducedDivisor P) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_anchoredPointLine_affineIdeal
        P
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_anchoredPointLine_infinityIdeal
        P

/-- Adding the positive-infinity anchor preserves the affine lattice, so
the normalized degree-two integral-point line remains vertically saturated. -/
theorem anchoredPointLine_affineVerticallySaturated
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffinePointInfinityClosure.anchoredPointLine P) := by
  simpa [N13TwoChartPicardRealization.AffineVerticallySaturated,
    N13FiniteAffinePointInfinityClosure.anchoredPointLine] using
    integralPointTwoChartLine_affineVerticallySaturated P

/-- Full two-fibre realization data for an integral affine point.

The positive-infinity tensor factor supplies special degree two, while the
oriented generic exponent `-1` records the affine point's zero infinity
multiplicity relative to the positive base point. -/
def data
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.Data where
  charts :=
    N13FiniteAffinePointInfinityClosure.anchoredPointLine P
  infinityOrder := -1
  specialDivisor :=
    N13IntegralAffinePointSpecialClass.anchoredReducedDivisor P
  special_affine :=
    N13FiniteAffinePointInfinityClosure.restrict_anchoredPointLine_affineIdeal
      P
  special_infinity :=
    N13FiniteAffinePointInfinityClosure.restrict_anchoredPointLine_infinityIdeal
      P

/-- The positive-infinity anchor is trivial on the generic affine chart, so
the anchored line still has the standard Mumford ideal of the original
integral point. -/
theorem map_anchoredPointLine_affineIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (degreeOneMumford P).u
        (degreeOneMumford P).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P).affineIdeal =
      _
  rw [N13FiniteAffinePointInfinityClosure.anchoredPointLine,
    N13TwoChartLineTensor.map_withPositiveInfinityMultiplicity_affineIdeal]
  exact
    N13FiniteAffineTwoChart.map_integralPointTwoChartLine_affineIdeal P

/-- The generic fractional-ideal unit of the anchored integral line is
exactly the unit packaged by its degree-one Mumford representative. -/
theorem genericIdealUnit_anchoredPointLine_eq_pointMumford
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.genericIdealUnit
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P) =
      SexticMumford.mumfordIdealUnit Model
        (degreeOneMumford P).toSemi := by
  apply Units.ext
  rw [N13TwoChartPicardRealization.coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      (map_anchoredPointLine_affineIdeal P)

/-- The raw oriented datum of the anchored integral line is literally the
Mumford raw datum: their ideal units agree and both exponents are `-1`. -/
theorem genericRaw_anchoredPointLine_eq_mumfordRaw
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.genericRaw
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P)
        (-1) =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford P) := by
  apply Prod.ext
  · change
      N13TwoChartPicardRealization.genericIdealUnit
          (N13FiniteAffinePointInfinityClosure.anchoredPointLine P) =
        SexticMumford.mumfordIdealUnit Model
          (degreeOneMumford P).toSemi
    exact
      genericIdealUnit_anchoredPointLine_eq_pointMumford P
  · change
      Multiplicative.ofAdd (-1 : ℤ) =
        Multiplicative.ofAdd
          (((degreeOneMumford P).nInf : ℤ) - 1)
    simp [degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]

/-- The generic raw datum selected by `data` is the exact Mumford raw datum,
before passing to the quotient by principal oriented ideals. -/
theorem data_genericRaw_eq_mumfordRaw
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.genericRaw
        (data P).charts
        (data P).infinityOrder =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford P) := by
  change
    N13TwoChartPicardRealization.genericRaw
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P)
        (-1) =
      _
  exact genericRaw_anchoredPointLine_eq_mumfordRaw P

/-- The generic class carried by the integral point's two-fibre data is the
standard oriented Picard class of its Mumford representative. -/
theorem data_toGenericPic_eq_classOf
    (P : IntegralPoint) :
    (data P).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (degreeOneMumford P) := by
  change
    N13TwoChartPicardRealization.genericClass
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P)
        (-1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (degreeOneMumford P)
  unfold N13TwoChartPicardRealization.genericClass
    SexticMumford.classOf
  rw [genericRaw_anchoredPointLine_eq_mumfordRaw]

end

end MazurProof.N13IntegralPointPicardRealization


