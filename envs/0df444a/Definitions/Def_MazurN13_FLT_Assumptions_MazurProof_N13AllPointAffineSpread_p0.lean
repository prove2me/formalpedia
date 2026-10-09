-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AllPointAffineSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13AllPointAffineSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:45:46.890995+00:00
-- url     : https://prove2.me/theorems/87dba5a0-faf0-4829-9d87-b9650d1f8c41
-- title:
--   FLT.Assumptions.MazurProof.N13AllPointAffineSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13AllPointAffineSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13AllPointAffineSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartLineTensor_p0

set_option autoImplicit false




/-!
# Affine integral spreads of all two-adic N13 points

An affine point of the good model has two structural integral
presentations.  If its horizontal coordinate is integral, use its monic
affine graph.  If it has negative valuation, use the affine half of its
explicit infinity-chart point line.  Both presentations are invertible
integral fractional ideals with exactly the standard sextic point ideal as
generic fibre.

Tensoring the two alternatives closes every split quadratic graph with
distinct roots, independently of the valuations of those roots.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13AllPointAffineSpread

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type :=
  N13EscapingDegreeOneSpread.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13EscapingDegreeOneSpread.Model

abbrev IntegralRing : Type :=
  N13IntegralGraphJacobian.IntegralRing

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal

local instance integralRationalAlgebra :
    Algebra IntegralRing N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- An invertible integral affine ideal realizing one standard sextic point
graph on the generic fibre. -/
structure PointSpread
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) where
  ideal : Ideal IntegralRing
  isUnit : IsUnit (ideal : IntegralFractionalIdeal)
  map_ideal :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic ideal =
      SexticMumford.mumfordIdeal Model
        (X - C x)
        (C (N13EscapingDegreeOneSpread.pointY x y))

/-- The monic affine graph presentation when `x` is integral. -/
def integralPointSpread
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : ‖x‖ ≤ 1) :
    PointSpread x y hcurve := by
  let P : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x y hx hcurve
  refine
    { ideal := N13IntegralAffinePointSpread.pointIdeal P
      isUnit := N13IntegralAffinePointSpread.pointIdeal_isUnit P
      map_ideal := ?_ }
  have hmap :=
    N13IntegralAffinePointSpread.map_pointIdeal P
  simpa [P, N13ProperCurveReduction.integralAffineLift,
    N13IntegralAffinePointSpread.curvePoint,
    N13IntegralAffinePointSpread.sexticY,
    N13EscapingDegreeOneSpread.pointY,
    SexticMumford.pointMumford,
    SexticMumford.affinePointMumford] using hmap

/-- The affine half of the proper infinity point line when `x` has
negative valuation. -/
def escapingPointSpread
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : x.valuation < 0) :
    PointSpread x y hcurve where
  ideal :=
    N13IntegralInfinityPointSpread.affinePointIdeal
      (N13EscapingDegreeOneSpread.lift x y hx hcurve)
  isUnit :=
    N13IntegralInfinityPointSpread.affinePointIdeal_isUnit
      (N13EscapingDegreeOneSpread.lift x y hx hcurve)
  map_ideal :=
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint
      x y hx hcurve

/-- Every two-adic affine curve point has one of the two integral affine
spread presentations. -/
def pointSpread
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    PointSpread x y hcurve := by
  by_cases hx : ‖x‖ ≤ 1
  · exact integralPointSpread x y hcurve hx
  · have hval : x.valuation < 0 :=
      lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg x).not.mp hx)
    exact escapingPointSpread x y hcurve hval

/-- Tensor product of two affine point spreads. -/
def pairIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    Ideal IntegralRing :=
  (pointSpread x₁ y₁ hcurve₁).ideal *
    (pointSpread x₂ y₂ hcurve₂).ideal

theorem pairIdeal_isUnit
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    IsUnit
      (pairIdeal x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ :
        IntegralFractionalIdeal) := by
  rw [pairIdeal, FractionalIdeal.coeIdeal_mul]
  exact
    (pointSpread x₁ y₁ hcurve₁).isUnit.mul
      (pointSpread x₂ y₂ hcurve₂).isUnit

/-- For distinct horizontal coordinates, the generic fibre of the tensor
spread is the quadratic secant graph. -/
theorem map_pairIdeal_eq_secantGraph
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂)
    (hneq : x₁ ≠ x₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pairIdeal x₁ y₁ x₂ y₂ hcurve₁ hcurve₂) =
      SexticMumford.mumfordIdeal Model
        ((X - C x₁) * (X - C x₂))
        (N13TwoChartLineTensor.secantV
          x₁ (N13EscapingDegreeOneSpread.pointY x₁ y₁)
          x₂ (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [pairIdeal, Ideal.map_mul,
    (pointSpread x₁ y₁ hcurve₁).map_ideal,
    (pointSpread x₂ y₂ hcurve₂).map_ideal,
    N13TwoChartLineTensor.pointIdeal_mul_eq_secantGraph
      _ _ _ _ hneq]

/-- Every balanced quadratic graph that splits over `ℚ₂` with distinct
roots has an invertible integral affine spread.  Rationality of the roots
is irrelevant; only the two-adic factorization is used. -/
theorem mumfordGraph_has_affineSpread_of_distinct_split
    (D : SexticMumford.Mumford Model)
    (x₁ x₂ : Q₂)
    (hfactor :
      D.u = (X - C x₁) * (X - C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ J : Ideal IntegralRing,
      IsUnit (J : IntegralFractionalIdeal) ∧
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic J =
          SexticMumford.mumfordIdeal Model D.u D.v := by
  have hDdeg : D.u.natDegree = 2 := by
    rw [hfactor]
    compute_degree
    norm_num
  obtain ⟨hsextic₁, hsextic₂⟩ :=
    N13TwoChartLineTensor.mumford_eval_onCurve_of_split
      D x₁ x₂ hfactor
  let y₁ := N13TwoChartLineTensor.goodY x₁ (D.v.eval x₁)
  let y₂ := N13TwoChartLineTensor.goodY x₂ (D.v.eval x₂)
  have hcurve₁ :
      N13GoodModelTwo.AffineEquation x₁ y₁ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₁ (D.v.eval x₁) hsextic₁
  have hcurve₂ :
      N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₂ (D.v.eval x₂) hsextic₂
  let J := pairIdeal x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  refine
    ⟨J,
      pairIdeal_isUnit
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂,
      ?_⟩
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pairIdeal x₁ y₁ x₂ y₂ hcurve₁ hcurve₂) =
      SexticMumford.mumfordIdeal Model D.u D.v
  rw [map_pairIdeal_eq_secantGraph
      x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ hneq,
    N13TwoChartLineTensor.pointY_goodY,
    N13TwoChartLineTensor.pointY_goodY,
    ← N13TwoChartLineTensor.mumford_v_eq_secant
      D hDdeg x₁ x₂ hneq,
    ← hfactor]

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- Every selected quadratic graph with two distinct rational roots has
an invertible integral affine spread, with no valuation restriction on
the roots. -/
theorem selectedGraph_has_affineSpread_of_distinct_split
    (P : G)
    (_hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 2)
    (x₁ x₂ : ℚ)
    (hfactor :
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u =
        (X - C x₁) * (X - C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ J : Ideal IntegralRing,
      IsUnit (J : IntegralFractionalIdeal) ∧
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic J =
          SexticMumford.mumfordIdeal Model
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).u
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).v := by
  let D :=
    N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford P
  let x₁₂ : Q₂ :=
    N13ProperCurveReduction.ratToQ₂ x₁
  let x₂₂ : Q₂ :=
    N13ProperCurveReduction.ratToQ₂ x₂
  have hneq₂ : x₁₂ ≠ x₂₂ :=
    N13InfinityBaseChange.ratToQ₂_injective.ne hneq
  have hfactor₂ :
      D.u = (X - C x₁₂) * (X - C x₂₂) := by
    have hmap :=
      congrArg
        (Polynomial.map N13InfinityBaseChange.ratToQ₂)
        hfactor
    simpa [D, x₁₂, x₂₂,
      N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford]
      using hmap
  simpa [D] using
    (mumfordGraph_has_affineSpread_of_distinct_split
      D x₁₂ x₂₂ hfactor₂ hneq₂)

end

end MazurProof.N13AllPointAffineSpread


