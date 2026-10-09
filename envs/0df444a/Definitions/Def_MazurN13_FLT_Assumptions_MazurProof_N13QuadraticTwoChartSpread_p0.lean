-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:55:43.633726+00:00
-- url     : https://prove2.me/theorems/c617f70f-88b5-4c0f-a70b-0a957a6c53c1
-- title:
--   FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticSpread_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RepeatedRootSpread_p0

set_option autoImplicit false




/-!
# Proper two-chart spreads for every quadratic N13 graph

Every two-adic affine point has a proper point line.  Integral points use the
finite-support closure of their monic affine graph, while nonintegral points
use the explicit infinity-chart line.  Tensoring two such point lines gives
proper spreads for split quadratic graphs, including the tangent
repeated-root case.

A monic quadratic is either split or irreducible.  Combining the point-line
tensor construction with the irreducible quadratic closure therefore gives
an actual proper two-chart line for every balanced quadratic Mumford graph.
-/

open Polynomial

namespace MazurProof.N13QuadraticTwoChartSpread

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The two-adic coefficient field of the generic N13 model. -/
abbrev Q₂ : Type :=
  N13AllPointAffineSpread.Q₂

/-- The good sextic N13 model over the two-adic field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13AllPointAffineSpread.Model

/-- Proper lines presented on the ordinary affine and infinity charts. -/
abbrev TwoChartLine : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine

/-- Rational Picard classes used by the selected-graph construction. -/
abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- Proper point line for a point whose affine horizontal coordinate is
integral. -/
def integralPointLine
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : ‖x‖ ≤ 1) :
    TwoChartLine :=
  let P : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x y hx hcurve
  N13FiniteAffineTwoChart.integralPointTwoChartLine P

/-- The generic affine ideal of the integral point line is the standard
sextic point graph. -/
theorem map_integralPointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : ‖x‖ ≤ 1) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (integralPointLine x y hcurve hx).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - C x)
        (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  let P : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x y hx hcurve
  have hmap :=
    N13FiniteAffineTwoChart.map_integralPointTwoChartLine_affineIdeal P
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      _
  rw [hmap]
  simp [P,
    N13ProperCurveReduction.integralAffineLift,
    N13IntegralAffinePointSpread.curvePoint,
    N13IntegralAffinePointSpread.sexticY,
    N13EscapingDegreeOneSpread.pointY,
    SexticMumford.pointMumford,
    SexticMumford.affinePointMumford]

/-- Proper point line for an affine point escaping the integral affine
chart. -/
def escapingPointLine
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : x.valuation < 0) :
    TwoChartLine :=
  N13IntegralInfinityPointSpread.nonintegralPointLine
    x y hx hcurve

/-- The generic affine ideal of the escaping point line is the same standard
sextic point graph. -/
theorem map_escapingPointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : x.valuation < 0) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (escapingPointLine x y hcurve hx).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - C x)
        (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  exact
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint
      x y hx hcurve

/-- Valuation-independent proper line for any two-adic affine curve point. -/
def pointLine
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    TwoChartLine :=
  if hx : ‖x‖ ≤ 1 then
    integralPointLine x y hcurve hx
  else
    escapingPointLine x y hcurve
      (lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg x).not.mp hx))

/-- The valuation-independent point line always has the standard point graph
as its generic affine ideal. -/
theorem map_pointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pointLine x y hcurve).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - C x)
        (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  rw [pointLine]
  split
  · exact map_integralPointLine_affineIdeal x y hcurve _
  · exact map_escapingPointLine_affineIdeal x y hcurve _

/-- Tensor product of the proper lines attached to two affine points. -/
def pairLine
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    TwoChartLine :=
  N13TwoChartLineTensor.tensor
    (pointLine x₁ y₁ hcurve₁)
    (pointLine x₂ y₂ hcurve₂)

/-- The generic affine ideal of the pair line is the product of the two
standard point graph ideals. -/
theorem map_pairLine_affineIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pairLine x₁ y₁ x₂ y₂ hcurve₁ hcurve₂).affineIdeal =
      SexticMumford.mumfordIdeal Model
          (X - C x₁)
          (C (N13EscapingDegreeOneSpread.pointY x₁ y₁)) *
        SexticMumford.mumfordIdeal Model
          (X - C x₂)
          (C (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [pairLine, N13TwoChartLineTensor.map_tensor_affineIdeal,
    map_pointLine_affineIdeal, map_pointLine_affineIdeal]

/-- A quadratic Mumford graph with two distinct roots has a proper line
obtained by tensoring the two point lines on its secant divisor. -/
theorem exists_twoChartLine_of_distinct_split
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : Q₂)
    (hfactor :
      D.u = (X - C x₁) * (X - C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
  obtain ⟨hsextic₁, hsextic₂⟩ :=
    N13TwoChartLineTensor.mumford_eval_onCurve_of_split
      D x₁ x₂ hfactor
  let y₁ :=
    N13TwoChartLineTensor.goodY x₁ (D.v.eval x₁)
  let y₂ :=
    N13TwoChartLineTensor.goodY x₂ (D.v.eval x₂)
  have hcurve₁ :
      N13GoodModelTwo.AffineEquation x₁ y₁ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₁ (D.v.eval x₁) hsextic₁
  have hcurve₂ :
      N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₂ (D.v.eval x₂) hsextic₂
  let L :=
    pairLine x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  refine ⟨L, ?_⟩
  rw [map_pairLine_affineIdeal,
    N13TwoChartLineTensor.pointY_goodY,
    N13TwoChartLineTensor.pointY_goodY,
    N13TwoChartLineTensor.mumfordIdeal_eq_pointIdeal_mul_of_split
      D hdeg x₁ x₂ hfactor hneq]

/-- A quadratic Mumford graph with a repeated root has a proper line obtained
by tensor-squaring the point line on its tangent divisor. -/
theorem exists_twoChartLine_of_repeated_root
    (D : SexticMumford.Mumford Model)
    (x : Q₂)
    (hfactor : D.u = (X - C x) ^ 2) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
  have hfactorMul :
      D.u = (X - C x) * (X - C x) := by
    simpa only [pow_two] using hfactor
  obtain ⟨hsextic, _⟩ :=
    N13TwoChartLineTensor.mumford_eval_onCurve_of_split
      D x x hfactorMul
  let y :=
    N13TwoChartLineTensor.goodY x (D.v.eval x)
  have hcurve :
      N13GoodModelTwo.AffineEquation x y :=
    N13TwoChartLineTensor.goodY_onCurve
      x (D.v.eval x) hsextic
  let L :=
    pairLine x y x y hcurve hcurve
  refine ⟨L, ?_⟩
  rw [map_pairLine_affineIdeal,
    N13TwoChartLineTensor.pointY_goodY,
    ← pow_two,
    N13RepeatedRootSpread.pointIdeal_sq_eq_mumfordIdeal_of_square
      Model D x hfactor]

/-- Every balanced quadratic Mumford graph has an actual proper two-chart
line whose generic affine ideal is exactly the graph ideal. -/
theorem exists_twoChartLine
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
  by_cases hirr : Irreducible D.u
  · exact
      N13IrreducibleQuadraticSpread.exists_twoChartLine
        D hdeg hirr
  obtain ⟨c₁, c₂, hc₀, hc₁⟩ :=
    (D.u_monic.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp
      hirr
  let x₁ : Q₂ := -c₁
  let x₂ : Q₂ := -c₂
  have hfactor :
      D.u = (X - C x₁) * (X - C x₂) := by
    have hc₂ : D.u.coeff 2 = 1 := by
      calc
        D.u.coeff 2 = D.u.coeff D.u.natDegree :=
          congrArg D.u.coeff hdeg.symm
        _ = 1 := D.u_monic.coeff_natDegree
    simp only [x₁, x₂, C_neg, sub_neg_eq_add]
    rw [D.u.as_sum_range_C_mul_X_pow, hdeg,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hc₂, hc₀, hc₁, C_mul, C_add, C_1]
    ring
  by_cases hneq : x₁ ≠ x₂
  · exact
      exists_twoChartLine_of_distinct_split
        D hdeg x₁ x₂ hfactor hneq
  · have heq : x₂ = x₁ := by
      apply not_ne_iff.mp
      exact fun h ↦ hneq h.symm
    have hfactorSquare :
        D.u = (X - C x₁) ^ 2 := by
      rw [heq] at hfactor
      simpa only [pow_two] using hfactor
    exact
      exists_twoChartLine_of_repeated_root
        D x₁ hfactorSquare

/-- Every Padé-selected quadratic graph therefore has a proper two-chart line
with the exact normalized generic graph ideal. -/
theorem selectedGraph_has_twoChartLine
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 2) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).u
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).v := by
  let D :=
    N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford P
  have hDdeg : D.u.natDegree = 2 := by
    change
      ((N13ConstructedHalfIntegralSpread.normalizedGraphMumford
        P).u.map N13InfinityBaseChange.ratToQ₂).natDegree = 2
    rw [
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford
        P).u_monic.natDegree_map]
    exact
      (N13DegreeOneGraphPoint.normalizedGraphMumford_u_natDegree P).trans
        hdeg
  simpa [D] using
    (exists_twoChartLine D hDdeg)

end

end MazurProof.N13QuadraticTwoChartSpread


