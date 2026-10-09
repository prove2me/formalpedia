-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SplitQuadraticSpecialRestriction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SplitQuadraticSpecialRestriction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:06:17.445476+00:00
-- url     : https://prove2.me/theorems/523086bf-a89c-4c10-88a6-c214c4cc83b5
-- title:
--   FLT.Assumptions.MazurProof.N13SplitQuadraticSpecialRestriction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SplitQuadraticSpecialRestriction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SplitQuadraticSpecialRestriction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffinePointInfinityClosure_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpread_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpreadSaturation_p0

set_option autoImplicit false




/-!
# Special restriction of split quadratic N13 lines

The valuation-independent point line chooses the ordinary affine closure for
an integral horizontal coordinate and the infinity-chart closure for an
escaping coordinate.  Both branches have already been identified with the
canonical chart pair of their reduced special point.

This file packages that case split once.  Tensoring the resulting point-line
equalities then identifies every split quadratic line, including a repeated
root, with the canonical chart pair of its literal degree-two special
divisor.  These are equalities of both chart ideals; no Picard orientation is
inferred from them.
-/

open scoped Sym2

namespace MazurProof.N13SplitQuadraticSpecialRestriction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The two-adic coefficient field of the good N13 model. -/
abbrev Q₂ : Type :=
  N13QuadraticTwoChartSpread.Q₂

/-- Completed points of the six-point special fibre. -/
abbrev SpecialPoint : Type :=
  N13SpecialDivisorCharts.CurvePoint

/-- Proper reduction of an arbitrary two-adic affine point.

An integral horizontal coordinate is reduced on the ordinary affine chart.
Otherwise its inverse coordinate is integral and the point reduces on the
infinity chart.  The two branches exactly mirror the definition of
`N13QuadraticTwoChartSpread.pointLine`. -/
def reducedPoint
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    SpecialPoint :=
  if hx : ‖x‖ ≤ 1 then
    N13IntegralAffinePointSpecialClass.reducedPoint
      (N13ProperCurveReduction.integralAffineLift x y hx hcurve)
  else
    N13ProperCurveReduction.reduceNonintegralAffine
      x y
      (lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg x).not.mp hx))
      hcurve

/-- Restriction of the valuation-independent point line on the ordinary
affine chart is the canonical ideal of its properly reduced point. -/
theorem restrict_pointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x y hcurve)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (reducedPoint x y hcurve)).affineIdeal := by
  rw [N13QuadraticTwoChartSpread.pointLine, reducedPoint]
  split
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_affineIdeal _
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_affineIdeal
        x y _ hcurve

/-- Restriction of the same point line on the infinity chart is the canonical
ideal of the same properly reduced point. -/
theorem restrict_pointLine_infinityIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x y hcurve)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (reducedPoint x y hcurve)).infinityIdeal := by
  rw [N13QuadraticTwoChartSpread.pointLine, reducedPoint]
  split
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_infinityIdeal _
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_infinityIdeal
        x y _ hcurve

/-- The literal degree-two special divisor obtained by reducing two affine
points, with multiplicity retained when the two points coincide. -/
def reducedPairDivisor
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    N13SpecialDivisorCharts.EffectiveDivisorTwo :=
  s(reducedPoint x₁ y₁ hcurve₁, reducedPoint x₂ y₂ hcurve₂)

/-- The affine restriction of a tensor product of two point lines equals the
canonical affine ideal of the reduced degree-two divisor. -/
theorem restrict_pairLine_affineIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal := by
  rw [N13QuadraticTwoChartSpread.pairLine,
    N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
    reducedPairDivisor, N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x₁ y₁ hcurve₁)).affineIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13QuadraticTwoChartSpread.pointLine x₂ y₂ hcurve₂)).affineIdeal =
      (N13SpecialDivisorCharts.point
          (reducedPoint x₁ y₁ hcurve₁)).affineIdeal *
        (N13SpecialDivisorCharts.point
          (reducedPoint x₂ y₂ hcurve₂)).affineIdeal
  rw [restrict_pointLine_affineIdeal, restrict_pointLine_affineIdeal]

/-- The infinity restriction of a tensor product of two point lines equals
the canonical infinity ideal of the same reduced degree-two divisor. -/
theorem restrict_pairLine_infinityIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal := by
  rw [N13QuadraticTwoChartSpread.pairLine,
    N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
    reducedPairDivisor, N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x₁ y₁ hcurve₁)).infinityIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13QuadraticTwoChartSpread.pointLine x₂ y₂ hcurve₂)).infinityIdeal =
      (N13SpecialDivisorCharts.point
          (reducedPoint x₁ y₁ hcurve₁)).infinityIdeal *
        (N13SpecialDivisorCharts.point
          (reducedPoint x₂ y₂ hcurve₂)).infinityIdeal
  rw [restrict_pointLine_infinityIdeal, restrict_pointLine_infinityIdeal]

/-- A quadratic Mumford graph with two distinct roots has a proper line whose
generic ideal is the graph ideal and whose two special chart ideals are the
canonical ideals of the reduced secant divisor.

The special divisor is returned explicitly because its two reduced points
depend on the valuations of the roots.  The final field retains vertical
saturation of the affine lattice. -/
theorem exists_saturated_twoChartLine_and_specialDivisor_of_distinct_split
    (D : SexticMumford.Mumford N13QuadraticTwoChartSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : Q₂)
    (hfactor : D.u = (Polynomial.X - Polynomial.C x₁) *
      (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ L : N13QuadraticTwoChartSpread.TwoChartLine,
      ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal
            N13QuadraticTwoChartSpread.Model D.u D.v ∧
        (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal ∧
        (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal ∧
        N13TwoChartPicardRealization.AffineVerticallySaturated L := by
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
    N13QuadraticTwoChartSpread.pairLine
      x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  let Δ :=
    reducedPairDivisor x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  refine ⟨L, Δ, ?_, ?_, ?_, ?_⟩
  · dsimp only [L]
    rw [N13QuadraticTwoChartSpread.map_pairLine_affineIdeal,
      N13TwoChartLineTensor.pointY_goodY,
      N13TwoChartLineTensor.pointY_goodY,
      N13TwoChartLineTensor.mumfordIdeal_eq_pointIdeal_mul_of_split
        D hdeg x₁ x₂ hfactor hneq]
  · exact
      restrict_pairLine_affineIdeal
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact
      restrict_pairLine_infinityIdeal
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact
      N13QuadraticTwoChartSpreadSaturation.pairLine_affineVerticallySaturated
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂

/-- Forgetting vertical saturation recovers the original split-special
realization interface. -/
theorem exists_twoChartLine_and_specialDivisor_of_distinct_split
    (D : SexticMumford.Mumford N13QuadraticTwoChartSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : Q₂)
    (hfactor : D.u = (Polynomial.X - Polynomial.C x₁) *
      (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ L : N13QuadraticTwoChartSpread.TwoChartLine,
      ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal
            N13QuadraticTwoChartSpread.Model D.u D.v ∧
        (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal ∧
        (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal := by
  obtain ⟨L, Δ, hmap, haffine, hinfinity, _⟩ :=
    exists_saturated_twoChartLine_and_specialDivisor_of_distinct_split
      D hdeg x₁ x₂ hfactor hneq
  exact ⟨L, Δ, hmap, haffine, hinfinity⟩

/-- A quadratic Mumford graph with a repeated root has a proper tensor-square
line whose generic ideal is the tangent graph and whose special restriction
is the doubled reduced point.

The multiplicity is retained by the symmetric-square divisor even if the
point changes charts after reduction.  The final field retains vertical
saturation of the tangent-square affine lattice. -/
theorem exists_saturated_twoChartLine_and_specialDivisor_of_repeated_root
    (D : SexticMumford.Mumford N13QuadraticTwoChartSpread.Model)
    (x : Q₂)
    (hfactor : D.u = (Polynomial.X - Polynomial.C x) ^ 2) :
    ∃ L : N13QuadraticTwoChartSpread.TwoChartLine,
      ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal
            N13QuadraticTwoChartSpread.Model D.u D.v ∧
        (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal ∧
        (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal ∧
        N13TwoChartPicardRealization.AffineVerticallySaturated L := by
  have hfactorMul :
      D.u = (Polynomial.X - Polynomial.C x) *
        (Polynomial.X - Polynomial.C x) := by
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
    N13QuadraticTwoChartSpread.pairLine
      x y x y hcurve hcurve
  let Δ :=
    reducedPairDivisor x y x y hcurve hcurve
  refine ⟨L, Δ, ?_, ?_, ?_, ?_⟩
  · dsimp only [L]
    rw [N13QuadraticTwoChartSpread.map_pairLine_affineIdeal,
      N13TwoChartLineTensor.pointY_goodY, ← pow_two,
      N13RepeatedRootSpread.pointIdeal_sq_eq_mumfordIdeal_of_square
        N13QuadraticTwoChartSpread.Model D x hfactor]
  · exact
      restrict_pairLine_affineIdeal
        x y x y hcurve hcurve
  · exact
      restrict_pairLine_infinityIdeal
        x y x y hcurve hcurve
  · exact
      N13QuadraticTwoChartSpreadSaturation.pairLine_affineVerticallySaturated
        x y x y hcurve hcurve

/-- Forgetting vertical saturation recovers the original repeated-root
special-realization interface. -/
theorem exists_twoChartLine_and_specialDivisor_of_repeated_root
    (D : SexticMumford.Mumford N13QuadraticTwoChartSpread.Model)
    (x : Q₂)
    (hfactor : D.u = (Polynomial.X - Polynomial.C x) ^ 2) :
    ∃ L : N13QuadraticTwoChartSpread.TwoChartLine,
      ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal
            N13QuadraticTwoChartSpread.Model D.u D.v ∧
        (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal ∧
        (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal := by
  obtain ⟨L, Δ, hmap, haffine, hinfinity, _⟩ :=
    exists_saturated_twoChartLine_and_specialDivisor_of_repeated_root
      D x hfactor
  exact ⟨L, Δ, hmap, haffine, hinfinity⟩

end

end MazurProof.N13SplitQuadraticSpecialRestriction


