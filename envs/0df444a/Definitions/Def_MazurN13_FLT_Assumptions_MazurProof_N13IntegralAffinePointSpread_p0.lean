-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralAffinePointSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralAffinePointSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:13:45.213563+00:00
-- url     : https://prove2.me/theorems/a743c0c7-7737-423f-a237-3d25faede207
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralAffinePointSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralAffinePointSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralAffinePointSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13DegreeOneGraphPoint_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphSpread_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ProperCurveReduction_p0

set_option autoImplicit false




/-!
# Integral spreads of affine N13 points

An integral point of the good two-adic affine chart gives the monic linear
generalized Mumford graph `(X-x, y)`.  Its curve equation follows by the
factor theorem.  Completion of the square identifies its generic sextic
graph with the standard Mumford graph of the corresponding curve point.

The semigraph contraction theorem and the global Jacobian frame therefore
make the canonical divisorial spread invertible.  This closes the affine
half of the proper degree-one branch without local factoriality.
-/

open Polynomial

namespace MazurProof.N13IntegralAffinePointSpread

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13ProperCurveReduction.Z₂

abbrev Q₂ : Type :=
  N13ProperCurveReduction.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

abbrev IntegralPoint : Type :=
  {p : R₂ × R₂ //
    N13GoodModelTwo.AffineEquation p.1 p.2}

abbrev IntegralSemiMumford : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂

def pointU (P : IntegralPoint) : R₂[X] :=
  X - C P.1.1

def pointV (P : IntegralPoint) : R₂[X] :=
  C P.1.2

def pointResidual (P : IntegralPoint) : R₂[X] :=
  pointV P ^ 2 +
    N13GeneralizedMumfordIntegral.hPoly (R := R₂) * pointV P -
    N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)

theorem pointResidual_eval (P : IntegralPoint) :
    (pointResidual P).eval P.1.1 = 0 := by
  simpa [pointResidual, pointV,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly,
    N13GoodModelTwo.AffineEquation,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    sub_eq_zero] using P.2

theorem pointU_dvd_pointResidual (P : IntegralPoint) :
    pointU P ∣ pointResidual P := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := pointResidual P) (a := P.1.1)
  simpa [pointU, pointResidual_eval] using h

def pointW (P : IntegralPoint) : R₂[X] :=
  Classical.choose (pointU_dvd_pointResidual P)

theorem pointResidual_eq_mul_pointW (P : IntegralPoint) :
    pointResidual P = pointU P * pointW P :=
  Classical.choose_spec (pointU_dvd_pointResidual P)

/-- The literal monic linear integral graph of an affine integral point. -/
def integralSemiGraph (P : IntegralPoint) :
    IntegralSemiMumford where
  u := pointU P
  v := pointV P
  w := pointW P
  u_monic := monic_X_sub_C P.1.1
  curve_eq := pointResidual_eq_mul_pointW P

/-- The standard sextic ordinate obtained by completing the square. -/
def sexticY (P : IntegralPoint) : Q₂ :=
  2 * (P.1.2 : Q₂) +
    N13GoodModelTwo.h (P.1.1 : Q₂)

theorem goodEquation_Q₂ (P : IntegralPoint) :
    N13GoodModelTwo.AffineEquation
      (P.1.1 : Q₂) (P.1.2 : Q₂) := by
  simpa [N13GoodModelTwo.AffineEquation,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs] using
    congrArg (algebraMap R₂ Q₂) P.2

theorem sexticY_onCurve (P : IntegralPoint) :
    sexticY P ^ 2 =
      (N13Mumford.model Q₂).f.eval (P.1.1 : Q₂) := by
  have hs :=
    N13GoodModelTwo.completed_square_identity
      (P.1.1 : Q₂) (P.1.2 : Q₂)
  have hzero :
      (P.1.2 : Q₂) ^ 2 +
          N13GoodModelTwo.h (P.1.1 : Q₂) * (P.1.2 : Q₂) -
        N13GoodModelTwo.rhs (P.1.1 : Q₂) = 0 :=
    sub_eq_zero.mpr (goodEquation_Q₂ P)
  rw [hzero] at hs
  change
    sexticY P ^ 2 =
      (N13Mumford.f Q₂).eval (P.1.1 : Q₂)
  calc
    sexticY P ^ 2 =
        N13GoodModelTwo.completedSextic (P.1.1 : Q₂) := by
      simpa [sexticY] using hs
    _ = (N13Mumford.f Q₂).eval (P.1.1 : Q₂) := by
      simp [N13GoodModelTwo.completedSextic, N13Mumford.f]

def curvePoint (P : IntegralPoint) :
    SexticMumford.CurvePoint Model :=
  .affine (P.1.1 : Q₂) (sexticY P) (sexticY_onCurve P)

@[simp] theorem sexticSemi_u (P : IntegralPoint) :
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi
      (integralSemiGraph P) 0).u =
      X - C (P.1.1 : Q₂) := by
  simp [integralSemiGraph, pointU,
    N13TwoAdicMumfordTransport.mapPoly,
    N13TwoAdicMumfordTransport.coeffMap]

@[simp] theorem sexticSemi_v (P : IntegralPoint) :
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi
      (integralSemiGraph P) 0).v =
      C (sexticY P) := by
  rw [N13TwoAdicMumfordTransport.sexticSemiOfSemi_v]
  simp [integralSemiGraph, pointU, pointV,
    N13TwoAdicMumfordTransport.mapPoly,
    N13TwoAdicMumfordTransport.coeffMap,
    N13GoodSexticMumfordTransport.reducedCompletedGraph,
    N13GoodSexticMumfordTransport.completedGraph,
    mod_X_sub_C_eq_C_eval, sexticY,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]

/-- The transported integral linear graph is exactly the sextic Mumford
graph of the corresponding two-adic curve point. -/
theorem sexticSemiIdeal_eq_pointIdeal (P : IntegralPoint) :
    N13IntegralGraphContraction.sexticSemiIdeal
        (integralSemiGraph P) 0 =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model (curvePoint P)).u
        (SexticMumford.pointMumford Model (curvePoint P)).v := by
  unfold N13IntegralGraphContraction.sexticSemiIdeal
  rw [sexticSemi_u, sexticSemi_v]
  rfl

/-- The literal integral affine graph ideal of an integral point. -/
def pointIdeal (P : IntegralPoint) :
    Ideal N13IntegralGraphJacobian.IntegralRing :=
  N13GeneralizedMumfordIntegral.mumfordIdeal
    (integralSemiGraph P).u (integralSemiGraph P).v

/-- The affine point graph is already an invertible integral fractional
ideal; no divisorial hull is needed for tensor products of point spreads. -/
theorem pointIdeal_isUnit (P : IntegralPoint) :
    IsUnit
      (pointIdeal P :
        N13IntegralGraphJacobian.IntegralFractionalIdeal) := by
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      (integralSemiGraph P)

/-- The generic fibre of the literal integral affine point ideal is the
standard sextic point graph. -/
theorem map_pointIdeal (P : IntegralPoint) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pointIdeal P) =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model (curvePoint P)).u
        (SexticMumford.pointMumford Model (curvePoint P)).v := by
  rw [pointIdeal,
    N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemiOfSemi]
  exact sexticSemiIdeal_eq_pointIdeal P

/-- Every affine integral point supplies an invertible canonical
divisorial spread of its generic sextic graph. -/
theorem divisorialHull_pointIdeal_isUnit (P : IntegralPoint) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (SexticMumford.mumfordIdeal Model
          (SexticMumford.pointMumford Model (curvePoint P)).u
          (SexticMumford.pointMumford Model (curvePoint P)).v)) := by
  rw [← sexticSemiIdeal_eq_pointIdeal]
  exact
    N13IntegralGraphSpread.divisorialHull_sexticSemiIdeal_isUnit
      (integralSemiGraph P) 0

/-! ## The integral branch of the selected degree-one Padé graph -/

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- If the rational affine point underlying a selected degree-one graph
has integral two-adic `x`-coordinate, its normalized graph has an
invertible canonical spread. -/
theorem selectedGraph_divisorialHull_isUnit_of_integral_x
    (P : G)
    (_hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 1)
    (x y : ℚ)
    (hcurve :
      y ^ 2 = (N13Mumford.model ℚ).f.eval x)
    (hgraph :
      N13ConstructedHalfIntegralSpread.normalizedGraphMumford P =
        SexticMumford.affinePointMumford
          (N13Mumford.model ℚ) x y hcurve)
    (hx :
      ‖N13ProperCurveReduction.ratToQ₂ x‖ ≤ 1) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (SexticMumford.mumfordIdeal Model
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).u
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).v)) := by
  have hcurve' :
      N13CurveModel.C13SexticEq x y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  let x₂ : Q₂ :=
    N13ProperCurveReduction.ratToQ₂ x
  let y₂ : Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY x y)
  have hgood :
      N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hcurve'
  let L : IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood
  have hsexticY :
      sexticY L =
        N13ProperCurveReduction.ratToQ₂ y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip x y)
    simpa [L, N13ProperCurveReduction.integralAffineLift,
      x₂, y₂, sexticY, N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  have hu :
      (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
        P).u =
        (SexticMumford.pointMumford Model (curvePoint L)).u := by
    change
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u.map
          N13InfinityBaseChange.ratToQ₂ =
        X - C (L.1.1 : Q₂)
    rw [hgraph]
    simp [SexticMumford.affinePointMumford, L,
      N13ProperCurveReduction.integralAffineLift, x₂]
  have hv :
      (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
        P).v =
        (SexticMumford.pointMumford Model (curvePoint L)).v := by
    change
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).v.map
          N13InfinityBaseChange.ratToQ₂ =
        C (sexticY L)
    rw [hgraph]
    simp [SexticMumford.affinePointMumford, hsexticY,
      N13ProperCurveReduction.ratToQ₂]
  rw [hu, hv]
  exact divisorialHull_pointIdeal_isUnit L

/-- The only degree-one case not closed by the affine semigraph is the
genuine proper escape to the infinity chart. -/
theorem selectedGraph_isUnit_or_escapes_to_infinity
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 1) :
    IsUnit
        (N13IntegralFractionalHull.divisorialHull
          (SexticMumford.mumfordIdeal Model
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).u
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).v)) ∨
      ∃ x y : ℚ, ∃ hcurve :
          y ^ 2 = (N13Mumford.model ℚ).f.eval x,
        N13ConstructedHalfIntegralSpread.normalizedGraphMumford P =
            SexticMumford.affinePointMumford
              (N13Mumford.model ℚ) x y hcurve ∧
          (N13ProperCurveReduction.ratToQ₂ x).valuation < 0 := by
  obtain ⟨x, y, hcurve, hgraph⟩ :=
    N13DegreeOneGraphPoint.exists_rationalAffinePoint_of_graphU_natDegree_eq_one
      P hdeg
  by_cases hx :
      ‖N13ProperCurveReduction.ratToQ₂ x‖ ≤ 1
  · exact Or.inl
      (selectedGraph_divisorialHull_isUnit_of_integral_x
        P hdeg x y hcurve hgraph hx)
  · refine Or.inr ⟨x, y, hcurve, hgraph, ?_⟩
    exact lt_of_not_ge
      ((Padic.norm_le_one_iff_val_nonneg
        (N13ProperCurveReduction.ratToQ₂ x)).not.mp hx)

end

end MazurProof.N13IntegralAffinePointSpread


