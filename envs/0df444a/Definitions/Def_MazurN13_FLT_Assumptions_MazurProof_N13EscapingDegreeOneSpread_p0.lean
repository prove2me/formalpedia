-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EscapingDegreeOneSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13EscapingDegreeOneSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:38:20.078481+00:00
-- url     : https://prove2.me/theorems/f769256a-db8a-42fa-97f1-b01b56da1cb2
-- title:
--   FLT.Assumptions.MazurProof.N13EscapingDegreeOneSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13EscapingDegreeOneSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13EscapingDegreeOneSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffineTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityPointSpread_p0

set_option autoImplicit false




/-!
# The generic class of an escaping degree-one point line

For a nonintegral affine point `(x,y)` on the good two-adic model, the
infinity lift has coordinates `t=x⁻¹` and `v=t³y`.  The two-chart line
constructed from this integral point has affine graph

`(1-tX, Y-vX³)`.

After passing to the generic fibre, its first generator is a unit multiple
of `X-x`, and its completed-square ordinate agrees modulo `X-x` with the
standard sextic ordinate `2y+h(x)`.  Hence the generic fibre is exactly the
usual degree-one Mumford point ideal.

For an integral affine point, the finite-support closure theorem instead
contracts the overlap ideal onto the infinity chart.  Together the two
constructions give a proper two-chart line for every selected degree-one
graph.
-/

open Polynomial

namespace MazurProof.N13EscapingDegreeOneSpread

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type :=
  N13ProperCurveReduction.Q₂

abbrev PInf : Type :=
  N13IntegralInfinityPointSpread.IntegralInfinityPoint

abbrev Model : SexticMumford.Model Q₂ :=
  N13IntegralInfinityPointSpread.Model

def lift
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    PInf :=
  N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy

@[simp] theorem lift_t_coe
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    ((lift x y hx hxy).1.1 : Q₂) = x⁻¹ := by
  rfl

@[simp] theorem lift_v_coe
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    ((lift x y hx hxy).1.2 : Q₂) = x⁻¹ ^ 3 * y := by
  rfl

@[simp] theorem coeffMap_lift_t
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicCoordinateBaseChange.coeffMap
        (lift x y hx hxy).1.1 = x⁻¹ := by
  exact lift_t_coe x y hx hxy

@[simp] theorem coeffMap_lift_v
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicCoordinateBaseChange.coeffMap
        (lift x y hx hxy).1.2 = x⁻¹ ^ 3 * y := by
  exact lift_v_coe x y hx hxy

@[simp] theorem transportCoeffMap_lift_t
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicMumfordTransport.coeffMap
        (lift x y hx hxy).1.1 = x⁻¹ := by
  exact lift_t_coe x y hx hxy

@[simp] theorem transportCoeffMap_lift_v
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicMumfordTransport.coeffMap
        (lift x y hx hxy).1.2 = x⁻¹ ^ 3 * y := by
  exact lift_v_coe x y hx hxy

theorem x_ne_zero
    (x : Q₂) (hx : x.valuation < 0) :
    x ≠ 0 :=
  N13LocalDlogRegimes.nonintegral_coordinate_ne_zero x hx

@[simp] theorem x_mul_lift_t
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    x * ((lift x y hx hxy).1.1 : Q₂) = 1 := by
  rw [lift_t_coe, mul_inv_cancel₀ (x_ne_zero x hx)]

def pointY (x y : Q₂) : Q₂ :=
  2 * y + N13GoodModelTwo.h x

theorem pointY_onCurve
    (x y : Q₂)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    pointY x y ^ 2 = (N13Mumford.model Q₂).f.eval x := by
  have hs :=
    N13GoodModelTwo.completed_square_identity x y
  have hzero :
      y ^ 2 + N13GoodModelTwo.h x * y -
        N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hxy
  rw [hzero] at hs
  change
    pointY x y ^ 2 =
      (N13Mumford.f Q₂).eval x
  calc
    pointY x y ^ 2 =
        N13GoodModelTwo.completedSextic x := by
      simpa [pointY] using hs
    _ = (N13Mumford.f Q₂).eval x := by
      simp [N13GoodModelTwo.completedSextic, N13Mumford.f]

def curvePoint
    (x y : Q₂)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SexticMumford.CurvePoint Model :=
  .affine x (pointY x y) (pointY_onCurve x y hxy)

def genericU
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Q₂[X] :=
  N13TwoAdicCoordinateBaseChange.mapPoly
    (N13IntegralInfinityPointSpread.affineU
      (lift x y hx hxy))

def genericV
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Q₂[X] :=
  N13GoodSexticMumfordTransport.completedGraph
    (N13TwoAdicCoordinateBaseChange.mapPoly
      (N13IntegralInfinityPointSpread.affineV
        (lift x y hx hxy)))

/-- The nonmonic affine closure equation becomes a unit multiple of the
standard monic point equation on the generic fibre. -/
theorem genericU_eq_unit_mul
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    genericU x y hx hxy =
      C (-((lift x y hx hxy).1.1 : Q₂)) *
        (X - C x) := by
  simp [genericU, N13IntegralInfinityPointSpread.affineU,
    N13TwoAdicCoordinateBaseChange.mapPoly_apply,
    N13TwoAdicCoordinateBaseChange.coeffMap,
    transportCoeffMap_lift_t, lift_t_coe]
  have hc :
      C (x⁻¹) * C x = (1 : Q₂[X]) := by
    rw [← map_mul, inv_mul_cancel₀ (x_ne_zero x hx), map_one]
  linear_combination -hc

/-- The completed-square graph ordinate evaluates to the standard sextic
ordinate at the generic point. -/
theorem genericV_eval
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (genericV x y hx hxy).eval x = pointY x y := by
  simp [genericV, pointY,
    N13IntegralInfinityPointSpread.affineV,
    N13GoodSexticMumfordTransport.completedGraph,
    N13TwoAdicCoordinateBaseChange.mapPoly_apply,
    N13TwoAdicCoordinateBaseChange.coeffMap,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h, transportCoeffMap_lift_v]
  field_simp [x_ne_zero x hx]

theorem standardU_dvd_genericV_sub
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    X - C x ∣
      genericV x y hx hxy - C (pointY x y) := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := genericV x y hx hxy) (a := x)
  simpa [genericV_eval x y hx hxy] using h

private theorem span_pair_mul_left_unit
    {A : Type*} [CommRing A]
    (a x y : A) (ha : IsUnit a) :
    Ideal.span ({a * x, y} : Set A) =
      Ideal.span ({x, y} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mul_mem_left _
        a (Ideal.subset_span (by simp))
    · rw [hz]
      exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      obtain ⟨b, hab⟩ := isUnit_iff_exists_inv.mp ha
      have hba : b * a = 1 := by
        simpa [mul_comm] using hab
      have hax :
          a * x ∈ Ideal.span ({a * x, y} : Set A) :=
        Ideal.subset_span (by simp)
      have hbx := Ideal.mul_mem_left _ b hax
      simpa [← mul_assoc, hba] using hbx
    · rw [hz]
      exact Ideal.subset_span (by simp)

theorem genericU_scalar_isUnit
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    IsUnit
      (SexticMumford.xClass Model
        (C (-((lift x y hx hxy).1.1 : Q₂)))) := by
  have ht :
      -((lift x y hx hxy).1.1 : Q₂) ≠ 0 := by
    simp [lift_t_coe, x_ne_zero x hx]
  have hu : IsUnit (-((lift x y hx hxy).1.1 : Q₂)) :=
    isUnit_iff_ne_zero.mpr ht
  change
    IsUnit
      (algebraMap Q₂
        (SexticMumford.CoordinateRing Model)
        (-((lift x y hx hxy).1.1 : Q₂)))
  exact
    hu.map
      (algebraMap Q₂
        (SexticMumford.CoordinateRing Model))

theorem mumfordIdeal_genericU_eq_standardU
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SexticMumford.mumfordIdeal Model
        (genericU x y hx hxy)
        (genericV x y hx hxy) =
      SexticMumford.mumfordIdeal Model
        (X - C x) (genericV x y hx hxy) := by
  rw [SexticMumford.mumfordIdeal,
    genericU_eq_unit_mul,
    SexticMumford.xClass_mul]
  exact
    span_pair_mul_left_unit
      (SexticMumford.xClass Model
        (C (-((lift x y hx hxy).1.1 : Q₂))))
      (SexticMumford.xClass Model (X - C x))
      (SexticMumford.ySubClass Model
        (genericV x y hx hxy))
      (genericU_scalar_isUnit x y hx hxy)

/-- The generic fibre of the escaping two-chart line is exactly the
standard sextic point graph. -/
theorem genericIdeal_eq_standardPoint
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (lift x y hx hxy)) =
      SexticMumford.mumfordIdeal Model
        (X - C x) (C (pointY x y)) := by
  rw [N13IntegralInfinityPointSpread.map_affinePointIdeal]
  change
    SexticMumford.mumfordIdeal Model
        (genericU x y hx hxy)
        (genericV x y hx hxy) =
      _
  rw [mumfordIdeal_genericU_eq_standardU]
  exact
    N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
      (X - C x) (genericV x y hx hxy) (C (pointY x y))
      (standardU_dvd_genericV_sub x y hx hxy)

theorem genericIdeal_eq_pointMumford
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (lift x y hx hxy)) =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (curvePoint x y hxy)).u
        (SexticMumford.pointMumford Model
          (curvePoint x y hxy)).v := by
  simpa [curvePoint, SexticMumford.pointMumford,
    SexticMumford.affinePointMumford] using
      genericIdeal_eq_standardPoint x y hx hxy

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- The integral alternative produced by the selected degree-one graph is
realized by closing its literal monic point ideal on the infinity chart. -/
theorem selectedGraph_has_pointLine_of_integral_x
    (P : G)
    (x y : ℚ)
    (hcurve :
      y ^ 2 = (N13Mumford.model ℚ).f.eval x)
    (hgraph :
      N13ConstructedHalfIntegralSpread.normalizedGraphMumford P =
        SexticMumford.affinePointMumford
          (N13Mumford.model ℚ) x y hcurve)
    (hx :
      ‖N13ProperCurveReduction.ratToQ₂ x‖ ≤ 1) :
    ∃ L : N13IntegralInfinityPointSpread.TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).u
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).v := by
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
  let P₂ : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood
  have hsexticY :
      N13IntegralAffinePointSpread.sexticY P₂ =
        N13ProperCurveReduction.ratToQ₂ y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip x y)
    simpa [P₂, N13ProperCurveReduction.integralAffineLift,
      x₂, y₂, N13IntegralAffinePointSpread.sexticY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  have hu :
      (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
        P).u =
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P₂)).u := by
    change
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u.map
          N13InfinityBaseChange.ratToQ₂ =
        X - C (P₂.1.1 : Q₂)
    rw [hgraph]
    simp [SexticMumford.affinePointMumford, P₂,
      N13ProperCurveReduction.integralAffineLift, x₂]
  have hv :
      (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
        P).v =
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P₂)).v := by
    change
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).v.map
          N13InfinityBaseChange.ratToQ₂ =
        C (N13IntegralAffinePointSpread.sexticY P₂)
    rw [hgraph]
    simp [SexticMumford.affinePointMumford, hsexticY,
      N13ProperCurveReduction.ratToQ₂]
  let L :=
    N13FiniteAffineTwoChart.integralPointTwoChartLine P₂
  refine ⟨L, ?_⟩
  rw [N13FiniteAffineTwoChart.map_integralPointTwoChartLine_affineIdeal,
    ← hu, ← hv]

/-- The escaping alternative produced by the selected degree-one graph is
realized by an actual two-chart point line with exactly that generic graph
ideal. -/
theorem selectedGraph_has_pointLine_of_escape
    (P : G)
    (x y : ℚ)
    (hcurve :
      y ^ 2 = (N13Mumford.model ℚ).f.eval x)
    (hgraph :
      N13ConstructedHalfIntegralSpread.normalizedGraphMumford P =
        SexticMumford.affinePointMumford
          (N13Mumford.model ℚ) x y hcurve)
    (hx :
      (N13ProperCurveReduction.ratToQ₂ x).valuation < 0) :
    ∃ L : N13IntegralInfinityPointSpread.TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).u
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).v := by
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
  have hpointY :
      pointY x₂ y₂ =
        N13ProperCurveReduction.ratToQ₂ y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip x y)
    simpa [x₂, y₂, pointY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  have hu :
      (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
        P).u =
        (SexticMumford.pointMumford Model
          (curvePoint x₂ y₂ hgood)).u := by
    change
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u.map
          N13InfinityBaseChange.ratToQ₂ =
        X - C x₂
    rw [hgraph]
    simp [SexticMumford.affinePointMumford, x₂]
  have hv :
      (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
        P).v =
        (SexticMumford.pointMumford Model
          (curvePoint x₂ y₂ hgood)).v := by
    change
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).v.map
          N13InfinityBaseChange.ratToQ₂ =
        C (pointY x₂ y₂)
    rw [hgraph]
    simp [SexticMumford.affinePointMumford, hpointY,
      N13ProperCurveReduction.ratToQ₂]
  let L :=
    N13IntegralInfinityPointSpread.nonintegralPointLine
      x₂ y₂ hx hgood
  refine ⟨L, ?_⟩
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (lift x₂ y₂ hx hgood)) =
      _
  rw [genericIdeal_eq_pointMumford x₂ y₂ hx hgood,
    ← hu, ← hv]

/-- Thus the selected degree-one graph is either already represented by
the affine divisorial spread or by the explicit proper two-chart point
line. -/
theorem selectedGraph_isUnit_or_has_pointLine
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
      ∃ L : N13IntegralInfinityPointSpread.TwoChartLine,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal Model
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).u
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).v := by
  rcases
      N13IntegralAffinePointSpread.selectedGraph_isUnit_or_escapes_to_infinity
        P hdeg with hunit | ⟨x, y, hcurve, hgraph, hx⟩
  · exact Or.inl hunit
  · exact Or.inr
      (selectedGraph_has_pointLine_of_escape
        P x y hcurve hgraph hx)

/-- Every selected degree-one graph has an actual proper two-chart line
whose affine generic fibre is exactly the selected Mumford graph. -/
theorem selectedGraph_has_pointLine
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 1) :
    ∃ L : N13IntegralInfinityPointSpread.TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).u
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).v := by
  obtain ⟨x, y, hcurve, hgraph⟩ :=
    N13DegreeOneGraphPoint.exists_rationalAffinePoint_of_graphU_natDegree_eq_one
      P hdeg
  by_cases hx :
      ‖N13ProperCurveReduction.ratToQ₂ x‖ ≤ 1
  · exact
      selectedGraph_has_pointLine_of_integral_x
        P x y hcurve hgraph hx
  · have hval :
      (N13ProperCurveReduction.ratToQ₂ x).valuation < 0 :=
      lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg
          (N13ProperCurveReduction.ratToQ₂ x)).not.mp hx)
    exact
      selectedGraph_has_pointLine_of_escape
        P x y hcurve hgraph hval

end

end MazurProof.N13EscapingDegreeOneSpread


