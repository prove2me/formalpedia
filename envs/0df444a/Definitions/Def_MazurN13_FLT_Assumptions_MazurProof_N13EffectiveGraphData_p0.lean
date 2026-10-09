-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EffectiveGraphData_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13EffectiveGraphData_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:34:23.079104+00:00
-- url     : https://prove2.me/theorems/b55065a2-09f3-46d6-b7dc-00c38cb337bc
-- title:
--   FLT.Assumptions.MazurProof.N13EffectiveGraphData source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13EffectiveGraphData

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13EffectiveGraphData
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EffectiveInfinityRepair_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityPointPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13DegreeOneGraphPoint_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartTensorCompatibility_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Actual chart constructions for an effective degree-two semirepresentative.
The degree-one negative marking uses the negative infinity point line; the
constant negative marking uses two copies of that line. A repaired quadratic
uses the residual graph, rather than the original balanced graph.

The raw/class conclusions below are proved from the displayed constructors.
Their generic formal-branch marking and integral-comparison theorems are
separate obligations, not consequences asserted from affine saturation.
-/

namespace MazurProof.N13EffectiveGraphData

noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev SpecialPoint := N13SymmetricSquareTwo.CurvePoint
abbrev Pair := N13TwoChartSpecialRestriction.ChartPair

def pointPairData (L M : Line) (p q : SpecialPoint)
    (hL : N13TwoChartSpecialRestriction.restrict L = N13SpecialDivisorCharts.point p)
    (hM : N13TwoChartSpecialRestriction.restrict M = N13SpecialDivisorCharts.point q)
    (k : ℤ) : Data where
  charts := N13TwoChartLineTensor.tensor L M
  infinityOrder := k
  specialDivisor := s(p, q)
  special_affine := by
    rw [restrict_tensor, hL, hM, N13SpecialDivisorCharts.ofDivisor_mk]
  special_infinity := by
    rw [restrict_tensor, hL, hM, N13SpecialDivisorCharts.ofDivisor_mk]

def infinityLine (positive : Bool) : Line :=
  if positive then N13TwoChartLineTensor.infinityPlusLine
  else N13TwoChartLineTensor.infinityMinusLine

def infinityPoint (positive : Bool) : SpecialPoint :=
  if positive then N13InfinityLineSpecialRestriction.specialInfinityPlusPoint
  else N13InfinityLineSpecialRestriction.specialInfinityMinusPoint

theorem infinityLine_affineIdeal (b : Bool) : (infinityLine b).affineIdeal = ⊤ := by
  cases b <;> simp [infinityLine]

theorem restrict_infinityLine (b : Bool) :
    N13TwoChartSpecialRestriction.restrict (infinityLine b) =
      N13SpecialDivisorCharts.point (infinityPoint b) := by
  cases b
  · exact N13TwoChartSpecialRestriction.ChartPair.ext
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_affineIdeal
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_infinityIdeal
  · exact N13TwoChartSpecialRestriction.ChartPair.ext
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_affineIdeal
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_infinityIdeal

theorem infinityLine_saturated (b : Bool) : AffineVerticallySaturated (infinityLine b) :=
  affineVerticallySaturated_of_affineIdeal_eq_top _ (infinityLine_affineIdeal b)

/-- Degree-two divisors supported at the two actual infinity sections. -/
def infinityPairData (b c : Bool) : Data :=
  pointPairData (infinityLine b) (infinityLine c)
    (infinityPoint b) (infinityPoint c)
    (restrict_infinityLine b) (restrict_infinityLine c)
    ((if b then 1 else 0) + (if c then 1 else 0) - 2)

theorem infinityPairData_affineIdeal (b c : Bool) :
    (infinityPairData b c).charts.affineIdeal = ⊤ := by
  change (infinityLine b).affineIdeal * (infinityLine c).affineIdeal = ⊤
  rw [infinityLine_affineIdeal, infinityLine_affineIdeal, Ideal.top_mul]

theorem infinityPairData_saturated (b c : Bool) :
    AffineVerticallySaturated (infinityPairData b c).charts :=
  affineVerticallySaturated_of_affineIdeal_eq_top _ (infinityPairData_affineIdeal b c)

theorem restrict_affinePointLine (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartSpecialRestriction.restrict (N13QuadraticTwoChartSpread.pointLine x y h) =
      N13SpecialDivisorCharts.point (N13SplitQuadraticSpecialRestriction.reducedPoint x y h) :=
  N13TwoChartSpecialRestriction.ChartPair.ext
    (N13SplitQuadraticSpecialRestriction.restrict_pointLine_affineIdeal x y h)
    (N13SplitQuadraticSpecialRestriction.restrict_pointLine_infinityIdeal x y h)

/-- Choose which infinity section really occurs in the degree-two divisor.
The negative section gives mark -2 and the positive section gives mark -1. -/
def anchoredPointData (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (positive : Bool) : Data :=
  pointPairData (N13QuadraticTwoChartSpread.pointLine x y h) (infinityLine positive)
    (N13SplitQuadraticSpecialRestriction.reducedPoint x y h) (infinityPoint positive)
    (restrict_affinePointLine x y h) (restrict_infinityLine positive)
    (if positive then -1 else -2)

theorem anchoredPointData_map_affineIdeal (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (b : Bool) :
    Ideal.map N13IntegralFractionalHull.integralToRational
        (anchoredPointData x y h b).charts.affineIdeal =
      SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model
        (X - C x) (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  change Ideal.map N13IntegralFractionalHull.integralToRational
    ((N13QuadraticTwoChartSpread.pointLine x y h).affineIdeal *
      (infinityLine b).affineIdeal) = _
  rw [infinityLine_affineIdeal, Ideal.mul_top]
  exact N13QuadraticTwoChartSpread.map_pointLine_affineIdeal x y h

theorem anchoredPointData_saturated (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (b : Bool) :
    AffineVerticallySaturated (anchoredPointData x y h b).charts :=
  N13QuadraticTwoChartSpreadSaturation.affineVerticallySaturated_tensor _ _
    (N13QuadraticTwoChartSpreadSaturation.pointLine_affineVerticallySaturated x y h)
    (infinityLine_saturated b)

/-- The same affine graph in the existing balanced graph-constructor API.
Its temporary orientation is not used as the effective divisor's marking. -/
def balancedGraph (E : N13Mumford.SemiMumford Q₂) (hd : E.u.natDegree ≤ 2) :
    N13Mumford.Mumford Q₂ where
  u := E.u
  v := E.v
  nInf := 0
  u_monic := E.u_monic
  deg_u := hd
  v_reduced := E.v_reduced
  curve_dvd := E.curve_dvd
  infinity_bound := by simpa using hd

def withMark (R : Data) (k : ℤ) : Data := { R with infinityOrder := k }

theorem raw_eq_of_map_and_mark
    (E : N13Mumford.SemiMumford Q₂) (R : Data)
    (hmap : Ideal.map N13IntegralFractionalHull.integralToRational R.charts.affineIdeal =
      SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v)
    (hmark : R.infinityOrder = E.nInf - 1) :
    genericRaw R.charts R.infinityOrder =
      SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model E := by
  apply Prod.ext
  · change genericIdealUnit R.charts =
      SexticMumford.mumfordIdealUnit N13TwoChartPicardRealization.Model E
    apply Units.ext
    rw [coe_genericIdealUnit, SexticMumford.coe_mumfordIdealUnit]
    exact congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal)) hmap
  · change Multiplicative.ofAdd R.infinityOrder = Multiplicative.ofAdd (E.nInf - 1)
    rw [hmark]

/-- Every effective chamber graph has a degree-two chart realization.
For affine degrees zero and one, the actual infinity sections are selected
from the integer marking. In degree two, use the residual graph's existing
quadratic closure and mark it -2. This theorem does not claim separatedness. -/
theorem exists_effective_data
    (E : N13Mumford.SemiMumford Q₂) (hE : EffectiveChamber E) :
    ∃ R : Data, genericRaw R.charts R.infinityOrder =
        SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model E ∧
      AffineVerticallySaturated R.charts := by
  have hd := hE.1
  interval_cases he : E.u.natDegree
  · have hu : E.u = 1 := Polynomial.eq_one_of_monic_natDegree_zero E.u_monic he
    have hv : E.v = 0 := by
      have hh := E.v_reduced
      rw [hu] at hh
      simpa using hh.symm
    have hnlo := hE.2.1
    have hnhi : E.nInf ≤ 1 - (E.u.natDegree : ℤ) := by have := hE.2.2; omega
    rw [he] at hnhi
    norm_num at hnhi
    have hm (b c : Bool) :
        Ideal.map N13IntegralFractionalHull.integralToRational
            (infinityPairData b c).charts.affineIdeal =
          SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v := by
      rw [infinityPairData_affineIdeal, Ideal.map_top, hu, hv]
      exact (SexticMumford.zero_mumfordIdeal N13TwoChartPicardRealization.Model).symm
    interval_cases hn : E.nInf
    · refine ⟨infinityPairData false false, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _⟩
      change (-2 : ℤ) = E.nInf - 1
      omega
    · refine ⟨infinityPairData false true, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _⟩
      change (-1 : ℤ) = E.nInf - 1
      omega
    · refine ⟨infinityPairData true true, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _⟩
      change (0 : ℤ) = E.nInf - 1
      omega
  · let D := balancedGraph E hE.1
    obtain ⟨x, y, hc, hD⟩ :=
      SexticMumford.exists_affinePoint_of_natDegree_eq_one
        N13TwoChartPicardRealization.Model D he rfl
    have hu : E.u = X - C x := congrArg (fun D => D.u) hD
    have hv : E.v = C y := congrArg (fun D => D.v) hD
    let hg := N13TwoChartLineTensor.goodY_onCurve x y hc
    have hm (b : Bool) :
        Ideal.map N13IntegralFractionalHull.integralToRational
            (anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg b).charts.affineIdeal =
          SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v := by
      rw [anchoredPointData_map_affineIdeal, N13TwoChartLineTensor.pointY_goodY, hu, hv]
    have hnlo := hE.2.1
    have hnhi : E.nInf ≤ 1 - (E.u.natDegree : ℤ) := by have := hE.2.2; omega
    rw [he] at hnhi
    norm_num at hnhi
    interval_cases hn : E.nInf
    · refine ⟨anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg false,
        raw_eq_of_map_and_mark E _ (hm _) ?_, anchoredPointData_saturated _ _ _ _⟩
      change (-2 : ℤ) = E.nInf - 1
      omega
    · refine ⟨anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg true,
        raw_eq_of_map_and_mark E _ (hm _) ?_, anchoredPointData_saturated _ _ _ _⟩
      change (-1 : ℤ) = E.nInf - 1
      omega
  · let D := balancedGraph E hE.1
    obtain ⟨R, hraw, _, hs⟩ := N13QuadraticPicardRealization.exists_saturated_data D he
    have hm := map_affineIdeal_eq_of_genericRaw_eq_mumfordRaw R.charts R.infinityOrder D hraw
    refine ⟨withMark R (E.nInf - 1), raw_eq_of_map_and_mark E _ hm rfl, hs⟩

/-- Apply the concrete Cantor repair before choosing any effective chart
geometry. Thus the problematic balanced branches use the residual graph. -/
theorem exists_repaired_data (D : N13Mumford.Mumford Q₂) :
    ∃ R : Data,
      genericRaw R.charts R.infinityOrder =
        SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model (repair D) ∧
      R.toGenericPic = SexticMumford.classOf N13TwoChartPicardRealization.Model
        (N13Infinity.positiveInfinityOrder Q₂) D ∧
      AffineVerticallySaturated R.charts := by
  obtain ⟨R, hraw, hs⟩ := exists_effective_data (repair D) (repair_effective D)
  refine ⟨R, hraw, ?_, hs⟩
  change genericClass R.charts R.infinityOrder = _
  unfold genericClass
  rw [hraw]
  exact repair_class D

end
end MazurProof.N13EffectiveGraphData


