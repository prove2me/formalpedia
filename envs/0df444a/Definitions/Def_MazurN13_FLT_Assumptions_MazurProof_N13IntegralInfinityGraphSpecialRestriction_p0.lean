-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSpecialRestriction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSpecialRestriction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:42:38.232558+00:00
-- url     : https://prove2.me/theorems/3fed3b60-a9be-4297-95e5-1d3e1c03a403
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSpecialRestriction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSpecialRestriction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSpecialRestriction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityGraphDivisorCharts_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartSpecialRestriction_p0

set_option autoImplicit false




/-!
# Special restriction of integral infinity graph divisors

A bounded monic quadratic graph on the integral infinity chart has a
weighted-reflection closure on the affine chart.  Coefficient reduction
commutes with both graph generators and all three weighted reflections.

The reduced monic infinity polynomial splits over `F₂`.  Its four possible
unordered root patterns explicitly determine the reflected affine ideal:
roots at `t = 0` disappear from the affine chart, roots at `t = 1` become
the point `x = 1`, and a repeated `t = 1` root retains its multiplicity
through the characteristic-two tangent-ideal identity.  Consequently the
two reduced chart ideals are exactly the canonical chart pair of the
completed special root divisor.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The residue field on both special charts. -/
abbrev K := N13SpecialInfinityChart.K

theorem eval_one_reflect
    (p : K[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    (p.reflect n).eval 1 = p.eval 1 := by
  letI : Invertible (1 : K) := invertibleOne
  simpa using
    (Polynomial.eval₂_reflect_mul_pow
      (RingHom.id K) (1 : K) n p hp)

/-- Weighted reflection sends two finite infinity roots to their reciprocal
affine factors. -/
theorem reflect_rootPolynomial_mk (a b : K) :
    (N13SpecialGraphDivisorCharts.rootPolynomial s(a, b)).reflect 2 =
      (1 - C a * X) * (1 - C b * X) := by
  rw [N13SpecialGraphDivisorCharts.rootPolynomial_mk,
    reflect_mul (F := 1) (G := 1)
      (X - C a) (X - C b) (by compute_degree) (by compute_degree),
    reflect_sub, reflect_sub]
  simp

/-- In characteristic two the reciprocal linear factor `1-X` equals
`X-1`. -/
@[simp] theorem one_sub_X_eq_X_sub_one :
    (1 : K[X]) - X = X - 1 := by
  rw [ZModModule.sub_eq_add, ZModModule.sub_eq_add, add_comm]

theorem reflected_affineIdeal_eq_rootAffineIdeal_of_rootPolynomial
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (z : Sym2 K)
    (hv : D.v.natDegree ≤ 3)
    (hfactor :
      D.u =
        N13SpecialGraphDivisorCharts.rootPolynomial z)
    (haff :
      D.v.reflect 3 ^ 2 +
          N13GoodCoordinateRingTwo.hPoly * D.v.reflect 3 -
          N13GoodCoordinateRingTwo.rhsPoly =
        D.u.reflect 2 * D.w.reflect 4) :
    N13GoodCoordinateRingTwo.mumfordIdeal
        (D.u.reflect 2) (D.v.reflect 3) =
      N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal D
        z := by
  induction z using Sym2.ind with
  | _ a b =>
      rcases
          N13GoodModelTwo.fixedTwo_eq_zero_or_one
            a (ZMod.pow_card a) with rfl | rfl <;>
        rcases
          N13GoodModelTwo.fixedTwo_eq_zero_or_one
            b (ZMod.pow_card b) with rfl | rfl
      · have hu : D.u.reflect 2 = 1 := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp
        rw [hu, N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        simp
        apply (Ideal.eq_top_iff_one _).mpr
        exact
          N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
            1 (D.v.reflect 3)
      · have hu :
            D.u.reflect 2 = X - C (1 : K) := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp [one_sub_X_eq_X_sub_one]
        have hv1 :
            (D.v.reflect 3).eval 1 = D.v.eval 1 :=
          eval_one_reflect D.v 3 hv
        have hdiv :
            X - C (1 : K) ∣
              D.v.reflect 3 - C (D.v.eval 1) := by
          simpa [hv1] using
            (X_sub_C_dvd_sub_C_eval
              (p := D.v.reflect 3) (a := (1 : K)))
        rw [hu,
          N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        simp
        simpa [N13GoodCoordinateRingTwo.mumfordIdeal,
          GeneralizedGraphIdealCore.graphIdeal,
          N13GoodCoordinateRingTwo.ySubClass,
          GeneralizedGraphIdealCore.ySubClass] using
          (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
            N13GoodCoordinateRingTwo.xClassHom
            N13GoodCoordinateRingTwo.yClass
            (X - C (1 : K))
            (C (D.v.eval 1)) (D.v.reflect 3) hdiv)
      · have hu :
            D.u.reflect 2 = X - C (1 : K) := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp [one_sub_X_eq_X_sub_one]
        have hv1 :
            (D.v.reflect 3).eval 1 = D.v.eval 1 :=
          eval_one_reflect D.v 3 hv
        have hdiv :
            X - C (1 : K) ∣
              D.v.reflect 3 - C (D.v.eval 1) := by
          simpa [hv1] using
            (X_sub_C_dvd_sub_C_eval
              (p := D.v.reflect 3) (a := (1 : K)))
        rw [hu,
          N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        simp
        simpa [N13GoodCoordinateRingTwo.mumfordIdeal,
          GeneralizedGraphIdealCore.graphIdeal,
          N13GoodCoordinateRingTwo.ySubClass,
          GeneralizedGraphIdealCore.ySubClass] using
          (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
            N13GoodCoordinateRingTwo.xClassHom
            N13GoodCoordinateRingTwo.yClass
            (X - C (1 : K))
            (C (D.v.eval 1)) (D.v.reflect 3) hdiv)
      · have hu :
            D.u.reflect 2 = (X - C (1 : K)) ^ 2 := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp [one_sub_X_eq_X_sub_one, pow_two]
        have huMonic : (D.u.reflect 2).Monic := by
          rw [hu]
          exact (monic_X_sub_C (1 : K)).pow 2
        have hbezout :
            ∃ a b c : K[X],
              a * D.u.reflect 2 +
                  b * (2 * D.v.reflect 3 +
                    N13GoodCoordinateRingTwo.hPoly) +
                  c * D.w.reflect 4 =
                1 := by
          refine ⟨-X, 1, 0, ?_⟩
          rw [hu]
          have htwo : (2 : K[X]) = 0 :=
            CharP.cast_eq_zero (K[X]) 2
          rw [htwo, zero_mul, zero_add]
          simp [N13GoodCoordinateRingTwo.hPoly]
          linear_combination X ^ 2 * htwo
        let A : N13GoodCoordinateRingTwo.SemiMumford :=
          ⟨D.u.reflect 2, D.v.reflect 3, D.w.reflect 4,
            huMonic, haff, hbezout⟩
        have hv1 :
            (D.v.reflect 3).eval 1 = D.v.eval 1 :=
          eval_one_reflect D.v 3 hv
        rw [N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        rw [← hv1]
        simpa [A, pow_two] using
          N13SpecialGraphDivisorCharts.pointIdeal_sq_eq_mumfordIdeal_of_square
            A 1 hu |>.symm

/-- Reflected special infinity graph data has the affine ideal obtained
from its canonical completed root divisor. -/
theorem reflected_affineIdeal_eq_rootAffineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2)
    (hv : D.v.natDegree ≤ 3)
    (haff :
      D.v.reflect 3 ^ 2 +
          N13GoodCoordinateRingTwo.hPoly * D.v.reflect 3 -
          N13GoodCoordinateRingTwo.rhsPoly =
        D.u.reflect 2 * D.w.reflect 4) :
    N13GoodCoordinateRingTwo.mumfordIdeal
        (D.u.reflect 2) (D.v.reflect 3) =
      N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal D
        (N13SpecialInfinityGraphDivisor.rootPair D hdeg) := by
  exact
    reflected_affineIdeal_eq_rootAffineIdeal_of_rootPolynomial
      D
      (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
      hv
      (N13SpecialInfinityGraphDivisorCharts.rootPolynomial_rootPair
        D hdeg).symm
      haff

/-- Coefficient reduction commutes with the weight-two horizontal
reflection. -/
theorem reduce_affineU
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityGraphTwoChart.affineU E) =
      (N13IntegralInfinityReduction.reducePoly E.u).reflect 2 := by
  rw [N13IntegralInfinityGraphTwoChart.affineU,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    ← Polynomial.reflect_map]
  rfl

/-- Coefficient reduction commutes with the weight-three vertical
reflection. -/
theorem reduce_affineV
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityGraphTwoChart.affineV E) =
      (N13IntegralInfinityReduction.reducePoly E.v).reflect 3 := by
  rw [N13IntegralInfinityGraphTwoChart.affineV,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    ← Polynomial.reflect_map]
  rfl

/-- Coefficient reduction commutes with the weight-four quotient
reflection. -/
theorem reduce_affineW
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityGraphTwoChart.affineW E) =
      (N13IntegralInfinityReduction.reducePoly E.w).reflect 4 := by
  rw [N13IntegralInfinityGraphTwoChart.affineW,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    ← Polynomial.reflect_map]
  rfl

/-- Reducing the integral infinity graph ideal gives the special infinity
graph ideal with coefficientwise reduced equations. -/
theorem map_infinityIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.infinityIdeal E) =
      N13SpecialInfinityGraphDivisorCharts.graphIdeal
        (N13IntegralInfinityReduction.reducePoly E.u)
        (N13IntegralInfinityReduction.reducePoly E.v) := by
  have hx (p : N13IntegralInfinityReduction.IntegralBase) :
      N13IntegralInfinityReduction.reduceCoordinate
          ((AdjoinRoot.of
            N13IntegralInfinityChart.infinityCurvePoly) p) =
        (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
          (N13IntegralInfinityReduction.reducePoly p) := by
    change
      N13IntegralInfinityReduction.reduceCoordinate
          (N13IntegralInfinityReduction.integralBaseClass p) =
        N13IntegralInfinityReduction.specialBaseClass
          (N13IntegralInfinityReduction.reducePoly p)
    exact N13IntegralInfinityReduction.reduce_integralBaseClass p
  simp [N13IntegralInfinityGraphTwoChart.infinityIdeal,
    N13SpecialInfinityGraphDivisorCharts.graphIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityGraphJacobian.xClassHom,
    N13IntegralInfinityPointSpread.xClassHom,
    N13IntegralInfinityGraphJacobian.yClass,
    N13IntegralInfinityPointSpread.yClass,
    N13SpecialInfinityGraphDivisorCharts.xClassHom,
    N13SpecialInfinityGraphDivisorCharts.yClass,
    N13IntegralInfinityReduction.reducePoly, hx]

/-- Reducing the weighted affine closure gives the reflected special graph
ideal. -/
theorem map_affineIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.affineIdeal E) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        ((N13IntegralInfinityReduction.reducePoly E.u).reflect 2)
        ((N13IntegralInfinityReduction.reducePoly E.v).reflect 3) := by
  change
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13IntegralInfinityGraphTwoChart.affineU E)
          (N13IntegralInfinityGraphTwoChart.affineV E)) =
      _
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal,
    reduce_affineU, reduce_affineV]

/-- The reflected special coefficients satisfy the affine semigraph
identity obtained by reducing the integral weighted-reflection identity. -/
theorem reduce_affine_curve_eq
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hdu : E.u.natDegree ≤ 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    (N13IntegralInfinityReduction.reducePoly E.v).reflect 3 ^ 2 +
          N13GoodCoordinateRingTwo.hPoly *
            (N13IntegralInfinityReduction.reducePoly E.v).reflect 3 -
          N13GoodCoordinateRingTwo.rhsPoly =
      (N13IntegralInfinityReduction.reducePoly E.u).reflect 2 *
        (N13IntegralInfinityReduction.reducePoly E.w).reflect 4 := by
  have h :=
    congrArg N13GeneralizedMumfordReduction.reducePoly
      (N13IntegralInfinityGraphTwoChart.affine_curve_eq
        E hdu hdv hdw)
  simpa only [map_add, map_sub, map_mul, map_pow,
    N13GeneralizedMumfordReduction.reduce_hPoly,
    N13GeneralizedMumfordReduction.reduce_rhsPoly,
    reduce_affineU, reduce_affineV, reduce_affineW] using h

/-- The affine restriction of a monic integral infinity quadratic is the
canonical affine ideal of its completed special root divisor. -/
theorem restrict_twoChartLine_affineIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor
          (N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg))).affineIdeal := by
  let D :=
    N13SpecialInfinityGraphDivisor.reduceGraphData E hu
  let hDdeg :=
    N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
      E hu hdeg
  change
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.affineIdeal E) =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hDdeg)).affineIdeal
  rw [map_affineIdeal,
    N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal]
  change
    N13GoodCoordinateRingTwo.mumfordIdeal
        (D.u.reflect 2) (D.v.reflect 3) =
      N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal D
        (N13SpecialInfinityGraphDivisor.rootPair D hDdeg)
  apply reflected_affineIdeal_eq_rootAffineIdeal D hDdeg
  · exact Polynomial.natDegree_map_le.trans hdv
  · exact reduce_affine_curve_eq E (by omega) hdv hdw

/-- The infinity restriction of a monic integral infinity quadratic is the
canonical infinity ideal of the same completed special root divisor. -/
theorem restrict_twoChartLine_infinityIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor
          (N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg))).infinityIdeal := by
  let D :=
    N13SpecialInfinityGraphDivisor.reduceGraphData E hu
  let hDdeg :=
    N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
      E hu hdeg
  change
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.infinityIdeal E) =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hDdeg)).infinityIdeal
  rw [map_infinityIdeal,
    N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal]
  rfl

/-- A bounded monic integral infinity quadratic restricts to the complete
canonical chart pair of its special root divisor. -/
theorem restrict_twoChartLine
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero) =
      N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor
          (N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg)) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact restrict_twoChartLine_affineIdeal E hu hdeg hdv hdw
  · exact restrict_twoChartLine_infinityIdeal E hu hdeg hdv hdw

end

end MazurProof.N13IntegralInfinityGraphSpecialRestriction


