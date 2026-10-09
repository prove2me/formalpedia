-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityGraphDivisor_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityGraphDivisor_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:21:41.753048+00:00
-- url     : https://prove2.me/theorems/9e9e98c7-0cd9-4263-a9fa-bcc18a02345d
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisor source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisor

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisor
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorCharts_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareFrobenius_p0

set_option autoImplicit false




/-!
# Special divisors cut out by infinity-chart graphs

A monic quadratic graph on the special infinity chart splits over `F₂`.
Roots at `t = 0` give the two points at infinity, while roots at `t = 1`
give affine points on the overlap.  This is the proper root divisor needed
when an integral reciprocal graph loses affine degree after reduction.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialInfinityGraphDivisor

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev K := N13SpecialInfinityChart.K

/-- Mumford graph data on the special infinity chart, with a monic
horizontal polynomial. -/
structure SemiMumford
    extends
      GeneralizedGraphIdealCore.SemiGraph
        N13SpecialInfinityChart.hPoly
        N13SpecialInfinityChart.rhsPoly where
  u_monic : u.Monic

/-- Reduce an integral infinity graph coefficientwise modulo `2`. -/
def reduceGraphData
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic) :
    SemiMumford where
  u := N13IntegralInfinityReduction.reducePoly E.u
  v := N13IntegralInfinityReduction.reducePoly E.v
  w := N13IntegralInfinityReduction.reducePoly E.w
  u_monic := hu.map N13IntegralInfinityReduction.reduceBase
  curve_eq := by
    have h := congrArg N13IntegralInfinityReduction.reducePoly E.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      N13IntegralInfinityReduction.reduce_hBase,
      N13IntegralInfinityReduction.reduce_rhsBase] using h

/-- A monic integral quadratic retains degree two after reduction. -/
theorem reduceGraphData_u_natDegree
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2) :
    (reduceGraphData E hu).u.natDegree = 2 := by
  change
    (E.u.map
      N13IntegralInfinityReduction.reduceBase).natDegree = 2
  rw [hu.natDegree_map, hdeg]

/-- Every monic quadratic graph satisfying the special infinity curve
equation splits over `F₂`. -/
theorem degreeTwo_splits
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    D.u.Splits := by
  by_contra hnot
  have hnoRoot (a : K) : D.u.eval a ≠ 0 := by
    intro ha
    exact hnot (Polynomial.Splits.of_natDegree_eq_two hdeg ha)
  have hroots : D.u.roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    exact hnoRoot a ((Polynomial.mem_roots D.u_monic.ne_zero).mp ha)
  have hirr : Irreducible D.u := by
    apply (D.u_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)).mpr
    exact hroots
  letI : Fact (Irreducible D.u) := ⟨hirr⟩
  letI : Module.Finite K (AdjoinRoot D.u) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  letI : Finite (AdjoinRoot D.u) :=
    Module.finite_of_finite K
  letI : Fintype (AdjoinRoot D.u) :=
    Fintype.ofFinite (AdjoinRoot D.u)
  letI : CharP (AdjoinRoot D.u) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (AdjoinRoot D.u)).injective 2
  have hcard : Fintype.card (AdjoinRoot D.u) = 4 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := AdjoinRoot D.u),
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      ZMod.card, AdjoinRoot.powerBasis_dim, hdeg]
    norm_num
  let alpha : AdjoinRoot D.u := AdjoinRoot.root D.u
  let beta : AdjoinRoot D.u := Polynomial.aeval alpha D.v
  have hfour (z : AdjoinRoot D.u) : z ^ 4 = z := by
    rw [← hcard]
    exact FiniteField.pow_card z
  have hroot : Polynomial.aeval alpha D.u = 0 := by
    simp [alpha, Polynomial.aeval_def, AdjoinRoot.eval₂_root]
  have hcurve :
      N13GoodModelTwo.InfinityChartEquation alpha beta := by
    have hc := congrArg (Polynomial.aeval alpha) D.curve_eq
    simp only [map_sub, map_add, map_pow, map_mul] at hc
    rw [hroot, zero_mul] at hc
    change
      beta ^ 2 + (1 + alpha ^ 2 + alpha ^ 3) * beta =
        alpha + alpha ^ 2
    simpa [beta, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly,
      Polynomial.aeval_def] using sub_eq_zero.mp hc
  by_cases halpha : alpha = 0
  · have hz : D.u.eval 0 = 0 := by
      apply (algebraMap K (AdjoinRoot D.u)).injective
      have hzmap :
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) = 0 := by
        calc
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) =
              eval₂ (algebraMap K (AdjoinRoot D.u))
                (algebraMap K (AdjoinRoot D.u) 0) D.u := by
                  rw [Polynomial.eval₂_at_apply]
          _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                rw [halpha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using hzmap
    exact hnoRoot 0 hz
  · let x : AdjoinRoot D.u := alpha⁻¹
    have hxa : x * alpha = 1 := by
      exact inv_mul_cancel₀ halpha
    have haffine :
        N13GoodModelTwo.AffineEquation x (x ^ 3 * beta) :=
      (N13GoodModelTwo.affine_iff_infinity_on_overlap hxa).mpr hcurve
    have hxFixed : x ^ 2 = x :=
      ((N13GoodModelTwo.affineEquation_iff_fixed
        hfour x (x ^ 3 * beta)).mp haffine).1
    rcases
        N13GoodModelTwo.fixedTwo_eq_zero_or_one x hxFixed with
      hx0 | hx1
    · exact (inv_ne_zero halpha hx0).elim
    · have halphaOne : alpha = 1 := by
        apply inv_injective
        simpa [x] using hx1
      have ho : D.u.eval 1 = 0 := by
        apply (algebraMap K (AdjoinRoot D.u)).injective
        have homap :
            algebraMap K (AdjoinRoot D.u) (D.u.eval 1) = 0 := by
          calc
            algebraMap K (AdjoinRoot D.u) (D.u.eval 1) =
                eval₂ (algebraMap K (AdjoinRoot D.u))
                  (algebraMap K (AdjoinRoot D.u) 1) D.u := by
                    rw [Polynomial.eval₂_at_apply]
            _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                  rw [halphaOne]
                  simp
            _ = 0 := AdjoinRoot.eval₂_root D.u
        simpa using homap
      exact hnoRoot 1 ho

/-- The two roots of a split infinity graph form an unordered pair. -/
theorem exists_rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    ∃ z : Sym2 K, z.toMultiset = D.u.roots := by
  have hcard : D.u.roots.card = 2 := by
    rw [← (degreeTwo_splits D hdeg).natDegree_eq_card_roots]
    exact hdeg
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨s(a, b), ?_⟩
  change ({a, b} : Multiset K) = D.u.roots
  exact hab.symm

/-- The canonical unordered pair of roots of a special infinity graph. -/
noncomputable def rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    Sym2 K :=
  Classical.choose (exists_rootPair D hdeg)

/-- The multiset underlying the chosen root pair is the polynomial root
multiset. -/
theorem rootPair_toMultiset
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    (rootPair D hdeg).toMultiset = D.u.roots :=
  Classical.choose_spec (exists_rootPair D hdeg)

/-- Membership in the chosen root pair is equivalent to vanishing of the
horizontal polynomial. -/
theorem mem_rootPair_iff_isRoot
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) (a : K) :
    a ∈ rootPair D hdeg ↔ D.u.IsRoot a := by
  rw [← Sym2.mem_toMultiset, rootPair_toMultiset,
    Polynomial.mem_roots D.u_monic.ne_zero]

/-- Evaluating the graph equation at a horizontal root gives a point on
the special infinity chart. -/
theorem curveEquationAtRoot
    (D : SemiMumford) {a : K} (ha : D.u.IsRoot a) :
    N13GoodModelTwo.InfinityChartEquation a (D.v.eval a) := by
  have hc := congrArg (Polynomial.eval a) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at hc
  rw [ha, zero_mul] at hc
  change
    D.v.eval a ^ 2 +
        (1 + a ^ 2 + a ^ 3) * D.v.eval a =
      a + a ^ 2
  simpa [N13SpecialInfinityChart.hPoly,
    N13SpecialInfinityChart.rhsPoly] using sub_eq_zero.mp hc

/-- Complete an infinity-graph root to the special curve: `t = 0` is a
point at infinity and the nonzero root `t = 1` lies on the affine overlap. -/
noncomputable def rootPoint
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (a : K) (ha : a ∈ rootPair D hdeg) :
    N13SpecialDivisorCharts.CurvePoint :=
  if ha0 : a = 0 then
    Sum.inr
      ⟨D.v.eval a, by
        subst a
        exact curveEquationAtRoot D
          ((mem_rootPair_iff_isRoot D hdeg 0).mp ha)⟩
  else
    Sum.inl
      ⟨(1, D.v.eval a), by
        have ha1 : a = 1 :=
          (N13GoodModelTwo.fixedTwo_eq_zero_or_one
            a (ZMod.pow_card a)).resolve_left ha0
        subst a
        simpa using
          (N13GoodModelTwo.affine_iff_infinity_on_overlap
            (show (1 : K) * 1 = 1 by simp)).mpr
            (curveEquationAtRoot D
              ((mem_rootPair_iff_isRoot D hdeg 1).mp ha))⟩

/-- The effective degree-two divisor consisting of the two completed graph
roots. -/
noncomputable def graphDivisor
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13SpecialDivisorCharts.EffectiveDivisorTwo :=
  Sym2.pmap (rootPoint D hdeg) (rootPair D hdeg)
    (fun _ ha => ha)

end

end MazurProof.N13SpecialInfinityGraphDivisor


