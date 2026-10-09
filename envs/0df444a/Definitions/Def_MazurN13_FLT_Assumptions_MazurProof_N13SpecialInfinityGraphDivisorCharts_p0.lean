-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityGraphDivisorCharts_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityGraphDivisorCharts_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:31:55.724173+00:00
-- url     : https://prove2.me/theorems/27dc73f2-31bb-44b4-9d6a-75520125f8a2
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisorCharts source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisorCharts

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisorCharts
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityGraphDivisor_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisorCharts_p0

set_option autoImplicit false




/-!
# Chart ideals of special infinity-graph divisors

This file identifies the canonical two-chart ideals of the degree-two
divisor obtained from a monic graph on the special infinity chart.  The
key local calculation treats a repeated root directly: the square of the
point ideal equals the quadratic graph ideal because the curve coefficient
`h∞(a)` is a unit at every `F₂`-rational root.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialInfinityGraphDivisorCharts

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev K := N13SpecialInfinityChart.K
abbrev Ring := N13SpecialDivisorCharts.SpecialInfinity

/-- The special infinity coordinate ring receives polynomials in `t`. -/
def xClassHom : K[X] →+* Ring :=
  AdjoinRoot.of N13SpecialInfinityChart.curvePoly

/-- The class of the infinity-chart vertical coordinate. -/
def yClass : Ring :=
  N13SpecialInfinityChart.vClass

/-- The ideal of the graph `u(t) = 0`, `v∞ = v(t)`. -/
def graphIdeal (u v : K[X]) : Ideal Ring :=
  GeneralizedGraphIdealCore.graphIdeal xClassHom yClass u v

/-- The coordinate-ring class of `v∞ - v(t)`. -/
def ySubClass (v : K[X]) : Ring :=
  GeneralizedGraphIdealCore.ySubClass xClassHom yClass v

/-- The defining equation of the special infinity chart holds in its
coordinate ring. -/
theorem yClass_relation :
    yClass ^ 2 +
        xClassHom N13SpecialInfinityChart.hPoly * yClass =
      xClassHom N13SpecialInfinityChart.rhsPoly := by
  change
    N13SpecialInfinityChart.vClass ^ 2 +
        (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.rhsPoly
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13SpecialInfinityChart.curvePoly]
  ring

/-- A root selected from the canonical root pair contributes its literal
infinity-chart point ideal. -/
theorem rootPoint_infinityIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2)
    (a : K)
    (ha : a ∈ N13SpecialInfinityGraphDivisor.rootPair D hdeg) :
    (N13SpecialDivisorCharts.point
        (N13SpecialInfinityGraphDivisor.rootPoint
          D hdeg a ha)).infinityIdeal =
      N13SpecialDivisorCharts.infinityPointIdeal
        a (D.v.eval a) := by
  rw [N13SpecialInfinityGraphDivisor.rootPoint]
  split
  · subst a
    rw [N13SpecialDivisorCharts.point.eq_def]
    rfl
  · have ha1 : a = 1 :=
      (N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a)).resolve_left ‹a ≠ 0›
    change
      N13SpecialDivisorCharts.infinityPointIdeal
          1 (D.v.eval a) =
        N13SpecialDivisorCharts.infinityPointIdeal
          a (D.v.eval a)
    rw [ha1]

/-- The affine chart contribution of one infinity-graph root is absent at
`t = 0` and is the point graph at `x = 1` for the nonzero root. -/
theorem rootPoint_affineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2)
    (a : K)
    (ha : a ∈ N13SpecialInfinityGraphDivisor.rootPair D hdeg) :
    (N13SpecialDivisorCharts.point
        (N13SpecialInfinityGraphDivisor.rootPoint
          D hdeg a ha)).affineIdeal =
      if a = 0 then ⊤ else
        N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C 1) (C (D.v.eval a)) := by
  rw [N13SpecialInfinityGraphDivisor.rootPoint]
  split
  · subst a
    rw [N13SpecialDivisorCharts.point.eq_def]
    rfl
  · have ha1 : a = 1 :=
      (N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a)).resolve_left ‹a ≠ 0›
    rw [N13SpecialDivisorCharts.point.eq_def]
    dsimp
    rfl

/-- The affine ideal contributed by an unordered pair of infinity roots. -/
def rootAffineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford) :
    Sym2 K → Ideal N13SpecialDivisorCharts.SpecialAffine :=
  Sym2.lift
    ⟨fun a b =>
        (if a = 0 then ⊤ else
          N13GoodCoordinateRingTwo.mumfordIdeal
            (X - C 1) (C (D.v.eval a))) *
        (if b = 0 then ⊤ else
          N13GoodCoordinateRingTwo.mumfordIdeal
            (X - C 1) (C (D.v.eval b))),
      fun a b => by
        dsimp
        rw [mul_comm]⟩

/-- Evaluation of the affine root-ideal product on a concrete unordered
pair. -/
@[simp] theorem rootAffineIdeal_mk
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a b : K) :
    rootAffineIdeal D s(a, b) =
      (if a = 0 then ⊤ else
        N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C 1) (C (D.v.eval a))) *
      (if b = 0 then ⊤ else
        N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C 1) (C (D.v.eval b))) :=
  rfl

/-- The canonical affine ideal of any selected pair of infinity-graph
roots is the product of their explicit affine contributions. -/
theorem ofDivisor_graphRoots_affineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2)
    (z : Sym2 K)
    (hz :
      ∀ a ∈ z,
        a ∈ N13SpecialInfinityGraphDivisor.rootPair D hdeg) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap
          (N13SpecialInfinityGraphDivisor.rootPoint D hdeg)
          z hz)).affineIdeal =
      rootAffineIdeal D z := by
  induction z using Sym2.ind with
  | _ a b =>
      rw [Sym2.pmap_pair,
        N13SpecialDivisorCharts.ofDivisor_mk]
      change
        (N13SpecialDivisorCharts.point
            (N13SpecialInfinityGraphDivisor.rootPoint D hdeg a
              (hz a (Sym2.mem_mk_left a b)))).affineIdeal *
          (N13SpecialDivisorCharts.point
            (N13SpecialInfinityGraphDivisor.rootPoint D hdeg b
              (hz b (Sym2.mem_mk_right a b)))).affineIdeal =
        rootAffineIdeal D s(a, b)
      rw [rootPoint_affineIdeal, rootPoint_affineIdeal,
        rootAffineIdeal_mk]

/-- The canonical affine ideal of an infinity-graph divisor is the product
of the contributions of its two infinity roots. -/
theorem ofDivisor_graphDivisor_affineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hdeg)).affineIdeal =
      rootAffineIdeal D
        (N13SpecialInfinityGraphDivisor.rootPair D hdeg) := by
  unfold N13SpecialInfinityGraphDivisor.graphDivisor
  exact
    ofDivisor_graphRoots_affineIdeal D hdeg
      (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
      (fun _ ha => ha)

/-- A special infinity point ideal is the graph ideal of its linear
`t`-factor and constant vertical value. -/
theorem infinityPointIdeal_eq_graphIdeal
    (a z : K) :
    N13SpecialDivisorCharts.infinityPointIdeal a z =
      graphIdeal (X - C a) (C z) := by
  simp [N13SpecialDivisorCharts.infinityPointIdeal,
    graphIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    xClassHom, yClass,
    N13SpecialInfinityChart.tClass]

/-- At a repeated `F₂`-root, the squared linear graph ideal is the
quadratic graph ideal. -/
theorem pointIdeal_sq_eq_graphIdeal_of_square
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a : K)
    (hfactor : D.u = (X - C a) ^ 2) :
    graphIdeal (X - C a) (C (D.v.eval a)) ^ 2 =
      graphIdeal D.u D.v := by
  let p : K[X] := X - C a
  let z : K := D.v.eval a
  let I : Ideal Ring := graphIdeal p D.v
  let J : Ideal Ring := graphIdeal (p ^ 2) D.v
  let g : Ring := ySubClass D.v
  let plus : Ring :=
    ySubClass
      (GeneralizedGraphIdealCore.conjugateV
        N13SpecialInfinityChart.hPoly D.v)
  have hdiv : p ∣ D.v - C z := by
    simpa [p, z] using
      (X_sub_C_dvd_sub_C_eval (p := D.v) (a := a))
  have hgraph :
      graphIdeal p D.v = graphIdeal p (C z) := by
    exact
      GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p (C z) D.v hdiv
  have hpI : xClassHom p ∈ I :=
    GeneralizedGraphIdealCore.xClass_mem_graphIdeal
      xClassHom yClass p D.v
  have hgI : g ∈ I :=
    GeneralizedGraphIdealCore.ySubClass_mem_graphIdeal
      xClassHom yClass p D.v
  have hp2I : xClassHom (p ^ 2) ∈ I ^ 2 := by
    rw [map_pow]
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hpI
  have hggI : g * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hgI hgI
  have hproduct :
      g * plus = -(xClassHom (p ^ 2) * xClassHom D.w) := by
    change
      GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass D.v *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass
              (GeneralizedGraphIdealCore.conjugateV
                N13SpecialInfinityChart.hPoly D.v) =
        -(xClassHom (p ^ 2) * xClassHom D.w)
    rw [GeneralizedGraphIdealCore.ySubClass_mul_conjugate
      xClassHom yClass
      N13SpecialInfinityChart.hPoly
      N13SpecialInfinityChart.rhsPoly
      D.toSemiGraph yClass_relation, hfactor]
  have hplusgI : plus * g ∈ I ^ 2 := by
    rw [mul_comm, hproduct]
    exact
      (I ^ 2).neg_mem
        (Ideal.mul_mem_right (xClassHom D.w) _ hp2I)
  have hvv : xClassHom D.v + xClassHom D.v = 0 := by
    rw [← map_add]
    have htwoPoly : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    have hvvPoly : D.v + D.v = 0 := by
      calc
        D.v + D.v = 2 * D.v := by ring
        _ = 0 := by rw [htwoPoly, zero_mul]
    rw [hvvPoly, map_zero]
  have hplus_sub_g :
      plus - g =
        xClassHom N13SpecialInfinityChart.hPoly := by
    simp only [plus, g, ySubClass,
      GeneralizedGraphIdealCore.ySubClass,
      GeneralizedGraphIdealCore.conjugateV,
      map_neg, map_sub]
    linear_combination hvv
  have hhEval :
      N13SpecialInfinityChart.hPoly.eval a = 1 := by
    simp only [N13SpecialInfinityChart.hPoly,
      eval_add, eval_pow, eval_X, eval_one]
    fin_cases a <;> decide
  have hhdiv :
      p ∣ N13SpecialInfinityChart.hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.hPoly) (a := a))
  have hpgI : xClassHom p * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hgI
  have hdeltaG :
      xClassHom (N13SpecialInfinityChart.hPoly - C 1) * g ∈
        I ^ 2 := by
    obtain ⟨s, hs⟩ := hhdiv
    rw [hs, map_mul]
    convert Ideal.mul_mem_left (I ^ 2) (xClassHom s) hpgI using 1
    ring
  have hhgI :
      xClassHom N13SpecialInfinityChart.hPoly * g ∈ I ^ 2 := by
    rw [← hplus_sub_g]
    convert Ideal.sub_mem (I ^ 2) hplusgI hggI using 1
    ring
  have hgSq : g ∈ I ^ 2 := by
    have hmem := Ideal.sub_mem (I ^ 2) hhgI hdeltaG
    have heq :
        xClassHom N13SpecialInfinityChart.hPoly * g -
            xClassHom
                (N13SpecialInfinityChart.hPoly - C 1) * g =
          g := by
      rw [map_sub]
      have hcOne : xClassHom (C (1 : K)) = 1 := rfl
      rw [hcOne]
      ring
    rw [heq] at hmem
    exact hmem
  have hIJ : I ^ 2 = J := by
    apply le_antisymm
    · change graphIdeal p D.v ^ 2 ≤ J
      rw [pow_two, graphIdeal,
        GeneralizedGraphIdealCore.graphIdeal,
        Ideal.span_pair_mul_span_pair]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      have hp2J : xClassHom (p ^ 2) ∈ J :=
        GeneralizedGraphIdealCore.xClass_mem_graphIdeal
          xClassHom yClass (p ^ 2) D.v
      have hgJ : g ∈ J :=
        GeneralizedGraphIdealCore.ySubClass_mem_graphIdeal
          xClassHom yClass (p ^ 2) D.v
      rcases ht with rfl | rfl | rfl | rfl
      · rw [← map_mul, ← pow_two]
        exact hp2J
      · exact Ideal.mul_mem_left J (xClassHom p) hgJ
      · exact Ideal.mul_mem_right (xClassHom p) J hgJ
      · exact Ideal.mul_mem_left J g hgJ
    · change graphIdeal (p ^ 2) D.v ≤ I ^ 2
      rw [graphIdeal, GeneralizedGraphIdealCore.graphIdeal]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact hp2I
      · exact hgSq
  calc
    graphIdeal p (C z) ^ 2 = I ^ 2 := by
      change graphIdeal p (C z) ^ 2 =
        graphIdeal p D.v ^ 2
      rw [hgraph]
    _ = J := hIJ
    _ = graphIdeal D.u D.v := by rw [hfactor]

/-- A root of an infinity-chart graph gives a completed special point. -/
def graphRootPoint
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    N13SpecialDivisorCharts.CurvePoint :=
  if ha0 : a = 0 then
    Sum.inr
      ⟨D.v.eval a, by
        subst a
        exact
          N13SpecialInfinityGraphDivisor.curveEquationAtRoot D ha⟩
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
            (N13SpecialInfinityGraphDivisor.curveEquationAtRoot D ha)⟩

/-- The completed point attached to a graph root has the corresponding
linear infinity graph ideal. -/
theorem graphRootPoint_infinityIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    (N13SpecialDivisorCharts.point
        (graphRootPoint D a ha)).infinityIdeal =
      graphIdeal (X - C a) (C (D.v.eval a)) := by
  have hpoint :
      (N13SpecialDivisorCharts.point
          (graphRootPoint D a ha)).infinityIdeal =
        N13SpecialDivisorCharts.infinityPointIdeal
          a (D.v.eval a) := by
    rw [graphRootPoint]
    split
    · subst a
      rw [N13SpecialDivisorCharts.point.eq_def]
      rfl
    · have ha1 : a = 1 :=
        (N13GoodModelTwo.fixedTwo_eq_zero_or_one
          a (ZMod.pow_card a)).resolve_left ‹a ≠ 0›
      change
        N13SpecialDivisorCharts.infinityPointIdeal
            1 (D.v.eval a) =
          N13SpecialDivisorCharts.infinityPointIdeal
            a (D.v.eval a)
      rw [ha1]
  rw [hpoint, infinityPointIdeal_eq_graphIdeal]

/-- The product of the two point ideals of a split graph is its quadratic
infinity graph ideal. -/
theorem ofDivisor_graphRoots_infinityIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (z : Sym2 K)
    (hz : ∀ a ∈ z, D.u.IsRoot a)
    (hfactor :
      D.u = N13SpecialGraphDivisorCharts.rootPolynomial z) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap (graphRootPoint D) z hz)).infinityIdeal =
      graphIdeal D.u D.v := by
  induction z using Sym2.ind with
  | _ a b =>
      rw [Sym2.pmap_pair,
        N13SpecialDivisorCharts.ofDivisor_mk]
      change
        (N13SpecialDivisorCharts.point
            (graphRootPoint D a
              (hz a (Sym2.mem_mk_left a b)))).infinityIdeal *
          (N13SpecialDivisorCharts.point
            (graphRootPoint D b
              (hz b (Sym2.mem_mk_right a b)))).infinityIdeal =
        graphIdeal D.u D.v
      rw [graphRootPoint_infinityIdeal,
        graphRootPoint_infinityIdeal]
      by_cases hab : a = b
      · subst b
        simpa only [pow_two] using
          (pointIdeal_sq_eq_graphIdeal_of_square D a
            (by
              simpa only [
                N13SpecialGraphDivisorCharts.rootPolynomial_mk,
                pow_two] using hfactor))
      · have hleft :
            X - C a ∣ D.v - C (D.v.eval a) :=
          X_sub_C_dvd_sub_C_eval
        have hright :
            X - C b ∣ D.v - C (D.v.eval b) :=
          X_sub_C_dvd_sub_C_eval
        have hd : b - a ≠ 0 :=
          sub_ne_zero.mpr (Ne.symm hab)
        have hcop :
            ∃ A B : K[X],
              A * (X - C a) + B * (X - C b) = 1 := by
          refine
            ⟨C ((b - a)⁻¹), -C ((b - a)⁻¹), ?_⟩
          calc
            C ((b - a)⁻¹) * (X - C a) +
                  -C ((b - a)⁻¹) * (X - C b) =
                C ((b - a)⁻¹) * C (b - a) := by
              rw [map_sub]
              ring
            _ = 1 := by
              rw [← map_mul, inv_mul_cancel₀ hd, map_one]
        rw [hfactor]
        exact
          GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
            xClassHom yClass
            (X - C a) (X - C b)
            (C (D.v.eval a)) (C (D.v.eval b)) D.v
            hleft hright hcop

/-- The polynomial reconstructed from the chosen infinity roots is the
original monic quadratic. -/
theorem rootPolynomial_rootPair
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    N13SpecialGraphDivisorCharts.rootPolynomial
        (N13SpecialInfinityGraphDivisor.rootPair D hdeg) =
      D.u := by
  calc
    N13SpecialGraphDivisorCharts.rootPolynomial
          (N13SpecialInfinityGraphDivisor.rootPair D hdeg) =
        ((N13SpecialInfinityGraphDivisor.rootPair D hdeg).toMultiset.map
          (fun a => X - C a)).prod :=
      N13SpecialGraphDivisorCharts.rootPolynomial_eq_prod _
    _ = (D.u.roots.map (fun a => X - C a)).prod := by
      rw [N13SpecialInfinityGraphDivisor.rootPair_toMultiset]
    _ = D.u :=
      (Polynomial.Splits.eq_prod_roots_of_monic
        (N13SpecialInfinityGraphDivisor.degreeTwo_splits D hdeg)
        D.u_monic).symm

/-- The canonical infinity ideal of the divisor cut out by a monic
quadratic infinity graph is exactly that graph ideal. -/
theorem ofDivisor_graphDivisor_infinityIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hdeg)).infinityIdeal =
      graphIdeal D.u D.v := by
  unfold N13SpecialInfinityGraphDivisor.graphDivisor
  let hz :
      ∀ a ∈ N13SpecialInfinityGraphDivisor.rootPair D hdeg,
        D.u.IsRoot a :=
    fun a ha =>
      (N13SpecialInfinityGraphDivisor.mem_rootPair_iff_isRoot
        D hdeg a).mp ha
  have hpmap :
      Sym2.pmap
          (N13SpecialInfinityGraphDivisor.rootPoint D hdeg)
          (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
          (fun _ ha => ha) =
        Sym2.pmap
          (graphRootPoint D)
          (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
          hz := by
    apply Sym2.ext
    intro P
    rw [Sym2.mem_pmap_iff, Sym2.mem_pmap_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [hpmap]
  exact
    ofDivisor_graphRoots_infinityIdeal D
      (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
      hz (rootPolynomial_rootPair D hdeg).symm

end

end MazurProof.N13SpecialInfinityGraphDivisorCharts


