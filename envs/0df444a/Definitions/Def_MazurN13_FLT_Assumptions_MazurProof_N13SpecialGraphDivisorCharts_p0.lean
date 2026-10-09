-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisorCharts_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisorCharts_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:21:44.479299+00:00
-- url     : https://prove2.me/theorems/bd2c95f3-22e1-42dc-8223-d06e821d519b
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialGraphDivisorCharts source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialGraphDivisorCharts

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialGraphDivisorCharts
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorCharts_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisor_p0

set_option autoImplicit false




/-!
# Chart ideals of special N13 graph divisors

A smooth quadratic generalized Mumford graph on the characteristic-two
N13 fibre splits into two graph points.  This file proves that the product
of their canonical affine point ideals is exactly the original Mumford
ideal.

For distinct roots this is the graph-ideal Chinese remainder theorem.  For
a repeated root, the vertical derivative is the everywhere nonzero
polynomial `h = X³ + X + 1` on `F₂`; this identifies the tangent graph ideal
with the square of the point ideal.  Thus the result retains multiplicity
without enumerating effective divisors.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialGraphDivisorCharts

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open N13GoodCoordinateRingTwo

abbrev K := N13GoodCoordinateRingTwo.K

theorem point_affineIdeal
    (P : N13SpecialDivisorCharts.AffinePoint) :
    (N13SpecialDivisorCharts.point (Sum.inl P)).affineIdeal =
      N13SpecialDivisorCharts.affinePointIdeal P := by
  rw [N13SpecialDivisorCharts.point]
  split <;> rfl

/-- On the special N13 fibre, a repeated-root graph ideal is the square
of its point ideal.  The key local unit is `h(a) = 1` for every `a ∈ F₂`. -/
theorem pointIdeal_sq_eq_mumfordIdeal_of_square
    (D : N13GoodCoordinateRingTwo.SemiMumford)
    (a : K)
    (hfactor : D.u = (X - C a) ^ 2) :
    N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C a) (C (D.v.eval a)) ^ 2 =
      N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v := by
  let p : K[X] := X - C a
  let z : K := D.v.eval a
  let I : Ideal CoordinateRing := mumfordIdeal p D.v
  let J : Ideal CoordinateRing := mumfordIdeal (p ^ 2) D.v
  let g : CoordinateRing := ySubClass D.v
  let plus : CoordinateRing := ySubClass (conjugateV D.v)
  have hdiv : p ∣ D.v - C z := by
    simpa [p, z] using
      (X_sub_C_dvd_sub_C_eval (p := D.v) (a := a))
  have hgraph :
      mumfordIdeal p D.v = mumfordIdeal p (C z) := by
    simpa [mumfordIdeal, GeneralizedGraphIdealCore.graphIdeal,
      ySubClass, GeneralizedGraphIdealCore.ySubClass] using
      (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p (C z) D.v hdiv)
  have hpI : xClass p ∈ I :=
    xClass_mem_mumfordIdeal p D.v
  have hgI : g ∈ I := by
    exact ySubClass_mem_mumfordIdeal p D.v
  have hp2I : xClass (p ^ 2) ∈ I ^ 2 := by
    rw [xClass_pow]
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hpI
  have hggI : g * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hgI hgI
  have hproduct :
      g * plus = -(xClass (p ^ 2) * xClass D.w) := by
    change
      ySubClass D.v * ySubClass (conjugateV D.v) =
        -(xClass (p ^ 2) * xClass D.w)
    rw [N13GoodCoordinateRingTwo.ySubClass_mul_conjugate D,
      hfactor]
  have hplusgI : plus * g ∈ I ^ 2 := by
    rw [mul_comm, hproduct]
    exact
      (I ^ 2).neg_mem
        (Ideal.mul_mem_right (xClass D.w) _ hp2I)
  have hvv : xClass D.v + xClass D.v = 0 := by
    rw [← xClass_add]
    have htwoPoly : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    have hvvPoly : D.v + D.v = 0 := by
      calc
        D.v + D.v = 2 * D.v := by ring
        _ = 0 := by rw [htwoPoly, zero_mul]
    rw [hvvPoly, xClass_zero]
  have hplus_sub_g : plus - g = xClass hPoly := by
    simp only [plus, g, conjugateV, ySubClass, xClass_neg,
      xClass_sub]
    linear_combination hvv
  have hhEval : hPoly.eval a = 1 := by
    simp only [hPoly, eval_add, eval_pow, eval_X, eval_one]
    fin_cases a <;> decide
  have hhdiv : p ∣ hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval (p := hPoly) (a := a))
  have hpgI : xClass p * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hgI
  have hdeltaG : xClass (hPoly - C 1) * g ∈ I ^ 2 := by
    obtain ⟨s, hs⟩ := hhdiv
    rw [hs, xClass_mul]
    convert Ideal.mul_mem_left (I ^ 2) (xClass s) hpgI using 1
    ring
  have hhgI : xClass hPoly * g ∈ I ^ 2 := by
    rw [← hplus_sub_g]
    convert Ideal.sub_mem (I ^ 2) hplusgI hggI using 1
    ring
  have hgSq : g ∈ I ^ 2 := by
    have hmem := Ideal.sub_mem (I ^ 2) hhgI hdeltaG
    have heq :
        xClass hPoly * g -
            xClass (hPoly - C 1) * g = g := by
      rw [xClass_sub]
      have hcOne : xClass (C (1 : K)) = 1 := rfl
      rw [hcOne]
      ring
    rw [heq] at hmem
    exact hmem
  have hIJ : I ^ 2 = J := by
    apply le_antisymm
    · change mumfordIdeal p D.v ^ 2 ≤ J
      rw [pow_two, mumfordIdeal, Ideal.span_pair_mul_span_pair]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      have hp2J : xClass (p ^ 2) ∈ J :=
        xClass_mem_mumfordIdeal (p ^ 2) D.v
      have hgJ : g ∈ J := by
        exact ySubClass_mem_mumfordIdeal (p ^ 2) D.v
      rcases ht with rfl | rfl | rfl | rfl
      · rw [← xClass_mul, ← pow_two]
        exact hp2J
      · exact Ideal.mul_mem_left J (xClass p) hgJ
      · exact Ideal.mul_mem_right (xClass p) J hgJ
      · exact Ideal.mul_mem_left J g hgJ
    · change mumfordIdeal (p ^ 2) D.v ≤ I ^ 2
      rw [mumfordIdeal]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact hp2I
      · exact hgSq
  calc
    mumfordIdeal p (C z) ^ 2 = I ^ 2 := by
      change mumfordIdeal p (C z) ^ 2 = mumfordIdeal p D.v ^ 2
      rw [hgraph]
    _ = J := hIJ
    _ = mumfordIdeal D.u D.v := by rw [hfactor]

/-- The monic quadratic attached to an unordered pair of roots. -/
def rootPolynomial : Sym2 K → K[X] :=
  Sym2.lift
    ⟨fun a b => (X - C a) * (X - C b),
      fun a b => by
        dsimp
        rw [mul_comm]⟩

@[simp] theorem rootPolynomial_mk (a b : K) :
    rootPolynomial s(a, b) =
      (X - C a) * (X - C b) :=
  rfl

/-- A root of the horizontal equation gives its literal graph point. -/
def graphRootPoint
    (D : SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    N13SpecialDivisorCharts.CurvePoint :=
  Sum.inl
    ⟨(a, D.v.eval a),
      N13SpecialGraphDivisor.curveEquationAtRoot D ha⟩

/-- The canonical affine ideal of a graph root is its two-generator point
ideal `(X-a, Y-v(a))`. -/
theorem graphRootPoint_affineIdeal
    (D : SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    (N13SpecialDivisorCharts.point
        (graphRootPoint D a ha)).affineIdeal =
      mumfordIdeal (X - C a) (C (D.v.eval a)) := by
  change
    (N13SpecialDivisorCharts.point
        (Sum.inl
          (⟨(a, D.v.eval a),
            N13SpecialGraphDivisor.curveEquationAtRoot D ha⟩ :
            N13SpecialDivisorCharts.AffinePoint))).affineIdeal =
      _
  rw [point_affineIdeal]
  rfl

/-- The affine chart ideal of a split root divisor is its generalized
Mumford graph ideal.  Distinct roots use the graph Chinese remainder
identity; a repeated root uses the characteristic-two tangent identity. -/
theorem ofDivisor_graphRoots_affineIdeal
    (D : SemiMumford)
    (z : Sym2 K)
    (hz : ∀ a ∈ z, D.u.IsRoot a)
    (hfactor : D.u = rootPolynomial z) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap (graphRootPoint D) z hz)).affineIdeal =
      mumfordIdeal D.u D.v := by
  induction z using Sym2.ind with
  | _ a b =>
      rw [Sym2.pmap_pair,
        N13SpecialDivisorCharts.ofDivisor_mk]
      change
        (N13SpecialDivisorCharts.point
            (graphRootPoint D a
              (hz a (Sym2.mem_mk_left a b)))).affineIdeal *
          (N13SpecialDivisorCharts.point
            (graphRootPoint D b
              (hz b (Sym2.mem_mk_right a b)))).affineIdeal =
        mumfordIdeal D.u D.v
      rw [graphRootPoint_affineIdeal,
        graphRootPoint_affineIdeal]
      by_cases hab : a = b
      · subst b
        simpa only [pow_two] using
          (pointIdeal_sq_eq_mumfordIdeal_of_square D a
            (by
              simpa only [rootPolynomial_mk, pow_two] using hfactor))
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
        simpa [mumfordIdeal,
          GeneralizedGraphIdealCore.graphIdeal,
          ySubClass,
          GeneralizedGraphIdealCore.ySubClass] using
          (GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
            xClassHom yClass
            (X - C a) (X - C b)
            (C (D.v.eval a)) (C (D.v.eval b)) D.v
            hleft hright hcop)

/-- The symmetric-pair construction agrees with the product over its
two-element multiset. -/
theorem rootPolynomial_eq_prod (z : Sym2 K) :
    rootPolynomial z =
      (z.toMultiset.map (fun a => X - C a)).prod := by
  induction z using Sym2.ind with
  | _ a b =>
      simp [rootPolynomial, Sym2.toMultiset]

/-- The polynomial reconstructed from the chosen root pair is the original
monic quadratic. -/
theorem rootPolynomial_rootPair
    (D : SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    rootPolynomial
        (N13SpecialGraphDivisor.rootPair D hdeg) =
      D.u := by
  calc
    rootPolynomial
          (N13SpecialGraphDivisor.rootPair D hdeg) =
        ((N13SpecialGraphDivisor.rootPair D hdeg).toMultiset.map
          (fun a => X - C a)).prod :=
      rootPolynomial_eq_prod _
    _ = (D.u.roots.map (fun a => X - C a)).prod := by
      rw [N13SpecialGraphDivisor.rootPair_toMultiset]
    _ = D.u :=
      (Polynomial.Splits.eq_prod_roots_of_monic
        (N13SpecialGraphDivisor.degreeTwo_splits D hdeg)
        D.u_monic).symm

/-- The canonical affine chart ideal of the divisor cut out by a special
quadratic graph is exactly that graph's Mumford ideal. -/
theorem ofDivisor_graphDivisor_affineIdeal
    (D : SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor D hdeg)).affineIdeal =
      mumfordIdeal D.u D.v := by
  unfold N13SpecialGraphDivisor.graphDivisor
  let hz :
      ∀ a ∈ N13SpecialGraphDivisor.rootPair D hdeg,
        D.u.IsRoot a :=
    fun a ha =>
      (N13SpecialGraphDivisor.mem_rootPair_iff_isRoot
        D hdeg a).mp ha
  have hpmap :
      Sym2.pmap
          (N13SpecialGraphDivisor.rootPoint D hdeg)
          (N13SpecialGraphDivisor.rootPair D hdeg)
          (fun _ ha => ha) =
        Sym2.pmap
          (graphRootPoint D)
          (N13SpecialGraphDivisor.rootPair D hdeg)
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
    ofDivisor_graphRoots_affineIdeal D
      (N13SpecialGraphDivisor.rootPair D hdeg)
      hz
      (rootPolynomial_rootPair D hdeg).symm

/-- The infinity chart contribution of one graph root is unit at `x = 0`
and is the literal point ideal at `t = 1` when `x = 1`. -/
theorem graphRootPoint_infinityIdeal
    (D : SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    (N13SpecialDivisorCharts.point
        (graphRootPoint D a ha)).infinityIdeal =
      if a = 0 then ⊤ else
        N13SpecialDivisorCharts.infinityPointIdeal
          1 (D.v.eval a) := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [graphRootPoint]
  split <;> rfl

/-- The infinity ideal contributed by an unordered pair of graph roots. -/
def rootInfinityIdeal
    (D : SemiMumford) :
    Sym2 K → Ideal N13SpecialDivisorCharts.SpecialInfinity :=
  Sym2.lift
    ⟨fun a b =>
        (if a = 0 then ⊤ else
          N13SpecialDivisorCharts.infinityPointIdeal
            1 (D.v.eval a)) *
        (if b = 0 then ⊤ else
          N13SpecialDivisorCharts.infinityPointIdeal
            1 (D.v.eval b)),
      fun a b => by
        dsimp
        rw [mul_comm]⟩

@[simp] theorem rootInfinityIdeal_mk
    (D : SemiMumford) (a b : K) :
    rootInfinityIdeal D s(a, b) =
      (if a = 0 then ⊤ else
        N13SpecialDivisorCharts.infinityPointIdeal
          1 (D.v.eval a)) *
      (if b = 0 then ⊤ else
        N13SpecialDivisorCharts.infinityPointIdeal
          1 (D.v.eval b)) :=
  rfl

/-- The infinity chart ideal of a split root divisor is the product of the
point contributions selected by its two roots. -/
theorem ofDivisor_graphRoots_infinityIdeal
    (D : SemiMumford)
    (z : Sym2 K)
    (hz : ∀ a ∈ z, D.u.IsRoot a) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap (graphRootPoint D) z hz)).infinityIdeal =
      rootInfinityIdeal D z := by
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
        rootInfinityIdeal D s(a, b)
      rw [graphRootPoint_infinityIdeal,
        graphRootPoint_infinityIdeal, rootInfinityIdeal_mk]

/-- The canonical infinity chart ideal of a quadratic special graph is the
explicit product attached to its chosen unordered root pair. -/
theorem ofDivisor_graphDivisor_infinityIdeal
    (D : SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor D hdeg)).infinityIdeal =
      rootInfinityIdeal D
        (N13SpecialGraphDivisor.rootPair D hdeg) := by
  unfold N13SpecialGraphDivisor.graphDivisor
  let hz :
      ∀ a ∈ N13SpecialGraphDivisor.rootPair D hdeg,
        D.u.IsRoot a :=
    fun a ha =>
      (N13SpecialGraphDivisor.mem_rootPair_iff_isRoot
        D hdeg a).mp ha
  have hpmap :
      Sym2.pmap
          (N13SpecialGraphDivisor.rootPoint D hdeg)
          (N13SpecialGraphDivisor.rootPair D hdeg)
          (fun _ ha => ha) =
        Sym2.pmap
          (graphRootPoint D)
          (N13SpecialGraphDivisor.rootPair D hdeg)
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
      (N13SpecialGraphDivisor.rootPair D hdeg) hz

end

end MazurProof.N13SpecialGraphDivisorCharts


