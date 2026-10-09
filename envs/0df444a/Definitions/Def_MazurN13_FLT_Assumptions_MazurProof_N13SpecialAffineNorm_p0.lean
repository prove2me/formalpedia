-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineNorm_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineNorm_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:55:10.476994+00:00
-- url     : https://prove2.me/theorems/dd257ccd-1d00-4abf-9228-e6047c5176dd
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialAffineNorm source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialAffineNorm

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialAffineNorm
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialComparisonFactorPair_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual hyperelliptic conjugation and polynomial norm on the good
characteristic-two affine coordinate ring. This is not the bad sextic
obtained by dividing the ordinate by two. Nonzero functions have nonzero
norm, and the comparison factor pair makes the norm divide an explicit
polynomial supported only over x=0 and x=1.
-/

namespace MazurProof.N13SpecialAffineNorm

noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts hiding K

abbrev R := N13GoodCoordinateRingTwo.CoordinateRing

private theorem conjugate_root :
    curvePoly.eval₂ xClassHom (-xClass hPoly - yClass) = 0 := by
  simp only [curvePoly, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, xClassHom_apply]
  linear_combination yClass_relation

def conjugate : R →+* R := AdjoinRoot.lift xClassHom (-xClass hPoly - yClass) conjugate_root

@[simp] theorem conjugate_xClass (p : K[X]) : conjugate (xClass p) = xClass p :=
  AdjoinRoot.lift_of _

@[simp] theorem conjugate_yClass : conjugate yClass = -xClass hPoly - yClass :=
  AdjoinRoot.lift_root _

def linear (p q : K[X]) : R := xClass p + xClass q * yClass

theorem conjugate_linear (p q : K[X]) :
    conjugate (linear p q) = linear (p - q * hPoly) (-q) := by
  simp only [linear, map_add, map_mul, conjugate_xClass, conjugate_yClass,
    xClass_sub, xClass_mul, xClass_neg]
  ring

theorem conjugate_involutive (z : R) : conjugate (conjugate z) = z := by
  have hz : z = linear (coeff0 z) (coeffY z) := (recompose z).symm
  calc
    conjugate (conjugate z) = conjugate (conjugate (linear (coeff0 z) (coeffY z))) := by rw [← hz]
    _ = linear ((coeff0 z - coeffY z * hPoly) - -coeffY z * hPoly) (- -coeffY z) := by
      rw [conjugate_linear, conjugate_linear]
    _ = linear (coeff0 z) (coeffY z) := by congr 1 <;> ring
    _ = z := hz.symm

def normPolynomial (p q : K[X]) : K[X] := p ^ 2 - p * q * hPoly - q ^ 2 * rhsPoly
def norm (z : R) : K[X] := normPolynomial (coeff0 z) (coeffY z)

theorem linear_mul_conjugate (p q : K[X]) :
    linear p q * conjugate (linear p q) = xClass (normPolynomial p q) := by
  rw [conjugate_linear]
  simp only [linear, normPolynomial, xClass_sub, xClass_mul, xClass_pow, xClass_neg]
  linear_combination -(xClass q) ^ 2 * yClass_relation

theorem mul_conjugate (z : R) : z * conjugate z = xClass (norm z) := by
  have he := linear_mul_conjugate (coeff0 z) (coeffY z)
  have hz : linear (coeff0 z) (coeffY z) = z := recompose z
  rw [hz] at he
  exact he

theorem norm_ne_zero (z : R) (hz : z ≠ 0) : norm z ≠ 0 := by
  intro hn
  have hp := mul_conjugate z
  rw [hn, xClass_zero] at hp
  rcases mul_eq_zero.mp hp with h | h
  · exact hz h
  · have hc := congrArg conjugate h
    rw [conjugate_involutive, map_zero] at hc
    exact hz hc

theorem xClass_injective : Function.Injective xClass := by
  intro p q hpq
  apply sub_eq_zero.mp
  by_contra h
  apply xClass_ne_zero h
  rw [xClass_sub, hpq, sub_self]

theorem norm_mul (z w : R) : norm (z * w) = norm z * norm w := by
  apply xClass_injective
  rw [xClass_mul, ← mul_conjugate, ← mul_conjugate, ← mul_conjugate, map_mul]
  ring

theorem norm_xClass (p : K[X]) : norm (xClass p) = p ^ 2 := by
  apply xClass_injective
  rw [← mul_conjugate, conjugate_xClass, xClass_pow, pow_two]

theorem normPolynomial_degree_le_eight (p q : K[X])
    (hp : p.natDegree ≤ 4) (hq : q.natDegree ≤ 1) :
    (normPolynomial p q).natDegree ≤ 8 := by
  have hp2 := Polynomial.natDegree_pow_le (p := p) (n := 2)
  have hq2 := Polynomial.natDegree_pow_le (p := q) (n := 2)
  have hpq := Polynomial.natDegree_mul_le (p := p) (q := q)
  have hpqh := Polynomial.natDegree_mul_le (p := p * q) (q := hPoly)
  have hqr := Polynomial.natDegree_mul_le (p := q ^ 2) (q := rhsPoly)
  have hsub := Polynomial.natDegree_sub_le (p ^ 2) (p * q * hPoly)
  have hsub' := Polynomial.natDegree_sub_le (p ^ 2 - p * q * hPoly) (q ^ 2 * rhsPoly)
  rw [hPoly_natDegree] at hpqh
  rw [rhsPoly_natDegree] at hqr
  unfold normPolynomial
  omega

open N13SpecialComparisonFactorPair hiding xClass R

/-- The arbitrary comparison already forces the cleared numerator norm to
divide a polynomial with support only at the two finite rational fibres.
No enumeration or principal-code compatibility is used. -/
theorem exists_factor_pair_with_supported_norm
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ z w : R, ∃ i j : ℕ,
      i + j ≤ 16 ∧ z ≠ 0 ∧ w ≠ 0 ∧
      h.aNum * xClass (tensorPolynomial D E) = h.aDen * z ∧
      h.aDen * xClass (tensorPolynomial F H) = h.aNum * w ∧
      norm z * norm w = X ^ i * (X - 1) ^ j ∧
      norm z ∣ X ^ i * (X - 1) ^ j := by
  obtain ⟨z, w, _, _, hz, hw, hprod, hz0, hw0⟩ := exists_factor_pair_of_comparison D E F H h
  obtain ⟨i, j, hij, hleft⟩ := tensorPolynomial_fibres D E
  obtain ⟨k, l, hkl, hright⟩ := tensorPolynomial_fibres F H
  have hn : norm z * norm w = X ^ (2 * (i + k)) * (X - 1) ^ (2 * (j + l)) := by
    rw [← norm_mul, hprod, norm_xClass, hleft, hright]
    rw [Nat.mul_comm 2 (i + k), Nat.mul_comm 2 (j + l), pow_mul, pow_mul, pow_add, pow_add]
    ring
  refine ⟨z, w, 2 * (i + k), 2 * (j + l), by omega, hz0, hw0, hz, hw, hn, ?_⟩
  exact ⟨norm w, hn.symm⟩

end
end MazurProof.N13SpecialAffineNorm


