-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_PadeZeroConstantSquare_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_PadeZeroConstantSquare_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:22:04.118078+00:00
-- url     : https://prove2.me/theorems/819c29a5-40d7-49f5-9eb1-4f93d08f96cc
-- title:
--   FLT.Assumptions.MazurProof.PadeZeroConstantSquare source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.PadeZeroConstantSquare

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.PadeZeroConstantSquare
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

set_option autoImplicit false




/-!
# The zero-constant branch of a quadratic Padé relation

Suppose

```
q * l ^ 2 = a ^ 2 * u
```

over a field, where `q` is a unit and `u` is monic of degree at most two.
After dividing `a` and `l` by their gcd, coprimality forces the remaining
factor of `a` to be a unit.  Normalization then shows that `u` is the square
of a monic polynomial of degree at most one.

This is a UFD argument only.  It does not factor either polynomial or
enumerate possible coefficients.
-/

namespace MazurProof.PadeZeroConstantSquare

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

private theorem left_isUnit_of_coprime_sq_relation
    {q a l u : K[X]}
    (hq : IsUnit q)
    (hcop : IsCoprime a l)
    (h : q * l ^ 2 = a ^ 2 * u) :
    IsUnit a := by
  have hcop2 : IsCoprime (a ^ 2) (l ^ 2) :=
    hcop.pow (m := 2) (n := 2)
  have ha2DvdL2q : a ^ 2 ∣ l ^ 2 * q := by
    refine ⟨u, ?_⟩
    calc
      l ^ 2 * q = q * l ^ 2 := by ring
      _ = a ^ 2 * u := h
  have ha2DvdQ : a ^ 2 ∣ q :=
    hcop2.dvd_of_dvd_mul_left ha2DvdL2q
  have ha2Unit : IsUnit (a ^ 2) :=
    isUnit_of_dvd_unit ha2DvdQ hq
  exact isUnit_of_dvd_unit
    ⟨a, by simp only [pow_two]⟩ ha2Unit

/-- A unit-times-square identity with a monic quadratic-or-smaller factor
forces that factor to be a monic square. -/
theorem exists_monic_square_root_of_relation
    {q a l u : K[X]}
    (hq : IsUnit q)
    (hl : l ≠ 0)
    (huMonic : u.Monic)
    (huDeg : u.natDegree ≤ 2)
    (hRelation : q * l ^ 2 = a ^ 2 * u) :
    ∃ b : K[X],
      b.Monic ∧
      b.natDegree ≤ 1 ∧
      u = b ^ 2 := by
  classical
  let g : K[X] := GCDMonoid.gcd a l
  let a0 : K[X] := a / g
  let l0 : K[X] := l / g
  have hg : g ≠ 0 := by
    dsimp only [g]
    exact gcd_ne_zero_of_right hl
  have hga : g * a0 = a := by
    dsimp only [g, a0]
    exact EuclideanDomain.mul_div_cancel'
      (gcd_ne_zero_of_right hl)
      (GCDMonoid.gcd_dvd_left a l)
  have hgl : g * l0 = l := by
    dsimp only [g, l0]
    exact EuclideanDomain.mul_div_cancel'
      (gcd_ne_zero_of_right hl)
      (GCDMonoid.gcd_dvd_right a l)
  have hprimitive : IsCoprime a0 l0 := by
    dsimp only [a0, l0, g]
    exact isCoprime_div_gcd_div_gcd hl
  have hRelation0 : q * l0 ^ 2 = a0 ^ 2 * u := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg)
    calc
      g ^ 2 * (q * l0 ^ 2) =
          q * (g * l0) ^ 2 := by ring
      _ = q * l ^ 2 := by rw [hgl]
      _ = a ^ 2 * u := hRelation
      _ = (g * a0) ^ 2 * u := by rw [hga]
      _ = g ^ 2 * (a0 ^ 2 * u) := by ring
  have ha0Unit : IsUnit a0 :=
    left_isUnit_of_coprime_sq_relation
      hq hprimitive hRelation0
  let b : K[X] := normalize l0
  have hl0 : l0 ≠ 0 := by
    dsimp only [l0, g]
    exact right_div_gcd_ne_zero hl
  have hbMonic : b.Monic := by
    change (normalize l0).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_normalize,
      normalize_eq_one]
    exact isUnit_iff_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hl0)
  have hnorm :=
    congrArg (fun p : K[X] => normalize p) hRelation0
  have hnorm' : (normalize l0) ^ 2 = normalize u := by
    simpa [pow_two, map_mul,
      normalize_eq_one.mpr hq,
      normalize_eq_one.mpr ha0Unit] using hnorm
  have hub : u = b ^ 2 := by
    calc
      u = normalize u := huMonic.normalize_eq_self.symm
      _ = (normalize l0) ^ 2 := hnorm'.symm
      _ = b ^ 2 := rfl
  have hdeg2 : 2 * b.natDegree ≤ 2 := by
    simpa [hub, Polynomial.natDegree_pow] using huDeg
  have hbDeg : b.natDegree ≤ 1 := by
    omega
  exact ⟨b, hbMonic, hbDeg, hub⟩

/-- If `u = b²` and the resultant of `u` and `v` is nonzero, then `b`
and `v` are coprime. -/
theorem isCoprime_squareRoot_of_resultant_ne_zero
    {u b v : K[X]}
    (hu : u ≠ 0)
    (hub : u = b ^ 2)
    (hres : u.resultant v ≠ 0) :
    IsCoprime b v := by
  have huv : IsCoprime u v := by
    by_contra hcop
    apply hres
    exact resultant_eq_zero_iff.mpr
      ⟨Or.inl hu, hcop⟩
  rw [hub] at huv
  exact (IsCoprime.pow_left_iff
    (by norm_num : 0 < 2)).mp huv

/-- Over the rationals, coprimality of `b` and `v` supplies the three-term
Bézout relation used by the repeated-point Cantor square. -/
theorem exists_bezout_b_twoV_bw
    {b v w : ℚ[X]}
    (hcop : IsCoprime b v) :
    ∃ A B E : ℚ[X],
      A * b + B * (2 * v) + E * (b * w) = 1 := by
  obtain ⟨A, B, hAB⟩ := hcop
  refine
    ⟨A, Polynomial.C (1 / 2 : ℚ) * B, 0, ?_⟩
  have htwo :
      (2 : ℚ[X]) = Polynomial.C (2 : ℚ) := by
    exact
      (map_natCast
        (Polynomial.C : ℚ →+* ℚ[X]) 2).symm
  have hhalf :
      Polynomial.C (1 / 2 : ℚ) * (2 : ℚ[X]) = 1 := by
    rw [htwo, ← Polynomial.C_mul]
    norm_num
  calc
    A * b +
          (Polynomial.C (1 / 2 : ℚ) * B) * (2 * v) +
          0 * (b * w) =
        A * b +
          (Polynomial.C (1 / 2 : ℚ) * 2) *
            (B * v) := by
      ring
    _ = A * b + B * v := by
      rw [hhalf, one_mul]
    _ = 1 := hAB

end

end MazurProof.PadeZeroConstantSquare


