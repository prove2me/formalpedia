-- Prove2me | Definitions.Def_MazurN13_DirectProofSupport2of21_p0
-- name    : MazurN13_DirectProofSupport2of21_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T13:17:52.728127+00:00
-- url     : https://prove2.me/theorems/555a8468-a856-4407-a3e6-a5b8f9ac4b9b
-- title:
--   Order-thirteen exclusion proof support, part 2 of 21
-- statement:
--   Verified auxiliary constructions and lemmas used in the formal proof excluding rational points of order thirteen on elliptic curves over the rationals. This part retains source declarations in dependency order.
-- source:
--   https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580 (N13 formalization; source reconstruction and two elaboration repairs retained locally)

import Definitions.Def_MazurN13_DirectProofSupport1of21_p0


section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TateNFDivision
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Division polynomials at the Tate normal form origin

For the Tate normal form `y² + (1-c)xy - by = x³ - bx²` with marked point
`P = (0,0)`, the division polynomials `ψₙ` evaluated at `P` factor as
`ψₙ(P) = b^eₙ · Fₙ(b,c)` where `Fₙ` is a small polynomial.

The condition "P has exact order n" is `Fₙ(b,c) = 0` (with `b ≠ 0` and
nonsingularity).  These compact factors are the foundation for all cyclic
torsion exclusions via Tate normal form.

## References

* Kubert, "Universal bounds on the torsion of elliptic curves", 1976
* The division polynomial recurrence specialized at the origin
-/

namespace MazurProof.TateNFDivision

variable {K : Type*} [Field K]

/-! ## Tate normal form curve and origin -/

/-- The Tate normal form `y² + (1-c)xy - by = x³ - bx²`. -/
def tateCurve (b c : K) : WeierstrassCurve K where
  a₁ := 1 - c
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

/-! ## Weierstrass invariants of the Tate normal form -/

theorem tate_b₂ (b c : K) : (tateCurve b c).b₂ = (1 - c) ^ 2 - 4 * b := by
  simp [tateCurve, WeierstrassCurve.b₂]; ring

theorem tate_b₄ (b c : K) : (tateCurve b c).b₄ = b * (c - 1) := by
  simp [tateCurve, WeierstrassCurve.b₄]; ring

theorem tate_b₆ (b c : K) : (tateCurve b c).b₆ = b ^ 2 := by
  simp [tateCurve, WeierstrassCurve.b₆]

theorem tate_b₈ (b c : K) : (tateCurve b c).b₈ = -b ^ 3 := by
  simp [tateCurve, WeierstrassCurve.b₈]; ring

/-! ## Compact factors of ψₙ(0,0) / b^eₙ

These are the NON-trivial factors after removing the power of `b`.
The order-n condition at the Tate origin is `Fₙ(b,c) = 0`.
-/

/-- `ψ₅(0,0) / b⁸ = b - c`.  Order 5 at origin ⟺ `c = b`. -/
def F5 (b c : K) : K := b - c

/-- `ψ₆(0,0) / b¹² = b - c - c²`.  Order 6 at origin ⟺ `c² + c = b`. -/
def F6 (b c : K) : K := b - c - c ^ 2

/-- `ψ₇(0,0) / b¹⁶ = c³ - b² + bc`.  Order 7 at origin. -/
def F7 (b c : K) : K := c ^ 3 - b ^ 2 + b * c

/-- `ψ₈(0,0) / (-b²¹c) = 2b² - 3bc - bc² + c²`.  Order 8 at origin
    requires additionally `c ≠ 0`. -/
def F8 (b c : K) : K := 2 * b ^ 2 - 3 * b * c - b * c ^ 2 + c ^ 2

/-- `ψ₉(0,0) / b²⁷ = (b-c)³ + c³(b-c-c²)`.  Order 9 at origin. -/
def F9 (b c : K) : K := (b - c) ^ 3 + c ^ 3 * (b - c - c ^ 2)

/-- `ψ₁₁(0,0) / b⁴⁰`.  11 monomials, total degree 8. -/
def F11 (b c : K) : K :=
  (c ^ 3 - b * (b - c)) * (b - c) ^ 3 - b * c * (b - c - c ^ 2) ^ 3

/-- `-ψ₁₃(0,0) / b⁵⁶`.  20 monomials, total degree 11. -/
def F13 (b c : K) : K :=
  (b - c) * (c ^ 3 - b * (b - c)) ^ 3 +
    b * c * F8 b c * (b - c - c ^ 2) ^ 3

/-- `ψ₁₅(0,0) / b⁷⁵ = F9 · F7³ + (b-c-c²) · c³ · F8³`. -/
def F15 (b c : K) : K :=
  F9 b c * F7 b c ^ 3 + (b - c - c ^ 2) * c ^ 3 * F8 b c ^ 3

/-- `ψ₁₇(0,0) / b⁹⁶`.  53 monomials, total degree 12–19. -/
def F17 (b c : K) : K :=
    b ^ 12
      - 10 * b ^ 11 * c
      + 10 * b ^ 10 * c ^ 3
      + 45 * b ^ 10 * c ^ 2
      - 39 * b ^ 9 * c ^ 5
      - 75 * b ^ 9 * c ^ 4
      - 120 * b ^ 9 * c ^ 3
      + 50 * b ^ 8 * c ^ 7
      + 249 * b ^ 8 * c ^ 6
      + 246 * b ^ 8 * c ^ 5
      + 210 * b ^ 8 * c ^ 4
      - 31 * b ^ 7 * c ^ 9
      - 246 * b ^ 7 * c ^ 8
      - 681 * b ^ 7 * c ^ 7
      - 461 * b ^ 7 * c ^ 6
      - 252 * b ^ 7 * c ^ 5
      + 9 * b ^ 6 * c ^ 11
      + 105 * b ^ 6 * c ^ 10
      + 485 * b ^ 6 * c ^ 9
      + 1035 * b ^ 6 * c ^ 8
      + 540 * b ^ 6 * c ^ 7
      + 210 * b ^ 6 * c ^ 6
      - b ^ 5 * c ^ 13
      - 15 * b ^ 5 * c ^ 12
      - 120 * b ^ 5 * c ^ 11
      - 469 * b ^ 5 * c ^ 10
      - 945 * b ^ 5 * c ^ 9
      - 405 * b ^ 5 * c ^ 8
      - 120 * b ^ 5 * c ^ 7
      + 30 * b ^ 4 * c ^ 12
      + 195 * b ^ 4 * c ^ 11
      + 519 * b ^ 4 * c ^ 10
      + 190 * b ^ 4 * c ^ 9
      + 45 * b ^ 4 * c ^ 8
      + 15 * b ^ 3 * c ^ 14
      + 45 * b ^ 3 * c ^ 13
      + 20 * b ^ 3 * c ^ 12
      - 159 * b ^ 3 * c ^ 11
      - 51 * b ^ 3 * c ^ 10
      - 10 * b ^ 3 * c ^ 9
      - 2 * b ^ 2 * c ^ 16
      - 15 * b ^ 2 * c ^ 15
      - 39 * b ^ 2 * c ^ 14
      - 49 * b ^ 2 * c ^ 13
      + 21 * b ^ 2 * c ^ 12
      + 6 * b ^ 2 * c ^ 11
      + b ^ 2 * c ^ 10
      + b * c ^ 18
      + 3 * b * c ^ 17
      + 6 * b * c ^ 16
      + 10 * b * c ^ 15
      + 15 * b * c ^ 14
      - c ^ 15

/-- `-ψ₁₉(0,0) / b¹²⁰`.  80 monomials, total degree 15–24. -/
def F19 (b c : K) : K :=
    b ^ 15
      - 10 * b ^ 14 * c
      - 20 * b ^ 13 * c ^ 3
      + 45 * b ^ 13 * c ^ 2
      + 69 * b ^ 12 * c ^ 5
      + 195 * b ^ 12 * c ^ 4
      - 120 * b ^ 12 * c ^ 3
      - 121 * b ^ 11 * c ^ 7
      - 588 * b ^ 11 * c ^ 6
      - 861 * b ^ 11 * c ^ 5
      + 210 * b ^ 11 * c ^ 4
      + 105 * b ^ 10 * c ^ 9
      + 870 * b ^ 10 * c ^ 8
      + 2235 * b ^ 10 * c ^ 7
      + 2275 * b ^ 10 * c ^ 6
      - 252 * b ^ 10 * c ^ 5
      - 48 * b ^ 9 * c ^ 11
      - 585 * b ^ 9 * c ^ 10
      - 2720 * b ^ 9 * c ^ 9
      - 4995 * b ^ 9 * c ^ 8
      - 4005 * b ^ 9 * c ^ 7
      + 210 * b ^ 9 * c ^ 6
      + 11 * b ^ 8 * c ^ 13
      + 183 * b ^ 8 * c ^ 12
      + 1320 * b ^ 8 * c ^ 11
      + 4851 * b ^ 8 * c ^ 10
      + 7290 * b ^ 8 * c ^ 9
      + 4950 * b ^ 8 * c ^ 8
      - 120 * b ^ 8 * c ^ 7
      - b ^ 7 * c ^ 15
      - 21 * b ^ 7 * c ^ 14
      - 231 * b ^ 7 * c ^ 13
      - 1531 * b ^ 7 * c ^ 12
      - 5466 * b ^ 7 * c ^ 11
      - 7308 * b ^ 7 * c ^ 10
      - 4410 * b ^ 7 * c ^ 9
      + 45 * b ^ 7 * c ^ 8
      + 120 * b ^ 6 * c ^ 14
      + 990 * b ^ 6 * c ^ 13
      + 4117 * b ^ 6 * c ^ 12
      + 5166 * b ^ 6 * c ^ 11
      + 2862 * b ^ 6 * c ^ 10
      - 10 * b ^ 6 * c ^ 9
      - 34 * b ^ 5 * c ^ 16
      - 165 * b ^ 5 * c ^ 15
      - 465 * b ^ 5 * c ^ 14
      - 2190 * b ^ 5 * c ^ 13
      - 2610 * b ^ 5 * c ^ 12
      - 1350 * b ^ 5 * c ^ 11
      + b ^ 5 * c ^ 10
      + 25 * b ^ 4 * c ^ 18
      + 150 * b ^ 4 * c ^ 17
      + 363 * b ^ 4 * c ^ 16
      + 320 * b ^ 4 * c ^ 15
      + 885 * b ^ 4 * c ^ 14
      + 945 * b ^ 4 * c ^ 13
      + 455 * b ^ 4 * c ^ 12
      - 6 * b ^ 3 * c ^ 20
      - 45 * b ^ 3 * c ^ 19
      - 161 * b ^ 3 * c ^ 18
      - 333 * b ^ 3 * c ^ 17
      - 225 * b ^ 3 * c ^ 16
      - 281 * b ^ 3 * c ^ 15
      - 240 * b ^ 3 * c ^ 14
      - 105 * b ^ 3 * c ^ 13
      + b ^ 2 * c ^ 22
      + 6 * b ^ 2 * c ^ 21
      + 21 * b ^ 2 * c ^ 20
      + 56 * b ^ 2 * c ^ 19
      + 126 * b ^ 2 * c ^ 18
      + 81 * b ^ 2 * c ^ 17
      + 61 * b ^ 2 * c ^ 16
      + 39 * b ^ 2 * c ^ 15
      + 15 * b ^ 2 * c ^ 14
      - 15 * b * c ^ 19
      - 10 * b * c ^ 18
      - 6 * b * c ^ 17
      - 3 * b * c ^ 16
      - b * c ^ 15
      - c ^ 21

/-! ## Expanded forms (useful for ring-level reasoning) -/

@[simp] theorem F5_eq (b c : K) : F5 b c = b - c := rfl

@[simp] theorem F6_eq (b c : K) : F6 b c = b - c - c ^ 2 := rfl

theorem F7_expanded (b c : K) : F7 b c = c ^ 3 + b * c - b ^ 2 := by
  unfold F7; ring

theorem F8_expanded (b c : K) :
    F8 b c = 2 * b ^ 2 - 3 * b * c - b * c ^ 2 + c ^ 2 := by
  unfold F8; ring

theorem F9_expanded (b c : K) :
    F9 b c = b ^ 3 - 3 * b ^ 2 * c + 3 * b * c ^ 2 - c ^ 3
           + b * c ^ 3 - c ^ 4 - c ^ 5 := by
  unfold F9; ring

theorem F11_expanded (b c : K) :
    F11 b c =
      - b ^ 5 + 3 * b ^ 4 * c - 3 * b ^ 3 * c ^ 2 + b ^ 2 * c ^ 3
      + 4 * b ^ 3 * c ^ 3 - 9 * b ^ 2 * c ^ 4 + 6 * b * c ^ 5 - c ^ 6
      - 3 * b ^ 2 * c ^ 5 + 3 * b * c ^ 6 + b * c ^ 7 := by
  unfold F11; ring

/-! ## Two-division polynomial (for rational 2-torsion detection) -/

/-- The 2-division x-polynomial for the Tate normal form.
    A rational root gives a rational 2-torsion point. -/
def T2 (b c X : K) : K :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

/-- The 3-division x-polynomial for the Tate normal form. -/
def Psi3X (b c X : K) : K :=
  3 * X ^ 4 + ((1 - c) ^ 2 - 4 * b) * X ^ 3 +
    3 * (b * (c - 1)) * X ^ 2 + 3 * b ^ 2 * X - b ^ 3

/-! ## Relation to Weierstrass invariants -/

theorem T2_eq_twoDiv (b c X : K) :
    T2 b c X = 4 * X ^ 3 + (tateCurve b c).b₂ * X ^ 2
             + 2 * (tateCurve b c).b₄ * X + (tateCurve b c).b₆ := by
  unfold T2; rw [tate_b₂, tate_b₄, tate_b₆]; ring

/-! ## Order conditions at the Tate origin

Exact order `n` at the origin means `Fₙ(b,c) = 0` and all proper divisor
conditions are nonzero.
-/

/-- Exact order 4: `c = 0` (with `b ≠ 0`). -/
def ExactOrder4 (b c : K) : Prop :=
  b ≠ 0 ∧ c = 0

/-- Exact order 5: `b = c` (with `b ≠ 0`). -/
def ExactOrder5 (b c : K) : Prop :=
  b ≠ 0 ∧ F5 b c = 0

/-- Exact order 7: `F7(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder7 (b c : K) : Prop :=
  b ≠ 0 ∧ F7 b c = 0

/-- Exact order 8: `F8(b,c) = 0` (with `b ≠ 0`, `c ≠ 0`). -/
def ExactOrder8 (b c : K) : Prop :=
  b ≠ 0 ∧ c ≠ 0 ∧ F8 b c = 0

/-- Exact order 9: `F9(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder9 (b c : K) : Prop :=
  b ≠ 0 ∧ F9 b c = 0

/-- Exact order 11: `F11(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder11 (b c : K) : Prop :=
  b ≠ 0 ∧ F11 b c = 0

/-- Exact order 13: `F13(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder13 (b c : K) : Prop :=
  b ≠ 0 ∧ F13 b c = 0

/-! ## Composite order systems via coprime decomposition -/

/-- A rational point of order 2 exists on `E(b,c)`: the 2-division cubic has
    a rational root. -/
def HasRational2Torsion (b c : K) : Prop :=
  ∃ X : K, T2 b c X = 0

/-- A rational point of order 3 exists on `E(b,c)`: the 3-division polynomial
    has a rational root, and the curve equation is satisfied. -/
def HasRational3Torsion (b c : K) : Prop :=
  ∃ X Y : K,
    Y ^ 2 + (1 - c) * X * Y - b * Y = X ^ 3 - b * X ^ 2 ∧
    Psi3X b c X = 0

/-- System for order 14 = 2 · 7: origin has order 7, plus rational 2-torsion. -/
def Obstruction14 (b c : K) : Prop :=
  ExactOrder7 b c ∧ HasRational2Torsion b c

/-- System for order 18 = 2 · 9: origin has order 9, plus rational 2-torsion. -/
def Obstruction18 (b c : K) : Prop :=
  ExactOrder9 b c ∧ HasRational2Torsion b c

/-- System for order 20 = 4 · 5: origin has order 4 (c=0), plus rational
    5-torsion (separate point). -/
def Obstruction20 (b c : K) : Prop :=
  ExactOrder4 b c ∧ F5 b c = 0

/-- System for order 21 = 3 · 7: origin has order 7, plus rational 3-torsion. -/
def Obstruction21 (b c : K) : Prop :=
  ExactOrder7 b c ∧ HasRational3Torsion b c

/-- System for order 24 = 3 · 8: origin has order 8, plus rational 3-torsion. -/
def Obstruction24 (b c : K) : Prop :=
  ExactOrder8 b c ∧ HasRational3Torsion b c

end MazurProof.TateNFDivision


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TateBridge
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The Tate-normal-form bridge to the optimized model of `X₁(13)`

This file isolates the birational geometry in the order-13 argument.  The
high-degree Tate division factor is first reduced, by Kubert's standard
substitution

`b = r s (r - 1)`, `c = s (r - 1)`,

to a low-degree plane model.  A second birational map sends its
nondegenerate locus to the optimized genus-two model

`y² + (x³ + x² + 1)y = x² + x`.

All identities below are identities of rational functions.  No rational-point
classification is used here.
-/

namespace MazurProof.N13TateBridge

/-- Kubert's raw affine equation for `X₁(13)`. -/
def rawF13 (r s : ℚ) : ℚ :=
  r ^ 3 - r ^ 2 * s ^ 4 + 5 * r ^ 2 * s ^ 3 - 9 * r ^ 2 * s ^ 2
    + 4 * r ^ 2 * s - 2 * r ^ 2 - r * s ^ 3 + 6 * r * s ^ 2
    - 3 * r * s + r - s ^ 3

/-- The optimized affine genus-two model of `X₁(13)`. -/
def C13OptEq (x y : ℚ) : Prop :=
  y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y = x ^ 2 + x

/-- A convenient affine open avoiding all four affine rational cusps. -/
def OptNonCusp13 (x y : ℚ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ y + 1 ≠ 0

/-- The nondegenerate part of Kubert's raw affine chart. -/
def RawNondegenerate13 (r s : ℚ) : Prop :=
  r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ s ≠ r

/-- The two-step Kubert substitution factors the Tate division condition. -/
theorem tateF13_substitution (r s : ℚ) :
    TateNFDivision.F13 (r * s * (r - 1)) (s * (r - 1)) =
      -s ^ 7 * (r - 1) ^ 11 * rawF13 r s := by
  simp only [TateNFDivision.F13, TateNFDivision.F8, rawF13]
  ring

theorem rawF13_at_s_one (r : ℚ) :
    rawF13 r 1 = (r - 1) ^ 3 := by
  simp [rawF13]
  ring

theorem rawF13_at_diagonal (r : ℚ) :
    rawF13 r r = -r * (r - 1) ^ 5 := by
  simp [rawF13]
  ring

/-- A nonzero Tate solution gives a point on the nondegenerate raw chart. -/
theorem raw_point_of_tateF13
    {b c : ℚ} (hb : b ≠ 0) (hF : TateNFDivision.F13 b c = 0) :
    ∃ r s : ℚ,
      rawF13 r s = 0 ∧ RawNondegenerate13 r s ∧
        b = r * s * (r - 1) ∧ c = s * (r - 1) := by
  have hc : c ≠ 0 := by
    intro hc
    subst c
    apply (pow_ne_zero 7 hb)
    rw [TateNFDivision.F13, TateNFDivision.F8] at hF
    ring_nf at hF ⊢
    exact neg_eq_zero.mp hF
  have hbc : b ≠ c := by
    intro hbc
    subst c
    apply (pow_ne_zero 11 hb)
    rw [TateNFDivision.F13, TateNFDivision.F8] at hF
    ring_nf at hF ⊢
    exact hF
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hr0 : r ≠ 0 := by
    exact div_ne_zero hb hc
  have hr1 : r ≠ 1 := by
    intro hr
    apply hbc
    apply (div_eq_one_iff_eq hc).mp
    exact hr
  have hs0 : s ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 hc) (sub_ne_zero.mpr hbc)
  have hb_param : b = r * s * (r - 1) := by
    dsimp [r, s]
    field_simp
  have hc_param : c = s * (r - 1) := by
    dsimp [r, s]
    field_simp
  have hraw : rawF13 r s = 0 := by
    have hfactor :
        -s ^ 7 * (r - 1) ^ 11 * rawF13 r s = 0 := by
      rw [← tateF13_substitution, ← hb_param, ← hc_param, hF]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero
        (neg_ne_zero.mpr (pow_ne_zero 7 hs0))
        (pow_ne_zero 11 (sub_ne_zero.mpr hr1)))
  have hs1 : s ≠ 1 := by
    intro hs
    have hpow : (r - 1) ^ 3 = 0 := by
      rw [← rawF13_at_s_one]
      simpa [hs] using hraw
    exact (pow_ne_zero 3 (sub_ne_zero.mpr hr1)) hpow
  have hsr : s ≠ r := by
    intro hs
    have hzero : -r * (r - 1) ^ 5 = 0 := by
      rw [← rawF13_at_diagonal]
      simpa [hs] using hraw
    exact (mul_ne_zero
      (neg_ne_zero.mpr hr0)
      (pow_ne_zero 5 (sub_ne_zero.mpr hr1))) hzero
  exact ⟨r, s, hraw, ⟨hr0, hr1, hs0, hs1, hsr⟩, hb_param, hc_param⟩

/-- The inverse birational map from the raw chart to the optimized model. -/
def rawToOptX (r s : ℚ) : ℚ :=
  (1 - r) * (1 - s) / (s - r)

/-- The second coordinate of the inverse birational map. -/
def rawToOptY (r s : ℚ) : ℚ :=
  (s - r) / (1 - s)

/-- The raw-to-optimized map lands on the optimized genus-two equation. -/
theorem rawToOpt_mem
    {r s : ℚ} (hraw : rawF13 r s = 0)
    (hs1 : s ≠ 1) (hsr : s ≠ r) :
    C13OptEq (rawToOptX r s) (rawToOptY r s) := by
  unfold C13OptEq rawToOptX rawToOptY
  field_simp [sub_ne_zero.mpr hsr, sub_ne_zero.mpr (Ne.symm hs1)]
  unfold rawF13 at hraw
  linear_combination (r - 1) * hraw

/-- On the nondegenerate chart the optimized point maps back to `(r,s)`. -/
theorem optToRaw_roundtrip
    {r s : ℚ} (hr1 : r ≠ 1) (hs1 : s ≠ 1) (hsr : s ≠ r) :
    let x := rawToOptX r s
    let y := rawToOptY r s
    r = 1 - x * y ∧ s = 1 - x * y / (y + 1) := by
  dsimp [rawToOptX, rawToOptY]
  have hrs : s - r ≠ 0 := sub_ne_zero.mpr hsr
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hxy :
      ((1 - r) * (1 - s) / (s - r)) * ((s - r) / (1 - s)) =
        1 - r := by
    field_simp [hrs, h1s]
  have hyone :
      (s - r) / (1 - s) + 1 = (1 - r) / (1 - s) := by
    field_simp [h1s]
    ring
  constructor
  · rw [hxy]
    ring
  · rw [hxy, hyone]
    field_simp [h1r, h1s]
    ring

/-- A nondegenerate raw point maps away from all affine rational cusps. -/
theorem rawToOpt_noncusp
    {r s : ℚ} (hnd : RawNondegenerate13 r s) :
    OptNonCusp13 (rawToOptX r s) (rawToOptY r s) := by
  rcases hnd with ⟨_, hr1, _, hs1, hsr⟩
  have hrs : s - r ≠ 0 := sub_ne_zero.mpr hsr
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  constructor
  · exact div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hr1))
        (sub_ne_zero.mpr (Ne.symm hs1)))
      hrs
  constructor
  · exact div_ne_zero hrs h1s
  · unfold rawToOptY
    have hyone :
        (s - r) / (1 - s) + 1 = (1 - r) / (1 - s) := by
      field_simp [h1s]
      ring
    rw [hyone]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hr1)) h1s

/-- The complete Tate-to-optimized-model bridge for order 13. -/
theorem exists_C13Opt_point_of_tateF13
    {b c : ℚ} (hb : b ≠ 0) (hF : TateNFDivision.F13 b c = 0) :
    ∃ x y : ℚ, C13OptEq x y ∧ OptNonCusp13 x y := by
  obtain ⟨r, s, hraw, hnd, _, _⟩ := raw_point_of_tateF13 hb hF
  exact ⟨rawToOptX r s, rawToOptY r s,
    rawToOpt_mem hraw hnd.2.2.2.1 hnd.2.2.2.2,
    rawToOpt_noncusp hnd⟩

end MazurProof.N13TateBridge


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CurveModel
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Equivalent affine models of `X₁(13)`

The optimized generalized model from `N13TateBridge` is completed to the
standard even-degree hyperelliptic model

`Y² = X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`

by the elementary change of variables

`X = -x - 1`, `Y = 2y + x³ + x² + 1`.

This exposes the four affine cusps as the points over `X = 0,-1`.  The two
remaining cusps are the two points at infinity on the smooth projective
completion; they do not occur in the affine Tate chart.
-/

namespace MazurProof.N13CurveModel

open N13TateBridge

/-- The standard sextic defining the hyperelliptic model of `X₁(13)`. -/
def sexticF13 (X : ℚ) : ℚ :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

/-- The affine standard hyperelliptic model of `X₁(13)`. -/
def C13SexticEq (X Y : ℚ) : Prop :=
  Y ^ 2 = sexticF13 X

/-- First coordinate of the optimized-to-sextic change of variables. -/
def optToSexticX (x : ℚ) : ℚ :=
  -x - 1

/-- Second coordinate of the optimized-to-sextic change of variables. -/
def optToSexticY (x y : ℚ) : ℚ :=
  2 * y + x ^ 3 + x ^ 2 + 1

/-- First coordinate of the inverse change of variables. -/
def sexticToOptX (X : ℚ) : ℚ :=
  -X - 1

/-- Second coordinate of the inverse change of variables. -/
def sexticToOptY (X Y : ℚ) : ℚ :=
  (Y - ((-X - 1) ^ 3 + (-X - 1) ^ 2 + 1)) / 2

/-- Completing the square and translating `x ↦ -x-1` gives the sextic. -/
theorem completed_square_identity (x y : ℚ) :
    optToSexticY x y ^ 2 =
      sexticF13 (optToSexticX x) +
        4 * (y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - (x ^ 2 + x)) := by
  simp only [optToSexticY, optToSexticX, sexticF13]
  ring

/-- The change of variables sends the optimized model to the sextic model. -/
theorem optToSextic_mem
    {x y : ℚ} (h : C13OptEq x y) :
    C13SexticEq (optToSexticX x) (optToSexticY x y) := by
  have hzero :
      y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - (x ^ 2 + x) = 0 :=
    sub_eq_zero.mpr h
  rw [C13SexticEq, completed_square_identity, hzero]
  ring

theorem sextic_opt_x_roundtrip (x : ℚ) :
    sexticToOptX (optToSexticX x) = x := by
  simp [sexticToOptX, optToSexticX]

theorem sextic_opt_y_roundtrip (x y : ℚ) :
    sexticToOptY (optToSexticX x) (optToSexticY x y) = y := by
  simp only [sexticToOptY, optToSexticX, optToSexticY]
  ring

theorem opt_sextic_x_roundtrip (X : ℚ) :
    optToSexticX (sexticToOptX X) = X := by
  simp [sexticToOptX, optToSexticX]

theorem opt_sextic_y_roundtrip (X Y : ℚ) :
    optToSexticY (sexticToOptX X) (sexticToOptY X Y) = Y := by
  simp only [optToSexticY, sexticToOptX, sexticToOptY]
  ring

/-- The inverse change of variables sends the sextic model to the optimized
model. -/
theorem sexticToOpt_mem
    {X Y : ℚ} (h : C13SexticEq X Y) :
    C13OptEq (sexticToOptX X) (sexticToOptY X Y) := by
  have hforward := completed_square_identity
    (sexticToOptX X) (sexticToOptY X Y)
  rw [opt_sextic_x_roundtrip, opt_sextic_y_roundtrip] at hforward
  rw [C13OptEq]
  have hres :
      sexticToOptY X Y ^ 2 +
          (sexticToOptX X ^ 3 + sexticToOptX X ^ 2 + 1) *
            sexticToOptY X Y -
        (sexticToOptX X ^ 2 + sexticToOptX X) = 0 := by
    rw [C13SexticEq] at h
    linarith
  exact sub_eq_zero.mp hres

@[simp] theorem sexticF13_zero : sexticF13 0 = 1 := by
  norm_num [sexticF13]

@[simp] theorem sexticF13_neg_one : sexticF13 (-1) = 1 := by
  norm_num [sexticF13]

/-- The four visible affine points above `X=0,-1` lie on the curve. -/
theorem affine_cusp_mem
    {X Y : ℚ} (hX : X = 0 ∨ X = -1) (hY : Y = 1 ∨ Y = -1) :
    C13SexticEq X Y := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
    norm_num [C13SexticEq]

/-- On the optimized curve, a point in the Tate open cannot have `x=-1`. -/
theorem opt_x_ne_neg_one
    {x y : ℚ} (hcurve : C13OptEq x y) (hnon : OptNonCusp13 x y) :
    x ≠ -1 := by
  intro hx
  subst x
  have hyprod : y * (y + 1) = 0 := by
    unfold C13OptEq at hcurve
    norm_num at hcurve
    nlinarith
  rcases mul_eq_zero.mp hyprod with hy | hy
  · exact hnon.2.1 hy
  · exact hnon.2.2 hy

/-- A point in the noncuspidal Tate open maps away from both affine cusp
fibers of the sextic model. -/
theorem optToSextic_nonexceptional
    {x y : ℚ} (hcurve : C13OptEq x y) (hnon : OptNonCusp13 x y) :
    C13SexticEq (optToSexticX x) (optToSexticY x y) ∧
      optToSexticX x ≠ 0 ∧ optToSexticX x ≠ -1 := by
  refine ⟨optToSextic_mem hcurve, ?_, ?_⟩
  · intro hzero
    apply opt_x_ne_neg_one hcurve hnon
    unfold optToSexticX at hzero
    linarith
  · intro hneg
    exact hnon.1 (by
      unfold optToSexticX at hneg
      linarith)

end MazurProof.N13CurveModel


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13Mumford
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The smooth sextic and Mumford model for `X₁(13)`

This file instantiates the curve-independent balanced Mumford layer with the
standard sextic model of `X₁(13)`.  Smoothness is proved by a short Bézout
identity between the sextic and its derivative.
-/

open Polynomial

namespace MazurProof.N13Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

/-- The standard sextic over an arbitrary characteristic-zero field. -/
def f : K[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

private def fQ : ℚ[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

omit [CharZero K] in
theorem f_monic : (f K).Monic := by
  unfold f
  monicity!

theorem f_natDegree : (f K).natDegree = 6 := by
  unfold f
  compute_degree!

private def bezoutA : ℚ[X] :=
  300 * X ^ 4 + 784 * X ^ 3 + 606 * X ^ 2 - 192 * X + 234

private def bezoutB : ℚ[X] :=
  -50 * X ^ 5 - 164 * X ^ 4 - 177 * X ^ 3 + 40 * X ^ 2 - 73 * X - 65

private theorem C_nat (n : ℕ) : C (n : ℚ) = (n : ℚ[X]) := by
  exact map_natCast (C : ℚ →+* ℚ[X]) n

private theorem fQ_derivative :
    fQ.derivative =
      6 * X ^ 5 + 20 * X ^ 4 + 24 * X ^ 3 + 6 * X ^ 2 + 2 * X + 2 := by
  simp only [fQ, derivative_add, derivative_one, derivative_X, derivative_pow,
    derivative_ofNat, derivative_mul, zero_mul, zero_add, add_zero]
  rw [C_nat 2, C_nat 3, C_nat 4, C_nat 5, C_nat 6]
  ring

/-- A small fixed smoothness certificate for the `X₁(13)` sextic. -/
theorem fQ_bezout_derivative :
    bezoutA * fQ + bezoutB * fQ.derivative = 104 := by
  rw [fQ_derivative]
  simp only [bezoutA, bezoutB, fQ]
  ring

private theorem fQ_separable : fQ.Separable := by
  rw [separable_def']
  refine ⟨C (1 / 104 : ℚ) * bezoutA, C (1 / 104 : ℚ) * bezoutB, ?_⟩
  calc
    (C (1 / 104 : ℚ) * bezoutA) * fQ +
        (C (1 / 104 : ℚ) * bezoutB) * fQ.derivative =
      C (1 / 104 : ℚ) * (bezoutA * fQ + bezoutB * fQ.derivative) := by
        ring
    _ = C (1 / 104 : ℚ) * 104 := by rw [fQ_bezout_derivative]
    _ = C (1 / 104 : ℚ) * C 104 := by rw [C_ofNat]
    _ = 1 := by rw [← C_mul]; norm_num

private theorem f_eq_map :
    f K = fQ.map (algebraMap ℚ K) := by
  simp [f, fQ]

theorem f_separable : (f K).Separable := by
  rw [f_eq_map]
  exact (separable_map (algebraMap ℚ K)).mpr fQ_separable

theorem f_squarefree : Squarefree (f K) :=
  (f_separable K).squarefree

/-- The `X₁(13)` instance of the generic smooth monic sextic model. -/
def model : SexticMumford.Model K where
  f := f K
  monic := f_monic K
  natDegree := f_natDegree K
  separable := f_separable K
  two_ne_zero := by norm_num

@[simp] theorem model_f :
    (model K).f = f K := rfl

theorem f_eval_eq_sexticF13 (x : ℚ) :
    (f ℚ).eval x = N13CurveModel.sexticF13 x := by
  simp [f, N13CurveModel.sexticF13]

abbrev CoordinateRing : Type u :=
  SexticMumford.CoordinateRing (model K)

abbrev FunctionField : Type u :=
  SexticMumford.FunctionField (model K)

abbrev Mumford : Type u :=
  SexticMumford.Mumford (model K)

abbrev SemiMumford : Type u :=
  SexticMumford.SemiMumford (model K)

/-! ## The six rational cusps -/

set_option backward.isDefEq.respectTransparency.types false in
/-- Names for the six rational cusps on the smooth projective curve. -/
inductive Cusp13
  | infinityPlus
  | infinityMinus
  | zeroPlus
  | zeroMinus
  | negOnePlus
  | negOneMinus
  deriving DecidableEq, Fintype

/-- The six cusps as points of the generic two-infinity sextic model. -/
def cuspPoint : Cusp13 → SexticMumford.CurvePoint (model ℚ)
  | .infinityPlus => .infinityPlus
  | .infinityMinus => .infinityMinus
  | .zeroPlus => .affine 0 1 (by norm_num [model, f])
  | .zeroMinus => .affine 0 (-1) (by norm_num [model, f])
  | .negOnePlus => .affine (-1) 1 (by norm_num [model, f])
  | .negOneMinus => .affine (-1) (-1) (by norm_num [model, f])

theorem cuspPoint_injective :
    Function.Injective cuspPoint := by
  intro c d h
  cases c <;> cases d <;> simp_all [cuspPoint] <;> norm_num at *

/-- A scalar point on the sextic gives a point of its projective completion. -/
def affineCurvePoint (X Y : ℚ) (h : N13CurveModel.C13SexticEq X Y) :
    SexticMumford.CurvePoint (model ℚ) :=
  .affine X Y (by
    change Y ^ 2 = (f ℚ).eval X
    rw [f_eval_eq_sexticF13]
    exact h)

/-- Once the affine `x`-coordinate classification is known, the full
projective curve consists exactly of the six named cusps. -/
theorem curvePoint_eq_cusp_of_affine_x
    (hclass : ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1)
    (P : SexticMumford.CurvePoint (model ℚ)) :
    ∃ c : Cusp13, P = cuspPoint c := by
  cases P with
  | infinityPlus =>
      exact ⟨.infinityPlus, rfl⟩
  | infinityMinus =>
      exact ⟨.infinityMinus, rfl⟩
  | affine X Y hcurve =>
      have hcurve' : N13CurveModel.C13SexticEq X Y := by
        rw [N13CurveModel.C13SexticEq, ← f_eval_eq_sexticF13]
        exact hcurve
      rcases hclass X Y hcurve' with rfl | rfl
      · have hYsq : Y ^ 2 = 1 := by
          calc
            Y ^ 2 = (model ℚ).f.eval 0 := hcurve
            _ = 1 := by norm_num [model, f]
        have hprod : (Y - 1) * (Y + 1) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp hprod with hY | hY
        · have : Y = 1 := sub_eq_zero.mp hY
          subst Y
          exact ⟨.zeroPlus, rfl⟩
        · have : Y = -1 := by linarith
          subst Y
          exact ⟨.zeroMinus, rfl⟩
      · have hYsq : Y ^ 2 = 1 := by
          calc
            Y ^ 2 = (model ℚ).f.eval (-1) := hcurve
            _ = 1 := by norm_num [model, f]
        have hprod : (Y - 1) * (Y + 1) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp hprod with hY | hY
        · have : Y = 1 := sub_eq_zero.mp hY
          subst Y
          exact ⟨.negOnePlus, rfl⟩
        · have : Y = -1 := by linarith
          subst Y
          exact ⟨.negOneMinus, rfl⟩

end

end MazurProof.N13Mumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13Infinity
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The positive infinity of the N13 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 6s² + 2s³ + s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `SexticMumford`.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

/-! ## The formal positive square root -/

def reverseF : K⟦X⟧ :=
  1 + 4 * PowerSeries.X + 6 * PowerSeries.X ^ 2 +
    2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 +
    2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6

def reverseTail : K⟦X⟧ := reverseF K - 1

omit [CharZero K] in
@[simp] theorem reverseTail_constantCoeff :
    PowerSeries.constantCoeff (reverseTail K) = 0 := by
  simp [reverseTail, reverseF]

omit [CharZero K] in
theorem reverseTail_hasSubst : PowerSeries.HasSubst (reverseTail K) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (reverseTail_constantCoeff K)

def sqrtReverseF : K⟦X⟧ :=
  PowerSeries.substAlgHom (reverseTail_hasSubst K)
    (PowerSeries.binomialSeries K (1 / 2 : K))

theorem sqrtReverseF_sq : sqrtReverseF K ^ 2 = reverseF K := by
  let h := reverseTail_hasSubst K
  change (PowerSeries.substAlgHom h
      (PowerSeries.binomialSeries K (1 / 2 : K))) ^ 2 = reverseF K
  rw [pow_two, ← map_mul, ← PowerSeries.binomialSeries_add]
  have hhalf : (1 / 2 : K) + 1 / 2 = 1 := by norm_num
  rw [hhalf]
  have hone : PowerSeries.binomialSeries K (1 : K) =
      (1 + PowerSeries.X : K⟦X⟧) := by
    simpa using (PowerSeries.binomialSeries_nat (R := K) (A := K) 1)
  rw [hone]
  simp only [map_add, map_one,
    PowerSeries.substAlgHom_X]
  simp [reverseTail]

@[simp] theorem sqrtReverseF_constantCoeff :
    PowerSeries.constantCoeff (sqrtReverseF K) = 1 := by
  rw [sqrtReverseF]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [PowerSeries.coe_substAlgHom (reverseTail_hasSubst K)]
  rw [PowerSeries.coeff_subst' (reverseTail_hasSubst K)]
  simp only [PowerSeries.binomialSeries_coeff]
  rw [finsum_eq_single _ 0]
  · simp
  · intro b hb
    simp [PowerSeries.coeff_zero_eq_constantCoeff,
      reverseTail_constantCoeff, hb]

/-! ## An algebraic model of the function field -/

def curvePolyRat : (RatFunc K)[X] :=
  (SexticMumford.curvePoly (N13Mumford.model K)).map
    (algebraMap K[X] (RatFunc K))

theorem curvePolyRat_monic : (curvePolyRat K).Monic := by
  exact (SexticMumford.curvePoly_monic (N13Mumford.model K)).map _

theorem curvePolyRat_irreducible : Irreducible (curvePolyRat K) := by
  rw [curvePolyRat]
  exact
    (SexticMumford.curvePoly_monic
      (N13Mumford.model K)).irreducible_iff_irreducible_map_fraction_map
        (R := K[X]) (K := RatFunc K) |>.mp
        (SexticMumford.curvePoly_irreducible (N13Mumford.model K))

instance curvePolyRatIrreducibleFact :
    Fact (Irreducible (curvePolyRat K)) :=
  ⟨curvePolyRat_irreducible K⟩

abbrev AlgebraicFunctionField : Type u := AdjoinRoot (curvePolyRat K)

def coordinateToAlgebraic :
    N13Mumford.CoordinateRing K →+* AlgebraicFunctionField K :=
  AdjoinRoot.map (algebraMap K[X] (RatFunc K))
    (SexticMumford.curvePoly (N13Mumford.model K)) (curvePolyRat K) (by
      rw [curvePolyRat])

@[simp] theorem coordinateToAlgebraic_mk (g : K[X][X]) :
    coordinateToAlgebraic K (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g) =
      AdjoinRoot.mk (curvePolyRat K)
        (g.map (algebraMap K[X] (RatFunc K))) := by
  simp only [coordinateToAlgebraic, AdjoinRoot.map, AdjoinRoot.lift_mk]
  rw [← Polynomial.eval₂_map]
  simpa only [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def] using
    (AdjoinRoot.aeval_eq
      (f := curvePolyRat K)
      (p := g.map (algebraMap K[X] (RatFunc K))))

theorem coordinateToAlgebraic_injective :
    Function.Injective (coordinateToAlgebraic K) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    let r : K[X][X] := g %ₘ SexticMumford.curvePoly (N13Mumford.model K)
    have hrz : AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) r =
        AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g := by
      simpa only [r, AdjoinRoot.modByMonicHom_mk] using
        (AdjoinRoot.mk_leftInverse (SexticMumford.curvePoly_monic (N13Mumford.model K))
          (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g))
    have hmap : AdjoinRoot.mk (curvePolyRat K)
        (r.map (algebraMap K[X] (RatFunc K))) = 0 := by
      rw [← coordinateToAlgebraic_mk, hrz, hz]
    have hrdeg : r.degree < (SexticMumford.curvePoly (N13Mumford.model K)).degree := by
      exact Polynomial.degree_modByMonic_lt g
        (SexticMumford.curvePoly_monic (N13Mumford.model K))
    have hbase : Function.Injective
        (algebraMap K[X] (RatFunc K)) :=
      IsFractionRing.injective K[X] (RatFunc K)
    have hmapdeg :
        (r.map (algebraMap K[X] (RatFunc K))).degree <
          (curvePolyRat K).degree := by
      rw [curvePolyRat, Polynomial.degree_map_eq_of_injective hbase,
        Polynomial.degree_map_eq_of_injective hbase]
      exact hrdeg
    have hrmapzero : r.map (algebraMap K[X] (RatFunc K)) = 0 := by
      by_contra hr0
      exact (curvePolyRat_monic K).not_dvd_of_degree_lt hr0 hmapdeg
        (AdjoinRoot.mk_eq_zero.mp hmap)
    have hrzero : r = 0 :=
      (Polynomial.map_eq_zero_iff hbase).mp hrmapzero
    rw [← hrz, hrzero, map_zero]
    exact Submodule.zero_mem _
  · exact bot_le

/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/

omit [CharZero K] in
theorem ratXInv_transcendental :
    Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
  rw [Transcendental, ← IsAlgebraic.inv_iff]
  simpa [Transcendental] using (RatFunc.transcendental_X (K := K))

def invPolyAlgHom : K[X] →ₐ[K] RatFunc K :=
  Polynomial.aeval ((RatFunc.X : RatFunc K)⁻¹)

omit [CharZero K] in
theorem invPolyAlgHom_injective :
    Function.Injective (invPolyAlgHom K) := by
  exact transcendental_iff_injective.mp (ratXInv_transcendental K)

def ratInvAlgHom : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (invPolyAlgHom K)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (invPolyAlgHom_injective K))

omit [CharZero K] in
omit [CharZero K] in
@[simp] theorem ratInvAlgHom_X :
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
      (RatFunc.X : RatFunc K)⁻¹ := by
  calc
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
        ratInvAlgHom K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = invPolyAlgHom K Polynomial.X := by
      change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
          (algebraMap K[X] (RatFunc K) Polynomial.X) = _
      exact RatFunc.liftRingHom_algebraMap _ _ _
    _ = (RatFunc.X : RatFunc K)⁻¹ := by simp [invPolyAlgHom]

def standardRatToLaurent : RatFunc K →+* LaurentSeries K :=
  IsFractionRing.lift
    (g := algebraMap K[X] (LaurentSeries K))
    (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ)

omit [CharZero K] in
@[simp] theorem standardRatToLaurent_X :
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
      HahnSeries.single 1 1 := by
  calc
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
        standardRatToLaurent K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = algebraMap K[X] (LaurentSeries K) Polynomial.X := by
      exact IsFractionRing.lift_algebraMap
        (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) _
    _ = HahnSeries.single 1 1 := by simp

omit [CharZero K] in
@[simp] theorem standardRatToLaurent_algebraMap (p : K[X]) :
    standardRatToLaurent K (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (LaurentSeries K) p := by
  exact IsFractionRing.lift_algebraMap
    (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) p

omit [CharZero K] in
omit [CharZero K] in
@[simp] theorem ratInvAlgHom_algebraMap (p : K[X]) :
    ratInvAlgHom K (algebraMap K[X] (RatFunc K) p) =
      invPolyAlgHom K p := by
  change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
      (algebraMap K[X] (RatFunc K) p) = _
  exact RatFunc.liftRingHom_algebraMap _ _ _

def ratToLaurent : RatFunc K →+* LaurentSeries K :=
  (standardRatToLaurent K).comp
    (ratInvAlgHom K).toRingHom

def parameter : LaurentSeries K := HahnSeries.single 1 1

@[simp] theorem parameter_ne_zero : parameter K ≠ 0 := by
  simp [parameter]

omit [CharZero K] in
@[simp] theorem ratToLaurent_X :
    ratToLaurent K (RatFunc.X : RatFunc K) = (parameter K)⁻¹ := by
  simp [ratToLaurent, parameter]

omit [CharZero K] in
@[simp] theorem ratToLaurent_C (a : K) :
    ratToLaurent K (RatFunc.C a) =
      algebraMap K (LaurentSeries K) a := by
  rw [← RatFunc.algebraMap_C]
  change standardRatToLaurent K
      (ratInvAlgHom K (algebraMap K[X] (RatFunc K) (C a))) = _
  rw [ratInvAlgHom_algebraMap]
  simp only [invPolyAlgHom, Polynomial.aeval_C]
  change standardRatToLaurent K (RatFunc.C a) = _
  rw [← RatFunc.algebraMap_C]
  rw [standardRatToLaurent_algebraMap]
  rw [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C,
    HahnSeries.ofPowerSeries_C]
  rw [HahnSeries.algebraMap_apply' (Γ := ℤ)]
  simp

omit [CharZero K] in
theorem ratToLaurent_comp_algebraMap :
    (ratToLaurent K).comp (algebraMap K[X] (RatFunc K)) =
      Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

def wSeries : LaurentSeries K := (sqrtReverseF K : LaurentSeries K)

def ySeries : LaurentSeries K :=
  ((parameter K)⁻¹) ^ 3 * wSeries K

omit [CharZero K] in
theorem reverseF_coe :
    ((reverseF K : K⟦X⟧) : LaurentSeries K) =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  simp [reverseF, parameter, PowerSeries.coe_add, PowerSeries.coe_mul,
    PowerSeries.coe_pow, map_ofNat]

theorem wSeries_sq :
    wSeries K ^ 2 =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  rw [wSeries, ← PowerSeries.coe_pow, sqrtReverseF_sq, reverseF_coe]

theorem ySeries_sq :
    ySeries K ^ 2 =
      (N13Mumford.f K).eval₂ (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹) := by
  rw [ySeries]
  simp only [N13Mumford.f, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_mul, eval₂_ofNat, eval₂_one]
  field_simp [parameter_ne_zero K]
  rw [wSeries_sq]
  ring

theorem curvePolyRat_eval_ySeries :
    (curvePolyRat K).eval₂ (ratToLaurent K) (ySeries K) = 0 := by
  rw [curvePolyRat, Polynomial.eval₂_map,
    ratToLaurent_comp_algebraMap]
  change (X ^ 2 - C (N13Mumford.f K)).eval₂
      (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹)) (ySeries K) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [ySeries_sq]
  exact sub_self _

def algebraicToLaurent :
    AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (ratToLaurent K) (ySeries K)
    (curvePolyRat_eval_ySeries K)

theorem algebraicToLaurent_injective :
    Function.Injective (algebraicToLaurent K) :=
  (algebraicToLaurent K).injective

def coordinateToLaurent :
    N13Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurent K).comp (coordinateToAlgebraic K)

theorem coordinateToLaurent_injective :
    Function.Injective (coordinateToLaurent K) :=
  (algebraicToLaurent_injective K).comp
    (coordinateToAlgebraic_injective K)

def functionFieldToLaurent :
    N13Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurent_injective K)

theorem functionFieldToLaurent_injective :
    Function.Injective (functionFieldToLaurent K) :=
  (functionFieldToLaurent K).injective

def laurentOrder : (LaurentSeries K)ˣ →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (z.1.order)
  map_one' := by
    change (1 : LaurentSeries K).order = 0
    simp
  map_mul' x y := by
    change ((x.1 * y.1 : LaurentSeries K).order) =
      x.1.order + y.1.order
    exact HahnSeries.order_mul x.ne_zero y.ne_zero

def infinityOrderHom :
    (N13Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (laurentOrder K).comp (Units.map (functionFieldToLaurent K))

def positiveInfinityOrder : SexticMumford.InfinityOrder (N13Mumford.model K) where
  ordPlus := infinityOrderHom K

end

end MazurProof.N13Infinity


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityAPI
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Evaluation API for the positive infinity embedding of the N13 sextic
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

@[simp] theorem functionFieldToLaurent_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurent K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurent K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurent_injective K) z

theorem coordinateToAlgebraic_xClass (p : K[X]) :
    coordinateToAlgebraic K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      AdjoinRoot.of (curvePolyRat K)
        (algebraMap K[X] (RatFunc K) p) := by
  simpa only [SexticMumford.xClass, SexticMumford.mk, Polynomial.map_C,
    AdjoinRoot.mk_C] using coordinateToAlgebraic_mk K (C p)

@[simp] theorem coordinateToLaurent_xClass (p : K[X]) :
    coordinateToLaurent K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((parameter K)⁻¹) := by
  change algebraicToLaurent K
      (coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [coordinateToAlgebraic_xClass]
  unfold algebraicToLaurent
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeries K)]
  exact DFunLike.congr_fun (ratToLaurent_comp_algebraMap K) p

@[simp] theorem coordinateToLaurent_scalar (c : K) :
    coordinateToLaurent K (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurent K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurent_xClass]
  simp

def coordinateConstUnit (c : Kˣ) : (N13Mumford.CoordinateRing K)ˣ :=
  Units.map (algebraMap K (N13Mumford.CoordinateRing K)) c

def functionConstUnit (c : Kˣ) : (N13Mumford.FunctionField K)ˣ :=
  Units.map
    (algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K))
    (coordinateConstUnit K c)

@[simp] theorem functionFieldToLaurent_functionConstUnit (c : Kˣ) :
    functionFieldToLaurent K (functionConstUnit K c :
      N13Mumford.FunctionField K) =
      algebraMap K (LaurentSeries K) (c : K) := by
  change functionFieldToLaurent K
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (c : K))) = _
  rw [functionFieldToLaurent_algebraMap, coordinateToLaurent_scalar]

@[simp] theorem ordPlus_functionConstUnit (c : Kˣ) :
    (positiveInfinityOrder K).ordPlus (functionConstUnit K c) = 1 := by
  change Multiplicative.ofAdd
      ((functionFieldToLaurent K
        (functionConstUnit K c : N13Mumford.FunctionField K)).order) = 1
  rw [functionFieldToLaurent_functionConstUnit]
  simp [HahnSeries.algebraMap_apply', HahnSeries.order_single c.ne_zero]

@[simp] theorem principalIdeal_functionConstUnit (c : Kˣ) :
    toPrincipalIdeal (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K) (functionConstUnit K c) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton
      (N13Mumford.CoordinateRing K)⁰
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (coordinateConstUnit K c : N13Mumford.CoordinateRing K)) = 1
  rw [← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨(coordinateConstUnit K c)⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← map_mul]
  change algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K)
      (((coordinateConstUnit K c)⁻¹ :
          (N13Mumford.CoordinateRing K)ˣ) * coordinateConstUnit K c :
        (N13Mumford.CoordinateRing K)ˣ) = 1
  simp

end

end MazurProof.N13Infinity


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityMinus
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The negative infinity of the N13 genus-two curve

The second branch at infinity is obtained by sending `Y` to the negative of
the positive Laurent expansion.  It gives the opposite orientation datum for
the two-infinity sextic model.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def ySeriesMinus : LaurentSeries K := -(N13Infinity.ySeries K)

@[simp] theorem ySeriesMinus_eq_neg :
    ySeriesMinus K = -(N13Infinity.ySeries K) := rfl

theorem ySeriesMinus_sq :
    ySeriesMinus K ^ 2 =
      (N13Mumford.f K).eval₂ (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹) := by
  rw [ySeriesMinus, neg_sq, N13Infinity.ySeries_sq]

theorem curvePolyRat_eval_ySeriesMinus :
    (N13Infinity.curvePolyRat K).eval₂ (N13Infinity.ratToLaurent K)
      (ySeriesMinus K) = 0 := by
  rw [N13Infinity.curvePolyRat, Polynomial.eval₂_map,
    N13Infinity.ratToLaurent_comp_algebraMap]
  change (X ^ 2 - C (N13Mumford.f K)).eval₂
      (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹)) (ySeriesMinus K) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [ySeriesMinus_sq]
  exact sub_self _

def algebraicToLaurentMinus :
    N13Infinity.AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (N13Infinity.ratToLaurent K) (ySeriesMinus K)
    (curvePolyRat_eval_ySeriesMinus K)

@[simp] theorem algebraicToLaurentMinus_root :
    algebraicToLaurentMinus K
      (AdjoinRoot.root (N13Infinity.curvePolyRat K)) = ySeriesMinus K := by
  exact AdjoinRoot.lift_root (curvePolyRat_eval_ySeriesMinus K)

theorem algebraicToLaurentMinus_injective :
    Function.Injective (algebraicToLaurentMinus K) :=
  (algebraicToLaurentMinus K).injective

def coordinateToLaurentMinus :
    N13Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurentMinus K).comp (N13Infinity.coordinateToAlgebraic K)

theorem coordinateToLaurentMinus_injective :
    Function.Injective (coordinateToLaurentMinus K) :=
  (algebraicToLaurentMinus_injective K).comp
    (N13Infinity.coordinateToAlgebraic_injective K)

@[simp] theorem coordinateToLaurentMinus_yClass :
    coordinateToLaurentMinus K
      (SexticMumford.yClass (N13Mumford.model K)) = ySeriesMinus K := by
  change algebraicToLaurentMinus K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact algebraicToLaurentMinus_root K

def functionFieldToLaurentMinus :
    N13Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurentMinus_injective K)

theorem functionFieldToLaurentMinus_injective :
    Function.Injective (functionFieldToLaurentMinus K) :=
  (functionFieldToLaurentMinus K).injective

def infinityOrderHomMinus :
    (N13Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (N13Infinity.laurentOrder K).comp
    (Units.map (functionFieldToLaurentMinus K))

def negativeInfinityOrder :
    SexticMumford.InfinityOrder (N13Mumford.model K) where
  ordPlus := infinityOrderHomMinus K

end

end MazurProof.N13InfinityMinus


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityMinusAPI
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Evaluation API for the negative infinity embedding of the N13 sextic
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

@[simp] theorem functionFieldToLaurentMinus_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurentMinus K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurentMinus K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurentMinus_injective K) z

@[simp] theorem coordinateToLaurentMinus_xClass (p : K[X]) :
    coordinateToLaurentMinus K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((N13Infinity.parameter K)⁻¹) := by
  change algebraicToLaurentMinus K
      (N13Infinity.coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [N13Infinity.coordinateToAlgebraic_xClass]
  unfold algebraicToLaurentMinus
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeriesMinus K)]
  exact DFunLike.congr_fun (N13Infinity.ratToLaurent_comp_algebraMap K) p

@[simp] theorem coordinateToLaurentMinus_scalar (c : K) :
    coordinateToLaurentMinus K
      (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurentMinus K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurentMinus_xClass]
  simp

def coordinateConstUnitMinus (c : Kˣ) : (N13Mumford.CoordinateRing K)ˣ :=
  Units.map (algebraMap K (N13Mumford.CoordinateRing K)) c

def functionConstUnitMinus (c : Kˣ) : (N13Mumford.FunctionField K)ˣ :=
  Units.map
    (algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K))
    (coordinateConstUnitMinus K c)

@[simp] theorem functionFieldToLaurentMinus_functionConstUnit (c : Kˣ) :
    functionFieldToLaurentMinus K (functionConstUnitMinus K c :
      N13Mumford.FunctionField K) =
      algebraMap K (LaurentSeries K) (c : K) := by
  change functionFieldToLaurentMinus K
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (c : K))) = _
  rw [functionFieldToLaurentMinus_algebraMap, coordinateToLaurentMinus_scalar]

@[simp] theorem ordPlus_functionConstUnitMinus (c : Kˣ) :
    (negativeInfinityOrder K).ordPlus (functionConstUnitMinus K c) = 1 := by
  change Multiplicative.ofAdd
      ((functionFieldToLaurentMinus K
        (functionConstUnitMinus K c : N13Mumford.FunctionField K)).order) = 1
  rw [functionFieldToLaurentMinus_functionConstUnit]
  simp [HahnSeries.algebraMap_apply', HahnSeries.order_single c.ne_zero]

@[simp] theorem principalIdeal_functionConstUnitMinus (c : Kˣ) :
    toPrincipalIdeal (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K) (functionConstUnitMinus K c) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton
      (N13Mumford.CoordinateRing K)⁰
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (coordinateConstUnitMinus K c : N13Mumford.CoordinateRing K)) = 1
  rw [← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨(coordinateConstUnitMinus K c)⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← map_mul]
  change algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K)
      (((coordinateConstUnitMinus K c)⁻¹ :
          (N13Mumford.CoordinateRing K)ˣ) * coordinateConstUnitMinus K c :
        (N13Mumford.CoordinateRing K)ˣ) = 1
  simp

theorem ySeriesMinus_order :
    (ySeriesMinus K).order = (N13Infinity.ySeries K).order := by
  rw [ySeriesMinus_eq_neg, HahnSeries.order_neg]

end

end MazurProof.N13InfinityMinus

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

private theorem wSeries_coeff_zero :
    (wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, sqrtReverseF_constantCoeff]

private theorem wSeries_ne_zero : wSeries K ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun z : LaurentSeries K => z.coeff (0 : ℤ)) h
  simp [wSeries_coeff_zero] at hcoeff

/-- The square-root factor in the Laurent expansion is a unit at infinity. -/
theorem wSeries_order : (wSeries K).order = 0 := by
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by simp [wSeries_coeff_zero])
  · rw [HahnSeries.le_order_iff_forall (wSeries_ne_zero K)]
    intro j hj
    change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff j = 0
    rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image]
    rintro n ⟨_, hn⟩
    have hnon : (0 : ℤ) ≤ (Nat.castOrderEmbedding n : ℤ) := by
      change (0 : ℤ) ≤ (n : ℤ)
      omega
    rw [hn] at hnon
    omega

/-- Both branches have a pole of order three at their respective infinities. -/
theorem ySeries_order : (ySeries K).order = -3 := by
  rw [ySeries]
  have hp : (parameter K)⁻¹ ^ 3 = HahnSeries.single (-3 : ℤ) 1 := by
    simp [parameter, HahnSeries.inv_single, HahnSeries.single_pow]
  rw [hp, HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero)
    (wSeries_ne_zero K), HahnSeries.order_single one_ne_zero, wSeries_order]
  norm_num

end

end MazurProof.N13Infinity

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem ySeriesMinus_order_eq_neg_three : (ySeriesMinus K).order = -3 := by
  rw [ySeriesMinus_order, N13Infinity.ySeries_order]

end

end MazurProof.N13InfinityMinus


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The order at infinity of a polynomial

The substitution `X = s⁻¹` reverses a polynomial.  Its leading
coefficient becomes the constant coefficient of the reversed polynomial,
so the latter has order zero; the factor `s⁻ⁿ` accounts for the whole
order.  This is the formal local calculation used at the cusps of `X₁(13)`.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof
namespace N13LaurentPolynomialOrder

noncomputable section

universe u

variable (K : Type u) [Field K]

/-- The Laurent parameter at infinity. -/
def parameter : LaurentSeries K := HahnSeries.single 1 1

/-- Evaluation of a polynomial after the substitution `X = s⁻¹`. -/
def evalAtInfinity (p : K[X]) : LaurentSeries K :=
  p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K)⁻¹

@[simp] lemma parameter_ne_zero : parameter K ≠ 0 := by
  simp [parameter]

@[simp] lemma parameter_inv : (parameter K)⁻¹ = HahnSeries.single (-1 : ℤ) 1 := by
  simp [parameter, HahnSeries.inv_single]

@[simp] lemma order_parameter : (parameter K).order = 1 := by
  simp [parameter, HahnSeries.order_single]

@[simp] lemma order_parameter_inv_pow (n : ℕ) :
    ((parameter K)⁻¹ ^ n).order = -(n : ℤ) := by
  rw [parameter_inv, HahnSeries.order_pow]
  simp [HahnSeries.order_single]

lemma eval_parameter_eq_ofPowerSeries (p : K[X]) :
    p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) =
      HahnSeries.ofPowerSeries ℤ K p := by
  have h : Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K) =
      algebraMap K[X] (LaurentSeries K) := by
    apply Polynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) (C a) = _
      rw [Polynomial.eval₂_C, Polynomial.algebraMap_hahnSeries_apply]
      simp [HahnSeries.algebraMap_apply']
    · change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) X = _
      rw [Polynomial.eval₂_X, Polynomial.algebraMap_hahnSeries_apply]
      simp [parameter, HahnSeries.ofPowerSeries_X]
  change (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K)) p = _
  rw [h, Polynomial.algebraMap_hahnSeries_apply]

lemma order_ofPowerSeries_of_coeff_zero_ne (p : K[X]) (hp : p.coeff 0 ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ K p).order = 0 := by
  have hcoeff : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 ≠ 0 := by
    have hcoeff_eq : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = p.coeff 0 := by
      calc
        (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = PowerSeries.coeff 0 (p : K⟦X⟧) :=
          HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (p : K⟦X⟧) 0
        _ = p.coeff 0 := Polynomial.coeff_coe p 0
    rwa [hcoeff_eq]
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero hcoeff
  · rw [← HahnSeries.zero_le_orderTop_iff]
    apply HahnSeries.le_orderTop_iff_forall.mpr
    intro j hj
    rw [HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨n, -, rfl⟩
    have hnonneg : (0 : ℤ) ≤ (Nat.castOrderEmbedding (α := ℤ) n : ℤ) := by
      simp
    exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hnonneg)) hj

lemma order_eval_parameter_reverse (p : K[X]) (hp : p ≠ 0) :
    (p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K)).order = 0 := by
  rw [eval_parameter_eq_ofPowerSeries]
  apply order_ofPowerSeries_of_coeff_zero_ne
  simpa using p.leadingCoeff_ne_zero.mpr hp

lemma evalAtInfinity_eq_reverse_mul (p : K[X]) :
    evalAtInfinity K p =
      p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) *
        (parameter K)⁻¹ ^ p.natDegree := by
  letI : Invertible ((parameter K)⁻¹) :=
    invertibleOfNonzero (inv_ne_zero (parameter_ne_zero K))
  symm
  unfold evalAtInfinity parameter
  simpa [Polynomial.reverse, HahnSeries.inv_single, invOf_eq_inv] using
    (Polynomial.eval₂_reflect_mul_pow (algebraMap K (LaurentSeries K))
      ((parameter K)⁻¹) p.natDegree p le_rfl)

theorem order_evalAtInfinity (p : K[X]) (hp : p ≠ 0) :
    (evalAtInfinity K p).order = -(p.natDegree : ℤ) := by
  rw [evalAtInfinity_eq_reverse_mul, HahnSeries.order_mul]
  · rw [order_eval_parameter_reverse K p hp, order_parameter_inv_pow]
    simp
  · rw [eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _ (inv_ne_zero (parameter_ne_zero K))

end
end N13LaurentPolynomialOrder
end MazurProof


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13BranchNorm
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13BranchNorm

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def evalPoly : K[X] →+* LaurentSeries K :=
  Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
    ((N13Infinity.parameter K)⁻¹)

omit [CharZero K] in
@[simp] theorem evalPoly_apply (p : K[X]) :
    evalPoly K p =
      p.eval₂ (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹) := rfl

omit [CharZero K] in
theorem evalPoly_eq_evalAtInfinity (p : K[X]) :
    evalPoly K p =
      N13LaurentPolynomialOrder.evalAtInfinity K p := by
  rfl

omit [CharZero K] in
theorem evalPoly_ne_zero {p : K[X]} (hp : p ≠ 0) :
    evalPoly K p ≠ 0 := by
  rw [evalPoly_eq_evalAtInfinity,
    N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul]
  apply mul_ne_zero
  · rw [N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _
      (inv_ne_zero (N13LaurentPolynomialOrder.parameter_ne_zero K))

omit [CharZero K] in
theorem evalPoly_order (p : K[X]) (hp : p ≠ 0) :
    (evalPoly K p).order = -(p.natDegree : ℤ) := by
  rw [evalPoly_eq_evalAtInfinity]
  exact N13LaurentPolynomialOrder.order_evalAtInfinity K p hp

@[simp] theorem coordinateToLaurent_yClass :
    N13Infinity.coordinateToLaurent K
      (SexticMumford.yClass (N13Mumford.model K)) =
      N13Infinity.ySeries K := by
  change N13Infinity.algebraicToLaurent K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk
        (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact AdjoinRoot.lift_root
    (N13Infinity.curvePolyRat_eval_ySeries K)

def linearFunction (p q : K[X]) : N13Mumford.CoordinateRing K :=
  SexticMumford.xClass (N13Mumford.model K) p +
    SexticMumford.xClass (N13Mumford.model K) q *
      SexticMumford.yClass (N13Mumford.model K)

@[simp] theorem coordinateToLaurent_linearFunction (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) =
      evalPoly K p + evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, coordinateToLaurent_yClass]

@[simp] theorem coordinateToLaurentMinus_linearFunction (p q : K[X]) :
    N13InfinityMinus.coordinateToLaurentMinus K (linearFunction K p q) =
      evalPoly K p - evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, N13InfinityMinus.ySeriesMinus_eq_neg]
  ring

def normNumerator (p q : K[X]) : K[X] :=
  p ^ 2 - q ^ 2 * N13Mumford.f K

theorem branch_product (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) *
        N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) =
      evalPoly K (normNumerator K p q) := by
  rw [coordinateToLaurent_linearFunction,
    coordinateToLaurentMinus_linearFunction]
  calc
    (evalPoly K p + evalPoly K q * N13Infinity.ySeries K) *
          (evalPoly K p - evalPoly K q * N13Infinity.ySeries K) =
        evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * N13Infinity.ySeries K ^ 2 := by ring
    _ = evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * evalPoly K (N13Mumford.f K) := by
            have hy :
                N13Infinity.ySeries K ^ 2 =
                  evalPoly K (N13Mumford.f K) := by
              simpa only [evalPoly_apply] using
                N13Infinity.ySeries_sq K
            rw [hy]
    _ = evalPoly K (normNumerator K p q) := by
      simp only [normNumerator, map_sub, map_mul, map_pow]

theorem branch_orders_add (p q : K[X])
    (hnorm : normNumerator K p q ≠ 0) :
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
        (N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q)).order =
      -((normNumerator K p q).natDegree : ℤ) := by
  have hproduct :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q) ≠ 0 := by
    rw [branch_product]
    exact evalPoly_ne_zero K hnorm
  have hplus :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) ≠ 0 :=
    left_ne_zero_of_mul hproduct
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) ≠ 0 :=
    right_ne_zero_of_mul hproduct
  calc
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
          (N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order =
        (N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order :=
      (HahnSeries.order_mul hplus hminus).symm
    _ = (evalPoly K (normNumerator K p q)).order := by
      rw [branch_product]
    _ = -((normNumerator K p q).natDegree : ℤ) :=
      evalPoly_order K _ hnorm

theorem normNumerator_eq_coeff_norm
    (z : N13Mumford.CoordinateRing K) :
    normNumerator K
        (SexticMumford.coeff0 (N13Mumford.model K) z)
        (SexticMumford.coeffY (N13Mumford.model K) z) =
      SexticMumford.coeff0 (N13Mumford.model K)
        (SexticMumford.norm (N13Mumford.model K) z) := by
  let p := SexticMumford.coeff0 (N13Mumford.model K) z
  let q := SexticMumford.coeffY (N13Mumford.model K) z
  symm
  calc
    SexticMumford.coeff0 (N13Mumford.model K)
          (SexticMumford.norm (N13Mumford.model K) z) =
        SexticMumford.coeff0 (N13Mumford.model K)
          (SexticMumford.norm (N13Mumford.model K)
            (SexticMumford.xClass (N13Mumford.model K) p +
              SexticMumford.xClass (N13Mumford.model K) q *
                SexticMumford.yClass (N13Mumford.model K))) := by
                  simpa [p, q] using congrArg
                    (fun w => SexticMumford.coeff0
                      (N13Mumford.model K)
                      (SexticMumford.norm (N13Mumford.model K) w))
                    (SexticMumford.recompose
                      (N13Mumford.model K) z).symm
    _ = normNumerator K p q := by
      rw [SexticMumford.norm_recompose,
        SexticMumford.coeff0_xClass]
      rfl

end

end MazurProof.N13BranchNorm


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13BranchLeading
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Leading pole degree across the two infinity branches

For `p(X) + q(X)Y`, cancellation can raise the order at one infinity, but
it cannot raise the order at both.  The minimum of the two branch orders is
the negative of

`max (deg p) (deg q + 3)`.

The proof is valuation-theoretic.  For arbitrary Laurent series `a,b`, the
pair `a+b, a-b` remembers the smaller of the orders of `a,b`, because `2` is
invertible.  This avoids any coefficient enumeration.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13BranchLeading

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem min_orderTop_add_sub (a b : LaurentSeries K) :
    min (a + b).orderTop (a - b).orderTop =
      min a.orderTop b.orderTop := by
  apply le_antisymm
  · apply le_min
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) + (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_add
        _ = (2 * a).orderTop := by ring_nf
        _ = a.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) - (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_sub
        _ = (2 * b).orderTop := by ring_nf
        _ = b.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
  · apply le_min
    · exact HahnSeries.min_orderTop_le_orderTop_add
    · exact HahnSeries.min_orderTop_le_orderTop_sub

theorem min_order_add_sub_of_ne
    (a b : LaurentSeries K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hplus : a + b ≠ 0) (hminus : a - b ≠ 0) :
    min (a + b).order (a - b).order = min a.order b.order := by
  have htop := min_orderTop_add_sub K a b
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ha,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hb,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hplus,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hminus] at htop
  exact WithTop.coe_injective (by
    simpa only [WithTop.coe_min] using htop)

def poleDegree (p q : K[X]) : ℕ :=
  by
    classical
    exact max p.natDegree (if q = 0 then 0 else q.natDegree + 3)

private theorem ySeries_ne_zero : N13Infinity.ySeries K ≠ 0 := by
  intro hzero
  have horder := N13Infinity.ySeries_order K
  rw [hzero, HahnSeries.order_zero] at horder
  norm_num at horder

theorem evalPoly_mul_ySeries_order (q : K[X]) (hq : q ≠ 0) :
    (N13BranchNorm.evalPoly K q * N13Infinity.ySeries K).order =
      -((q.natDegree + 3 : ℕ) : ℤ) := by
  rw [HahnSeries.order_mul
    (N13BranchNorm.evalPoly_ne_zero K hq)
    (ySeries_ne_zero K),
    N13BranchNorm.evalPoly_order K q hq,
    N13Infinity.ySeries_order]
  omega

theorem branch_min_order (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0) :
    min
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order
        (N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q)).order =
      -(poleDegree K p q : ℤ) := by
  have hplus :
      N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13Infinity.coordinateToLaurent_injective K
    simpa using hzero
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13InfinityMinus.coordinateToLaurentMinus_injective K
    simpa using hzero
  have hplus' :
      N13BranchNorm.evalPoly K p +
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurent_linearFunction] using
      hplus
  have hminus' :
      N13BranchNorm.evalPoly K p -
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurentMinus_linearFunction] using
      hminus
  rw [N13BranchNorm.coordinateToLaurent_linearFunction,
    N13BranchNorm.coordinateToLaurentMinus_linearFunction]
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      intro hq
      apply hz
      simp [N13BranchNorm.linearFunction, hp, hq]
    simp only [hp, map_zero, zero_add, zero_sub, HahnSeries.order_neg,
      min_self]
    rw [evalPoly_mul_ySeries_order K q hq]
    simp [poleDegree, hq]
  · by_cases hq : q = 0
    · simp only [hq, map_zero, zero_mul, add_zero, sub_zero, min_self]
      rw [N13BranchNorm.evalPoly_order K p hp]
      simp [poleDegree]
    · have ha := N13BranchNorm.evalPoly_ne_zero K hp
      have hb : N13BranchNorm.evalPoly K q *
          N13Infinity.ySeries K ≠ 0 :=
        mul_ne_zero (N13BranchNorm.evalPoly_ne_zero K hq)
          (ySeries_ne_zero K)
      rw [min_order_add_sub_of_ne K _ _ ha hb hplus' hminus',
        N13BranchNorm.evalPoly_order K p hp,
        evalPoly_mul_ySeries_order K q hq]
      simp only [poleDegree, hq, if_false]
      omega

/-- A regular function with at most a simple pole at each infinity has no
`Y`-part and is at most linear in `X`.  This is the genus-two replacement
for a coefficient search. -/
theorem eq_zero_and_natDegree_le_one_of_branch_orders
    (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0)
    (hplus : (-1 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K
        (N13BranchNorm.linearFunction K p q)).order)
    (hminus : (-1 : ℤ) ≤
      (N13InfinityMinus.coordinateToLaurentMinus K
        (N13BranchNorm.linearFunction K p q)).order) :
    q = 0 ∧ p.natDegree ≤ 1 := by
  have hmin : (-1 : ℤ) ≤
      min
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order
        (N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q)).order :=
    le_min hplus hminus
  rw [branch_min_order K p q hz] at hmin
  have hdegree : poleDegree K p q ≤ 1 := by
    omega
  have hq : q = 0 := by
    by_contra hq
    simp only [poleDegree, hq, if_false] at hdegree
    omega
  refine ⟨hq, ?_⟩
  simpa only [poleDegree, hq, if_pos, Nat.max_zero] using hdegree

end

end MazurProof.N13BranchLeading


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordInfinityBalance
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Structural infinity balancing for the true `X₁(13)` sextic

The polynomial used here is exactly

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Its positive-infinity cubic part is

`s = X³ + 2X² + X - 1`,

with the exact low-degree identity `f - s² = 4X(X+1)`.  This file builds
the two adapted Cantor lifts needed to balance the integer at infinity.
There is no divisor enumeration or Riemann--Roch input.
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13MumfordInfinityBalance

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

open MazurProof
open MazurProof.SexticMumford

abbrev M : SexticMumford.Model K := N13Mumford.model K

/-- Polynomial part of the positive branch `Y` at infinity. -/
def sqrtInfinity : K[X] :=
  X ^ 3 + 2 * X ^ 2 + X - 1

theorem sqrtInfinity_isMonicOfDegree :
    IsMonicOfDegree (sqrtInfinity : K[X]) 3 := by
  constructor
  · unfold sqrtInfinity
    compute_degree!
  · unfold sqrtInfinity
    monicity!

@[simp] theorem sqrtInfinity_natDegree :
    (sqrtInfinity : K[X]).natDegree = 3 :=
  sqrtInfinity_isMonicOfDegree.natDegree_eq

omit [CharZero K] in
theorem f_sub_sqrtInfinity_sq :
    N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2 =
      4 * X * (X + 1) := by
  simp only [N13Mumford.f, sqrtInfinity]
  ring

omit [CharZero K] in
theorem f_sub_sqrtInfinity_sq_natDegree_le :
    (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤ 2 := by
  rw [f_sub_sqrtInfinity_sq]
  compute_degree!

variable (D : N13Mumford.SemiMumford K)

/-! ## The two adapted lifts -/

def plusRemainder : K[X] :=
  (sqrtInfinity - D.v) % D.u

/-- Congruent to `v` and monic cubic; adapted to the positive branch. -/
def plusLift : K[X] :=
  sqrtInfinity - plusRemainder D

def minusRemainder : K[X] :=
  (-sqrtInfinity - D.v) % D.u

/-- Congruent to `v`, with `-minusLift` monic cubic. -/
def minusLift : K[X] :=
  -sqrtInfinity - minusRemainder D

omit [CharZero K] in
private theorem sub_mod_dvd
    (p u : K[X]) :
    u ∣ p - p % u := by
  refine ⟨p / u, ?_⟩
  have hdiv := EuclideanDomain.mod_add_div p u
  calc
    p - p % u =
        (p % u + u * (p / u)) - p % u := by rw [hdiv]
    _ = u * (p / u) := by ring

theorem plusLift_congr :
    D.u ∣ plusLift D - D.v := by
  unfold plusLift plusRemainder
  convert sub_mod_dvd (sqrtInfinity - D.v) D.u using 1
  all_goals ring

theorem minusLift_congr :
    D.u ∣ minusLift D - D.v := by
  unfold minusLift minusRemainder
  convert sub_mod_dvd (-sqrtInfinity - D.v) D.u using 1
  all_goals ring

private theorem curve_dvd_of_congr
    (V : K[X]) (hV : D.u ∣ V - D.v) :
    D.u ∣ N13Mumford.f K - V ^ 2 := by
  obtain ⟨a, ha⟩ := D.curve_dvd
  change N13Mumford.f K - D.v ^ 2 = D.u * a at ha
  obtain ⟨b, hb⟩ := hV
  refine ⟨a - b * (V + D.v), ?_⟩
  calc
    N13Mumford.f K - V ^ 2 =
        (N13Mumford.f K - D.v ^ 2) -
          (V - D.v) * (V + D.v) := by ring
    _ = D.u * a - (D.u * b) * (V + D.v) := by
          rw [ha, hb]
    _ = D.u * (a - b * (V + D.v)) := by ring

theorem plusLift_curve_dvd :
    D.u ∣ N13Mumford.f K - (plusLift D) ^ 2 :=
  curve_dvd_of_congr D (plusLift D) (plusLift_congr D)

theorem minusLift_curve_dvd :
    D.u ∣ N13Mumford.f K - (minusLift D) ^ 2 :=
  curve_dvd_of_congr D (minusLift D) (minusLift_congr D)

def plusFactor : K[X] :=
  Classical.choose (plusLift_curve_dvd D)

theorem plusFactor_spec :
    N13Mumford.f K - (plusLift D) ^ 2 =
      D.u * plusFactor D :=
  Classical.choose_spec (plusLift_curve_dvd D)

def minusFactor : K[X] :=
  Classical.choose (minusLift_curve_dvd D)

theorem minusFactor_spec :
    N13Mumford.f K - (minusLift D) ^ 2 =
      D.u * minusFactor D :=
  Classical.choose_spec (minusLift_curve_dvd D)

theorem plusFactor_ne_zero :
    plusFactor D ≠ 0 :=
  cantorFactor_ne_zero (N13Mumford.model K)
    D.u (plusLift D) (plusFactor D) (plusFactor_spec D)

theorem minusFactor_ne_zero :
    minusFactor D ≠ 0 :=
  cantorFactor_ne_zero (N13Mumford.model K)
    D.u (minusLift D) (minusFactor D) (minusFactor_spec D)

/-! ## Degree bounds -/

private theorem mod_natDegree_lt
    (p : K[X]) (hpos : 0 < D.u.natDegree) :
    (p % D.u).natDegree < D.u.natDegree := by
  by_cases hr : p % D.u = 0
  · rw [hr]
    simp
    exact hpos
  · exact natDegree_lt_natDegree hr
      (degree_mod_lt p D.u_monic.ne_zero)

private theorem mod_eq_zero_of_natDegree_eq_zero
    (p : K[X]) (hzero : D.u.natDegree = 0) :
    p % D.u = 0 := by
  have hu : D.u = 1 :=
    eq_one_of_monic_natDegree_zero D.u_monic hzero
  rw [hu]
  simp

theorem plusRemainder_natDegree_lt
    (hpos : 0 < D.u.natDegree) :
    (plusRemainder D).natDegree < D.u.natDegree :=
  mod_natDegree_lt D (sqrtInfinity - D.v) hpos

theorem minusRemainder_natDegree_lt
    (hpos : 0 < D.u.natDegree) :
    (minusRemainder D).natDegree < D.u.natDegree :=
  mod_natDegree_lt D (-sqrtInfinity - D.v) hpos

theorem plusRemainder_eq_zero
    (hzero : D.u.natDegree = 0) :
    plusRemainder D = 0 :=
  mod_eq_zero_of_natDegree_eq_zero D _ hzero

theorem minusRemainder_eq_zero
    (hzero : D.u.natDegree = 0) :
    minusRemainder D = 0 :=
  mod_eq_zero_of_natDegree_eq_zero D _ hzero

theorem plusRemainder_natDegree_le_one
    (hdeg : D.u.natDegree ≤ 2) :
    (plusRemainder D).natDegree ≤ 1 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [plusRemainder_eq_zero D hzero]
    simp
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    have hlt := plusRemainder_natDegree_lt D hpos
    omega

theorem minusRemainder_natDegree_le_one
    (hdeg : D.u.natDegree ≤ 2) :
    (minusRemainder D).natDegree ≤ 1 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [minusRemainder_eq_zero D hzero]
    simp
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    have hlt := minusRemainder_natDegree_lt D hpos
    omega

theorem plusLift_isMonicOfDegree
    (hdeg : D.u.natDegree ≤ 2) :
    IsMonicOfDegree (plusLift D) 3 := by
  unfold plusLift
  exact sqrtInfinity_isMonicOfDegree.sub
    (by have := plusRemainder_natDegree_le_one D hdeg; omega)

theorem neg_minusLift_isMonicOfDegree
    (hdeg : D.u.natDegree ≤ 2) :
    IsMonicOfDegree (-minusLift D) 3 := by
  have hmonic :
      IsMonicOfDegree
        (sqrtInfinity + minusRemainder D : K[X]) 3 :=
    sqrtInfinity_isMonicOfDegree.add_right
      (by have := minusRemainder_natDegree_le_one D hdeg; omega)
  convert hmonic using 1
  unfold minusLift
  ring

private theorem two_mul_sqrt_mul_natDegree_le
    (r : K[X]) {d : ℕ} (hr : r.natDegree < d) :
    (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 := by
  calc
    (2 * (sqrtInfinity : K[X]) * r).natDegree ≤
        (2 * (sqrtInfinity : K[X])).natDegree + r.natDegree :=
      natDegree_mul_le
    _ ≤ ((2 : K[X]).natDegree +
          (sqrtInfinity : K[X]).natDegree) + r.natDegree := by
      gcongr
      exact natDegree_mul_le
    _ = 3 + r.natDegree := by simp
    _ ≤ d + 2 := by omega

omit [CharZero K] in
private theorem remainder_sq_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2) (hr : r.natDegree < d) :
    (r ^ 2).natDegree ≤ d + 2 := by
  rw [natDegree_pow]
  omega

private theorem adaptedNumerator_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2)
    (hr : r.natDegree < d) :
    ((N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) +
        2 * sqrtInfinity * r - r ^ 2).natDegree ≤ d + 2 := by
  have hbase :
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤
        d + 2 :=
    (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans (by omega)
  have hmiddle :
      (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 :=
    two_mul_sqrt_mul_natDegree_le r hr
  have hsquare : (r ^ 2).natDegree ≤ d + 2 :=
    remainder_sq_natDegree_le r hd hr
  exact
    (natDegree_sub_le _ _).trans <|
      (Nat.max_le.mpr
        ⟨(natDegree_add_le _ _).trans
            (Nat.max_le.mpr ⟨hbase, hmiddle⟩),
          hsquare⟩)

private theorem adaptedNumeratorNeg_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2)
    (hr : r.natDegree < d) :
    ((N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) -
        2 * sqrtInfinity * r - r ^ 2).natDegree ≤ d + 2 := by
  have hbase :
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤
        d + 2 :=
    (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans (by omega)
  have hmiddle :
      (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 :=
    two_mul_sqrt_mul_natDegree_le r hr
  have hsquare : (r ^ 2).natDegree ≤ d + 2 :=
    remainder_sq_natDegree_le r hd hr
  exact
    (natDegree_sub_le _ _).trans <|
      (Nat.max_le.mpr
        ⟨(natDegree_sub_le _ _).trans
            (Nat.max_le.mpr ⟨hbase, hmiddle⟩),
          hsquare⟩)

theorem plusNumerator_natDegree_le
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Mumford.f K - (plusLift D) ^ 2).natDegree ≤
      D.u.natDegree + 2 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [plusLift, plusRemainder_eq_zero D hzero]
    simp only [sub_zero]
    exact (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans
      (by omega)
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    rw [show N13Mumford.f K - (plusLift D) ^ 2 =
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) +
        2 * sqrtInfinity * plusRemainder D -
          (plusRemainder D) ^ 2 by
      unfold plusLift
      ring]
    exact adaptedNumerator_natDegree_le
      (plusRemainder D) hdeg (plusRemainder_natDegree_lt D hpos)

theorem minusNumerator_natDegree_le
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Mumford.f K - (minusLift D) ^ 2).natDegree ≤
      D.u.natDegree + 2 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [minusLift, minusRemainder_eq_zero D hzero]
    simp only [sub_zero, neg_sq]
    exact (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans
      (by omega)
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    rw [show N13Mumford.f K - (minusLift D) ^ 2 =
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) -
        2 * sqrtInfinity * minusRemainder D -
          (minusRemainder D) ^ 2 by
      unfold minusLift
      ring]
    exact adaptedNumeratorNeg_natDegree_le
      (minusRemainder D) hdeg (minusRemainder_natDegree_lt D hpos)

theorem plusFactor_natDegree_le_two
    (hdeg : D.u.natDegree ≤ 2) :
    (plusFactor D).natDegree ≤ 2 := by
  have hsum :
      D.u.natDegree + (plusFactor D).natDegree =
        (N13Mumford.f K - (plusLift D) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero
      (plusFactor_ne_zero D), ← plusFactor_spec D]
  have hnum := plusNumerator_natDegree_le D hdeg
  omega

theorem minusFactor_natDegree_le_two
    (hdeg : D.u.natDegree ≤ 2) :
    (minusFactor D).natDegree ≤ 2 := by
  have hsum :
      D.u.natDegree + (minusFactor D).natDegree =
        (N13Mumford.f K - (minusLift D) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero
      (minusFactor_ne_zero D), ← minusFactor_spec D]
  have hnum := minusNumerator_natDegree_le D hdeg
  omega

/-! ## Leading terms at the two infinities -/

omit [CharZero K] in
private theorem evalPoly_coeff_neg_three_eq_zero
    (p : K[X]) (hdeg : p.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K p).coeff (-3 : ℤ) = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · by_contra hcoeff
    have horder :
        (N13BranchNorm.evalPoly K p).order ≤ (-3 : ℤ) :=
      HahnSeries.order_le_of_coeff_ne_zero hcoeff
    rw [N13BranchNorm.evalPoly_order K p hp] at horder
    omega

omit [CharZero K] in
private theorem evalSqrtInfinity_coeff_neg_three :
    (N13BranchNorm.evalPoly K (sqrtInfinity : K[X])).coeff
        (-3 : ℤ) = 1 := by
  simp [N13BranchNorm.evalPoly, sqrtInfinity,
    N13Infinity.parameter]
  change ((2 : LaurentSeries K) *
    HahnSeries.single (-2 : ℤ) 1).coeff (-3 : ℤ) = 0
  rw [show (2 : LaurentSeries K) =
    HahnSeries.single (0 : ℤ) 2 by rfl]
  rw [HahnSeries.coeff_single_mul]
  norm_num [HahnSeries.coeff_single]

private theorem wSeries_coeff_zero :
    (N13Infinity.wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K
    (N13Infinity.sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]

private theorem ySeries_coeff_neg_three :
    (N13Infinity.ySeries K).coeff (-3 : ℤ) = 1 := by
  simp only [N13Infinity.ySeries, N13Infinity.parameter,
    HahnSeries.inv_single, inv_one,
    HahnSeries.single_pow, one_pow]
  rw [HahnSeries.coeff_single_mul]
  norm_num
  exact wSeries_coeff_zero (K := K)

theorem evalPlusLift_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K (plusLift D)).coeff (-3 : ℤ) = 1 := by
  rw [plusLift, map_sub, HahnSeries.coeff_sub,
    evalSqrtInfinity_coeff_neg_three]
  rw [evalPoly_coeff_neg_three_eq_zero
    (plusRemainder D) (by
      exact (plusRemainder_natDegree_le_one D hdeg).trans (by omega))]
  norm_num

theorem evalNegMinusLift_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K (-minusLift D)).coeff (-3 : ℤ) = 1 := by
  rw [show -minusLift D =
      sqrtInfinity + minusRemainder D by
        unfold minusLift
        ring,
    map_add, HahnSeries.coeff_add,
    evalSqrtInfinity_coeff_neg_three]
  rw [evalPoly_coeff_neg_three_eq_zero
    (minusRemainder D) (by
      exact (minusRemainder_natDegree_le_one D hdeg).trans (by omega))]
  norm_num

private theorem linearFunction_neg_eq_ySubClass
    (V : K[X]) :
    N13BranchNorm.linearFunction K (-V) 1 =
      ySubClass (N13Mumford.model K) V := by
  simp [N13BranchNorm.linearFunction, ySubClass]
  ring

private theorem branch_order_lower_bounds_of_natDegree_three
    (V : K[X]) (hV : V.natDegree = 3) :
    (-3 : ℤ) ≤
        (N13Infinity.coordinateToLaurent K
          (ySubClass (N13Mumford.model K) V)).order ∧
      (-3 : ℤ) ≤
        (N13InfinityMinus.coordinateToLaurentMinus K
          (ySubClass (N13Mumford.model K) V)).order := by
  have hlinear := linearFunction_neg_eq_ySubClass (K := K) V
  have hmin := N13BranchLeading.branch_min_order K (-V) 1
    (by
      rw [hlinear]
      exact ySubClass_ne_zero (N13Mumford.model K) V)
  rw [hlinear] at hmin
  have hpole :
      N13BranchLeading.poleDegree K (-V) 1 = 3 := by
    simp [N13BranchLeading.poleDegree, hV]
  rw [hpole] at hmin
  constructor <;> omega

theorem plusYSub_minus_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (ySubClass (N13Mumford.model K) (plusLift D))).coeff
        (-3 : ℤ) = -2 := by
  rw [ySubClass, map_sub,
    N13InfinityMinus.coordinateToLaurentMinus_yClass,
    N13InfinityMinus.coordinateToLaurentMinus_xClass]
  change
    (N13InfinityMinus.ySeriesMinus K -
      N13BranchNorm.evalPoly K (plusLift D)).coeff (-3 : ℤ) = -2
  rw [N13InfinityMinus.ySeriesMinus_eq_neg,
    HahnSeries.coeff_sub, HahnSeries.coeff_neg,
    ySeries_coeff_neg_three,
    evalPlusLift_coeff_neg_three D hdeg]
  norm_num

theorem minusYSub_plus_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (minusLift D))).coeff
        (-3 : ℤ) = 2 := by
  rw [ySubClass, map_sub,
    N13BranchNorm.coordinateToLaurent_yClass,
    N13Infinity.coordinateToLaurent_xClass]
  change
    (N13Infinity.ySeries K -
      N13BranchNorm.evalPoly K (minusLift D)).coeff (-3 : ℤ) = 2
  have hneg :
      N13BranchNorm.evalPoly K (minusLift D) =
        -N13BranchNorm.evalPoly K (-minusLift D) := by
    simp
  rw [hneg, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
    ySeries_coeff_neg_three,
    evalNegMinusLift_coeff_neg_three D hdeg]
  norm_num

theorem plusYSub_minus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (ySubClass (N13Mumford.model K) (plusLift D))).order = -3 := by
  have hlower :=
    (branch_order_lower_bounds_of_natDegree_three
      (K := K) (plusLift D)
      (plusLift_isMonicOfDegree D hdeg).natDegree_eq).2
  have hupper :
      (N13InfinityMinus.coordinateToLaurentMinus K
        (ySubClass (N13Mumford.model K) (plusLift D))).order ≤
          (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [plusYSub_minus_coeff_neg_three D hdeg]
      norm_num)
  exact le_antisymm hupper hlower

theorem minusYSub_plus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (minusLift D))).order = -3 := by
  have hlower :=
    (branch_order_lower_bounds_of_natDegree_three
      (K := K) (minusLift D)
      (by
        rw [← natDegree_neg]
        exact (neg_minusLift_isMonicOfDegree D hdeg).natDegree_eq)).1
  have hupper :
      (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) (minusLift D))).order ≤
          (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [minusYSub_plus_coeff_neg_three D hdeg]
      norm_num)
  exact le_antisymm hupper hlower

/-! ## Exact orders of the principal Cantor corrections -/

theorem plusNormNumerator_eq :
    N13BranchNorm.normNumerator K (-(plusLift D)) 1 =
      -(D.u * plusFactor D) := by
  simp only [N13BranchNorm.normNumerator, neg_sq, one_pow, one_mul]
  rw [← plusFactor_spec D]
  ring

theorem plusNormNumerator_ne_zero :
    N13BranchNorm.normNumerator K (-(plusLift D)) 1 ≠ 0 := by
  rw [plusNormNumerator_eq D]
  exact neg_ne_zero.mpr
    (mul_ne_zero D.u_monic.ne_zero (plusFactor_ne_zero D))

theorem plusNormNumerator_natDegree :
    (N13BranchNorm.normNumerator K (-(plusLift D)) 1).natDegree =
      D.u.natDegree + (plusFactor D).natDegree := by
  rw [plusNormNumerator_eq D, natDegree_neg,
    natDegree_mul D.u_monic.ne_zero (plusFactor_ne_zero D)]

theorem plusYSub_branch_orders_add :
    (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) (plusLift D))).order +
      (N13InfinityMinus.coordinateToLaurentMinus K
        (ySubClass (N13Mumford.model K) (plusLift D))).order =
      -((D.u.natDegree + (plusFactor D).natDegree : ℕ) : ℤ) := by
  have hsum := N13BranchNorm.branch_orders_add K
    (-(plusLift D)) 1 (plusNormNumerator_ne_zero D)
  rw [linearFunction_neg_eq_ySubClass] at hsum
  rw [plusNormNumerator_natDegree D] at hsum
  exact hsum

theorem plusYSub_plus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (plusLift D))).order =
        3 - (D.u.natDegree : ℤ) -
          ((plusFactor D).natDegree : ℤ) := by
  have hsum := plusYSub_branch_orders_add D
  have hminus := plusYSub_minus_order D hdeg
  omega

theorem ordPlus_ySubFunctionUnit
    (V : K[X]) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (ySubFunctionUnit (N13Mumford.model K) V)) =
      (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) V)).order := by
  change
    (N13Infinity.functionFieldToLaurent K
      (algebraMap
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (ySubClass (N13Mumford.model K) V))).order = _
  rw [N13Infinity.functionFieldToLaurent_algebraMap]

theorem ordPlus_xClassFunctionUnit
    (p : K[X]) (hp : p ≠ 0) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (xClassFunctionUnit (N13Mumford.model K) p hp)) =
      -(p.natDegree : ℤ) := by
  change
    (N13Infinity.functionFieldToLaurent K
      (algebraMap
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (xClass (N13Mumford.model K) p))).order =
      -(p.natDegree : ℤ)
  rw [N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass]
  exact N13BranchNorm.evalPoly_order K p hp

theorem plusCorrection_order
    (hdeg : D.u.natDegree ≤ 2) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (cantorCorrectionUnit (N13Mumford.model K)
          (plusLift D) (plusFactor D) (plusFactor_ne_zero D))) =
      3 - (D.u.natDegree : ℤ) := by
  rw [cantorCorrectionUnit, map_mul, map_inv,
    toAdd_mul, toAdd_inv,
    ordPlus_ySubFunctionUnit,
    ordPlus_xClassFunctionUnit,
    plusYSub_plus_order D hdeg,
    natDegree_normalize_eq]
  ring

theorem minusCorrection_order
    (hdeg : D.u.natDegree ≤ 2) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (cantorCorrectionUnit (N13Mumford.model K)
          (minusLift D) (minusFactor D) (minusFactor_ne_zero D))) =
      (minusFactor D).natDegree - 3 := by
  rw [cantorCorrectionUnit, map_mul, map_inv,
    toAdd_mul, toAdd_inv,
    ordPlus_ySubFunctionUnit,
    ordPlus_xClassFunctionUnit,
    minusYSub_plus_order D hdeg,
    natDegree_normalize_eq]
  ring

/-! ## The two class-preserving balancing steps -/

def plusStep :
    N13Mumford.SemiMumford K :=
  cantorNextSemi (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D
    (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)

def minusStep :
    N13Mumford.SemiMumford K :=
  cantorNextSemi (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D
    (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusFactor_ne_zero D)

@[simp] theorem plusStep_nInf
    (hdeg : D.u.natDegree ≤ 2) :
    (plusStep D).nInf =
      D.nInf + (D.u.natDegree : ℤ) - 3 := by
  change D.nInf - Multiplicative.toAdd
    ((N13Infinity.positiveInfinityOrder K).ordPlus
      (cantorCorrectionUnit (N13Mumford.model K)
        (plusLift D) (plusFactor D) (plusFactor_ne_zero D))) = _
  rw [plusCorrection_order D hdeg]
  ring

@[simp] theorem minusStep_nInf
    (hdeg : D.u.natDegree ≤ 2) :
    (minusStep D).nInf =
      D.nInf + 3 - (minusFactor D).natDegree := by
  change D.nInf - Multiplicative.toAdd
    ((N13Infinity.positiveInfinityOrder K).ordPlus
      (cantorCorrectionUnit (N13Mumford.model K)
        (minusLift D) (minusFactor D) (minusFactor_ne_zero D))) = _
  rw [minusCorrection_order D hdeg]
  ring

@[simp] theorem plusStep_natDegree :
    (plusStep D).u.natDegree = (plusFactor D).natDegree := by
  exact cantorNextSemi_natDegree (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)

@[simp] theorem minusStep_natDegree :
    (minusStep D).u.natDegree = (minusFactor D).natDegree := by
  exact cantorNextSemi_natDegree (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusFactor_ne_zero D)

private theorem adaptedBezout
    (V w : K[X])
    (hcurve : N13Mumford.f K - V ^ 2 = D.u * w)
    (hcongr : D.u ∣ V - D.v) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * V) + c * w = 1 := by
  obtain ⟨t, ht⟩ := hcongr
  have hV : V = D.v + D.u * t := by
    linear_combination ht
  rw [hV]
  exact cantorBezout_add_mul (N13Mumford.model K) D t w
    (by simpa only [N13Mumford.model_f, hV] using hcurve)

theorem plusStep_class :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) (plusStep D) =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D := by
  unfold plusStep
  apply cantorNextSemi_class
    (N13Mumford.model K) (N13Infinity.positiveInfinityOrder K)
    D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)
    (plusLift_congr D)
  exact adaptedBezout D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusLift_congr D)

theorem minusStep_class :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) (minusStep D) =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D := by
  unfold minusStep
  apply cantorNextSemi_class
    (N13Mumford.model K) (N13Infinity.positiveInfinityOrder K)
    D (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusFactor_ne_zero D)
    (minusLift_congr D)
  exact adaptedBezout D (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusLift_congr D)

abbrev LowDegree :
    Type u :=
  LowDegreeSemi (N13Mumford.model K)

def plusStepLow (E : LowDegree (K := K)) :
    LowDegree (K := K) where
  toSemi := plusStep E.toSemi
  degree_le_two := by
    rw [plusStep_natDegree]
    exact plusFactor_natDegree_le_two E.toSemi E.degree_le_two

def minusStepLow (E : LowDegree (K := K)) :
    LowDegree (K := K) where
  toSemi := minusStep E.toSemi
  degree_le_two := by
    rw [minusStep_natDegree]
    exact minusFactor_natDegree_le_two E.toSemi E.degree_le_two

theorem minusStep_nInf_gt
    (E : LowDegree (K := K)) :
    E.toSemi.nInf < (minusStep E.toSemi).nInf := by
  have he :=
    minusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [minusStep_nInf E.toSemi E.degree_le_two]
  omega

theorem minusStep_upper_wall
    (E : LowDegree (K := K)) (_hn : E.toSemi.nInf < 0) :
    ((minusStep E.toSemi).u.natDegree : ℤ) +
        (minusStep E.toSemi).nInf ≤ 2 := by
  have he :=
    minusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [minusStep_natDegree,
    minusStep_nInf E.toSemi E.degree_le_two]
  omega

theorem plusStep_lower_wall
    (E : LowDegree (K := K))
    (hhigh : 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf) :
    0 ≤ (plusStep E.toSemi).nInf := by
  rw [plusStep_nInf E.toSemi E.degree_le_two]
  omega

theorem plusStep_upper_excess_lt
    (E : LowDegree (K := K)) :
    ((plusStep E.toSemi).u.natDegree : ℤ) +
          (plusStep E.toSemi).nInf - 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf - 2 := by
  have he :=
    plusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [plusStep_natDegree,
    plusStep_nInf E.toSemi E.degree_le_two]
  omega

/-! ## A well-founded measure for the two balance walls -/

def lowerDefect (E : LowDegree (K := K)) : ℕ :=
  Int.toNat (-E.toSemi.nInf)

def upperDefect (E : LowDegree (K := K)) : ℕ :=
  Int.toNat
    ((E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf - 2)

def imbalance (E : LowDegree (K := K)) : ℕ :=
  lowerDefect E + upperDefect E

def IsBalanced (E : LowDegree (K := K)) : Prop :=
  0 ≤ E.toSemi.nInf ∧
    (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf ≤ 2

theorem imbalance_eq_zero_iff
    (E : LowDegree (K := K)) :
    imbalance E = 0 ↔ IsBalanced E := by
  simp only [imbalance, Nat.add_eq_zero_iff, lowerDefect, upperDefect,
    Int.toNat_eq_zero, IsBalanced]
  omega

theorem imbalance_minusStepLow_lt
    (E : LowDegree (K := K)) (hn : E.toSemi.nInf < 0) :
    imbalance (minusStepLow E) < imbalance E := by
  have hgt := minusStep_nInf_gt E
  have hnewUpper := minusStep_upper_wall E hn
  have holdUpper :
      upperDefect E = 0 := by
    rw [upperDefect, Int.toNat_eq_zero]
    have hd := E.degree_le_two
    omega
  have hnextUpper :
      upperDefect (minusStepLow E) = 0 := by
    rw [upperDefect, Int.toNat_eq_zero]
    exact sub_nonpos.mpr hnewUpper
  rw [imbalance, imbalance, holdUpper, hnextUpper,
    Nat.add_zero, Nat.add_zero]
  apply (Int.toNat_lt_toNat (by omega)).2
  change -(minusStep E.toSemi).nInf < -E.toSemi.nInf
  omega

theorem imbalance_plusStepLow_lt
    (E : LowDegree (K := K))
    (hn : 0 ≤ E.toSemi.nInf)
    (hhigh : 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf) :
    imbalance (plusStepLow E) < imbalance E := by
  have hnewLower := plusStep_lower_wall E hhigh
  have hexcess := plusStep_upper_excess_lt E
  have holdLower :
      lowerDefect E = 0 := by
    rw [lowerDefect, Int.toNat_eq_zero]
    omega
  have hnextLower :
      lowerDefect (plusStepLow E) = 0 := by
    rw [lowerDefect, Int.toNat_eq_zero]
    exact neg_nonpos.mpr hnewLower
  rw [imbalance, imbalance, holdLower, hnextLower,
    Nat.zero_add, Nat.zero_add]
  apply (Int.toNat_lt_toNat (by omega)).2
  exact hexcess

/-! ## Structural infinity balancing -/

def toBalanced
    (E : LowDegree (K := K))
    (hzero : 0 ≤ E.toSemi.nInf)
    (hupper :
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf ≤ 2) :
    N13Mumford.Mumford K where
  u := E.toSemi.u
  v := E.toSemi.v
  nInf := Int.toNat E.toSemi.nInf
  u_monic := E.toSemi.u_monic
  deg_u := E.degree_le_two
  v_reduced := E.toSemi.v_reduced
  curve_dvd := E.toSemi.curve_dvd
  infinity_bound := by
    have hn :
        ((Int.toNat E.toSemi.nInf : ℕ) : ℤ) =
          E.toSemi.nInf :=
      Int.toNat_of_nonneg hzero
    omega

@[simp] theorem toBalanced_toSemi
    (E : LowDegree (K := K))
    (hzero : 0 ≤ E.toSemi.nInf)
    (hupper :
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf ≤ 2) :
    (toBalanced E hzero hupper).toSemi = E.toSemi := by
  cases E with
  | mk D hdeg =>
      cases D with
      | mk u v n hu hv hc =>
          simp only [toBalanced, Mumford.toSemi]
          congr
          exact Int.toNat_of_nonneg hzero

def balanceInfinity
    (E : LowDegree (K := K)) :
    N13Mumford.Mumford K :=
  if hn : E.toSemi.nInf < 0 then
    balanceInfinity (minusStepLow E)
  else if hhigh :
      2 < (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf then
    balanceInfinity (plusStepLow E)
  else
    toBalanced E (le_of_not_gt hn) (le_of_not_gt hhigh)
termination_by imbalance E
decreasing_by
  · exact imbalance_minusStepLow_lt E hn
  · exact imbalance_plusStepLow_lt E (le_of_not_gt hn) hhigh

theorem balanceInfinity_class
    (E : LowDegree (K := K)) :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)
        (balanceInfinity E).toSemi =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) E.toSemi := by
  fun_induction balanceInfinity E with
  | case1 E hn ih =>
      exact ih.trans (minusStep_class E.toSemi)
  | case2 E hn hhigh ih =>
      exact ih.trans (plusStep_class E.toSemi)
  | case3 E hn hhigh =>
      rw [toBalanced_toSemi]

def normalizeSemi
    (D₀ : N13Mumford.SemiMumford K) :
    N13Mumford.Mumford K :=
  balanceInfinity
    (reduceDegree (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) D₀)

theorem normalizeSemi_class
    (D₀ : N13Mumford.SemiMumford K) :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)
        (normalizeSemi D₀).toSemi =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D₀ := by
  exact
    (balanceInfinity_class
      (reduceDegree (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D₀)).trans
      (reduceDegree_class (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D₀)

theorem classOf_surjective :
    Function.Surjective
      (classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)) := by
  intro c
  obtain ⟨E, hE⟩ :=
    exists_lowDegreeSemiRepresentative
      (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) c
  refine ⟨balanceInfinity E, ?_⟩
  rw [← semiMumfordClass_toSemi]
  exact (balanceInfinity_class E).trans hE

end

end MazurProof.N13MumfordInfinityBalance


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13EffectiveInfinityRepair
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Move the balanced upper wall by an actual Cantor principal relation. The
result lies in the effective degree-two chamber relative to two copies of
positive infinity. This does not assert an integral chart extension theorem.
-/

namespace MazurProof.N13EffectiveInfinityRepair

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]
local instance instDecidableEq_fLT : DecidableEq K := Classical.decEq K

open SexticMumford N13MumfordInfinityBalance
open Polynomial

abbrev Model : SexticMumford.Model K := N13Mumford.model K

/-- If the affine degree is d, the raw order is nInf - 1. Relative to
2 infinity-plus, the two effective infinity multiplicities are nInf + 1
and 1 - d - nInf. These inequalities make both nonnegative. -/
def EffectiveChamber (E : N13Mumford.SemiMumford K) : Prop :=
  E.u.natDegree ≤ 2 ∧ -1 ≤ E.nInf ∧
    (E.u.natDegree : ℤ) + E.nInf ≤ 1

/-- The only balanced inputs outside the effective chamber are on the
upper wall d + nInf = 2. One positive-branch cubic Cantor step repairs
all of them, changing the affine polynomial and its principal relation. -/
def repair (D : N13Mumford.Mumford K) : N13Mumford.SemiMumford K :=
  if D.u.natDegree + D.nInf = 2 then plusStep D.toSemi else D.toSemi

theorem repair_class (D : N13Mumford.Mumford K) :
    semiMumfordClass Model (N13Infinity.positiveInfinityOrder K) (repair D) =
      classOf Model (N13Infinity.positiveInfinityOrder K) D := by
  unfold repair
  split
  · simpa only [semiMumfordClass_toSemi] using plusStep_class D.toSemi
  · rfl

theorem repair_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    repair D = plusStep D.toSemi := by
  simp only [repair, hwall, if_true]

theorem repair_nInf_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    (repair D).nInf = -1 := by
  rw [repair_of_upper_wall D hwall, plusStep_nInf D.toSemi D.deg_u]
  simp only [toSemi_nInf, toSemi_u]
  omega

/-- The residual horizontal polynomial is the normalized quotient
(f - V^2)/u, with V the positive-branch cubic lift. -/
theorem repair_u_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    (repair D).u = normalize (plusFactor D.toSemi) := by
  rw [repair_of_upper_wall D hwall]
  exact cantorNextSemi_u Model (N13Infinity.positiveInfinityOrder K)
    D.toSemi (plusLift D.toSemi) (plusFactor D.toSemi)
    (plusFactor_spec D.toSemi) (plusFactor_ne_zero D.toSemi)

/-- The residual graph uses the conjugate ordinate, including multiplicity. -/
theorem repair_v_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    (repair D).v = (-plusLift D.toSemi) % normalize (plusFactor D.toSemi) := by
  rw [repair_of_upper_wall D hwall]
  exact cantorNextSemi_v Model (N13Infinity.positiveInfinityOrder K)
    D.toSemi (plusLift D.toSemi) (plusFactor D.toSemi)
    (plusFactor_spec D.toSemi) (plusFactor_ne_zero D.toSemi)

/-- The actual rational function (Y - V)/normalize(w) for the repair. -/
def correction (D : N13Mumford.Mumford K) : (N13Mumford.FunctionField K)ˣ :=
  cantorCorrectionUnit Model (plusLift D.toSemi) (plusFactor D.toSemi)
    (plusFactor_ne_zero D.toSemi)

theorem correction_order (D : N13Mumford.Mumford K) :
    Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus (correction D)) =
      3 - (D.u.natDegree : ℤ) :=
  plusCorrection_order D.toSemi D.deg_u

/-- Exact affine principal-ideal relation, with the named correction
function, before passing to a quotient. -/
theorem repair_ideal_principal_relation
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    mumfordIdealUnit Model (repair D) *
        toPrincipalIdeal (CoordinateRing Model) (FunctionField Model) (correction D) =
      mumfordIdealUnit Model D.toSemi := by
  have hcongr := plusLift_congr D.toSemi
  obtain ⟨t, ht⟩ := hcongr
  have hV : plusLift D.toSemi = D.toSemi.v + D.toSemi.u * t := by
    linear_combination ht
  have hbez : ∃ a b c : K[X],
      a * D.toSemi.u + b * (2 * plusLift D.toSemi) +
        c * plusFactor D.toSemi = 1 := by
    rw [hV]
    apply cantorBezout_add_mul Model D.toSemi t (plusFactor D.toSemi)
    simpa only [N13Mumford.model_f, hV] using plusFactor_spec D.toSemi
  rw [repair_of_upper_wall D hwall]
  exact cantorConjugateSemi_principalRelation Model D.toSemi
    (plusLift D.toSemi) (plusFactor D.toSemi)
    (cantorNextNInf Model (N13Infinity.positiveInfinityOrder K) D.toSemi
      (plusLift D.toSemi) (plusFactor D.toSemi) (plusFactor_ne_zero D.toSemi))
    (plusFactor_spec D.toSemi) (plusFactor_ne_zero D.toSemi)
    (plusLift_congr D.toSemi) hbez

theorem repair_natDegree_le_two (D : N13Mumford.Mumford K) :
    (repair D).u.natDegree ≤ 2 := by
  unfold repair
  split
  · rw [plusStep_natDegree]
    exact plusFactor_natDegree_le_two D.toSemi D.deg_u
  · exact D.deg_u

theorem repair_effective (D : N13Mumford.Mumford K) :
    EffectiveChamber (repair D) := by
  refine ⟨repair_natDegree_le_two D, ?_⟩
  by_cases hwall : D.u.natDegree + D.nInf = 2
  · rw [repair_nInf_of_upper_wall D hwall]
    have hd := repair_natDegree_le_two D
    omega
  · have hb := D.infinity_bound
    simp only [repair, hwall, if_false, toSemi_nInf, toSemi_u]
    omega

/-- The degree-one/nInf=1 case changes to the residual quadratic-or-lower
graph, with raw infinity exponent -2. -/
theorem repair_degree_one
    (D : N13Mumford.Mumford K)
    (hd : D.u.natDegree = 1) (hn : D.nInf = 1) :
    repair D = plusStep D.toSemi ∧ (repair D).nInf = -1 := by
  have hwall : D.u.natDegree + D.nInf = 2 := by omega
  exact ⟨repair_of_upper_wall D hwall, repair_nInf_of_upper_wall D hwall⟩

/-- Every balanced degree-two input is on the upper wall and gets the
same concrete residual-graph repair. -/
theorem repair_degree_two
    (D : N13Mumford.Mumford K) (hd : D.u.natDegree = 2) :
    repair D = plusStep D.toSemi ∧ (repair D).nInf = -1 := by
  have hb := D.infinity_bound
  have hwall : D.u.natDegree + D.nInf = 2 := by omega
  exact ⟨repair_of_upper_wall D hwall, repair_nInf_of_upper_wall D hwall⟩

/-- Coefficients for an actual effective infinity completion of the repaired
affine graph; no natural-number truncation changes their integer values. -/
def positiveMultiplicity (E : N13Mumford.SemiMumford K) : ℕ :=
  Int.toNat (E.nInf + 1)

def negativeMultiplicity (E : N13Mumford.SemiMumford K) : ℕ :=
  Int.toNat (1 - (E.u.natDegree : ℤ) - E.nInf)

theorem positiveMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (positiveMultiplicity E : ℤ) = E.nInf + 1 := by
  apply Int.toNat_of_nonneg
  have := h.2.1
  omega

theorem negativeMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (negativeMultiplicity E : ℤ) = 1 - (E.u.natDegree : ℤ) - E.nInf := by
  apply Int.toNat_of_nonneg
  have := h.2.2
  omega

theorem completed_degree_two
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    E.u.natDegree + positiveMultiplicity E + negativeMultiplicity E = 2 := by
  have hp := positiveMultiplicity_cast E h
  have hm := negativeMultiplicity_cast E h
  omega

theorem infinity_mark_eq_positiveMultiplicity_sub_two
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    E.nInf - 1 = (positiveMultiplicity E : ℤ) - 2 := by
  rw [positiveMultiplicity_cast E h]
  omega

theorem repaired_upper_wall_multiplicities
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    positiveMultiplicity (repair D) = 0 ∧
      negativeMultiplicity (repair D) = 2 - (repair D).u.natDegree := by
  have hn := repair_nInf_of_upper_wall D hwall
  have hh := repair_effective D
  have hp := positiveMultiplicity_cast (repair D) hh
  have hm := negativeMultiplicity_cast (repair D) hh
  have hd := hh.1
  omega

/-- The representative is given explicitly; existence is not an assumption. -/
theorem exists_effective_representative (D : N13Mumford.Mumford K) :
    ∃ E : N13Mumford.SemiMumford K, EffectiveChamber E ∧
      semiMumfordClass Model (N13Infinity.positiveInfinityOrder K) E =
        classOf Model (N13Infinity.positiveInfinityOrder K) D :=
  ⟨repair D, repair_effective D, repair_class D⟩

end
end MazurProof.N13EffectiveInfinityRepair


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RankTwoQuotientAlgebra
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Rank-two quotient algebras for the N13 integral graph

Once a relative degree-two divisor has been shown finite and flat, its
affine coordinate quotient is free of rank two with the literal basis
`{1,x}`.  This file records the structural algebra needed to recover its
Mumford equation.

A basis `{1,x}` is a power basis.  Over an arbitrary nontrivial
commutative base ring, evaluation at its generator has kernel generated by
the power-basis relation polynomial.  That polynomial is also the
characteristic polynomial of multiplication by the generator.
-/

open Module
open Polynomial

namespace MazurProof.N13RankTwoQuotientAlgebra

noncomputable section

universe u v

variable {R : Type u} {B : Type v}

section PowerBasisKernel

variable [CommRing R] [Nontrivial R]
variable [Ring B] [Algebra R B]

/-- A power basis presents its algebra as the polynomial quotient by the
relation polynomial of its generator.  The proof uses monic division and
linear independence of the power basis, so no domain hypothesis is needed. -/
theorem ker_aeval_eq_span_minpolyGen
    (pb : PowerBasis R B) :
    RingHom.ker (aeval pb.gen) =
      Ideal.span ({pb.minpolyGen} : Set R[X]) := by
  apply le_antisymm
  · intro p hp
    rw [Ideal.mem_span_singleton]
    have hpRoot : aeval pb.gen p = 0 :=
      RingHom.mem_ker.mp hp
    have hremRoot :
        aeval pb.gen (p %ₘ pb.minpolyGen) = 0 := by
      have hdiv :=
        modByMonic_add_div p pb.minpolyGen
      calc
        aeval pb.gen (p %ₘ pb.minpolyGen) =
            aeval pb.gen
              (p - pb.minpolyGen * (p /ₘ pb.minpolyGen)) := by
          congr 1
          exact eq_sub_of_add_eq hdiv
        _ =
            aeval pb.gen p -
              aeval pb.gen pb.minpolyGen *
                aeval pb.gen (p /ₘ pb.minpolyGen) := by
          simp only [map_sub, map_mul]
        _ = 0 := by
          rw [hpRoot, pb.aeval_minpolyGen, zero_mul, sub_zero]
    have hrem :
        p %ₘ pb.minpolyGen = 0 := by
      by_contra hne
      have hle :=
        pb.dim_le_degree_of_root hne hremRoot
      have hlt :
          degree (p %ₘ pb.minpolyGen) < pb.dim := by
        simpa [pb.degree_minpolyGen] using
          degree_modByMonic_lt p pb.minpolyGen_monic
      exact (not_le_of_gt hlt) hle
    exact
      (modByMonic_eq_zero_iff_dvd pb.minpolyGen_monic).mp hrem
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.mpr pb.aeval_minpolyGen

end PowerBasisKernel

section CharacteristicPolynomial

variable [CommRing R]
variable [Ring B] [Algebra R B]
variable [Module.Free R B] [Module.Finite R B]

/-- The characteristic polynomial of multiplication by the generator is
the power-basis relation polynomial. -/
theorem charpoly_lmul_eq_minpolyGen
    (pb : PowerBasis R B) :
    (Algebra.lmul R B pb.gen).charpoly =
      pb.minpolyGen := by
  rw [← LinearMap.charpoly_toMatrix
      (Algebra.lmul R B pb.gen) pb.basis,
    ← Algebra.leftMulMatrix_apply,
    charpoly_leftMulMatrix,
    ← pb.minpolyGen_eq]

/-- Hence the evaluation kernel is generated by the characteristic
polynomial of multiplication by the power-basis generator. -/
theorem ker_aeval_eq_span_charpoly
    [Nontrivial R]
    (pb : PowerBasis R B) :
    RingHom.ker (aeval pb.gen) =
      Ideal.span
        ({(Algebra.lmul R B pb.gen).charpoly} : Set R[X]) := by
  rw [charpoly_lmul_eq_minpolyGen]
  exact ker_aeval_eq_span_minpolyGen pb

end CharacteristicPolynomial

section LiteralOneXBasis

variable [CommRing R]
variable [Ring B] [Algebra R B]

/-- A literal rank-two basis `{1,x}` is a power basis generated by `x`. -/
def powerBasisOfOneX
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    PowerBasis R B where
  gen := x
  dim := 2
  basis := b
  basis_eq_pow i := by
    fin_cases i
    · simpa using hb0
    · simpa using hb1

@[simp] theorem powerBasisOfOneX_gen
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    (powerBasisOfOneX x b hb0 hb1).gen = x := rfl

@[simp] theorem powerBasisOfOneX_dim
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    (powerBasisOfOneX x b hb0 hb1).dim = 2 := rfl

/-- Kernel presentation specialized to a literal rank-two basis `{1,x}`. -/
theorem ker_aeval_eq_span_charpoly_of_one_x
    [Nontrivial R]
    [Module.Free R B] [Module.Finite R B]
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    RingHom.ker (aeval x) =
      Ideal.span
        ({(Algebra.lmul R B x).charpoly} : Set R[X]) := by
  simpa using
    ker_aeval_eq_span_charpoly
      (powerBasisOfOneX x b hb0 hb1)

/-- The multiplication characteristic polynomial is monic. -/
theorem charpoly_lmul_monic_of_one_x
    [Module.Free R B] [Module.Finite R B]
    (x : B) :
    (Algebra.lmul R B x).charpoly.Monic :=
  LinearMap.charpoly_monic _

/-- For a rank-two power basis, the multiplication characteristic
polynomial has degree exactly two. -/
theorem charpoly_lmul_natDegree_of_one_x
    [Nontrivial R]
    [Module.Free R B] [Module.Finite R B]
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    (Algebra.lmul R B x).charpoly.natDegree = 2 := by
  let pb := powerBasisOfOneX x b hb0 hb1
  calc
    (Algebra.lmul R B x).charpoly.natDegree =
        pb.minpolyGen.natDegree := by
      rw [show x = pb.gen by rfl,
        charpoly_lmul_eq_minpolyGen]
    _ = pb.dim := pb.natDegree_minpolyGen
    _ = 2 := rfl

/-- Cayley--Hamilton gives the defining quadratic relation at `x`. -/
theorem aeval_charpoly_lmul_eq_zero
    [Module.Free R B] [Module.Finite R B]
    (x : B) :
    aeval x (Algebra.lmul R B x).charpoly = 0 :=
  Algebra.aeval_self_charpoly_lmul x

/-- Every element of a rank-two algebra with basis `{1,x}` has a unique
linear-polynomial expression in `x`; only existence is needed downstream. -/
theorem exists_eq_algebraMap_add_algebraMap_mul
    [Nontrivial R] [Nontrivial B]
    (x y : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    ∃ a c : R,
      y = algebraMap R B a + algebraMap R B c * x := by
  let pb := powerBasisOfOneX x b hb0 hb1
  obtain ⟨f, hf, hy⟩ := pb.exists_eq_aeval y
  have hf' : f.natDegree ≤ 1 := by
    simpa [pb] using Nat.le_of_lt_succ hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf'] at hy
  have hy' :
      y =
        algebraMap R B (f.coeff 1) * x +
          algebraMap R B (f.coeff 0) := by
    simpa [pb] using hy
  calc
    y =
        algebraMap R B (f.coeff 1) * x +
          algebraMap R B (f.coeff 0) := hy'
    _ =
        algebraMap R B (f.coeff 0) +
          algebraMap R B (f.coeff 1) * x := by
      rw [add_comm]

end LiteralOneXBasis

end

end MazurProof.N13RankTwoQuotientAlgebra


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FiniteFlatBasisLift
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Lifting the literal special-fibre basis `{1,x}`

For a finite flat algebra over a local ring, a family whose residue-field
base change is a basis is already a basis over the local ring.  This file
specializes the structural local lifting theorem to the literal family
`{1,x}` needed by the N13 quotient.
-/

open scoped TensorProduct
open Module

namespace MazurProof.N13FiniteFlatBasisLift

noncomputable section

universe uR uB

variable {R : Type uR} {B : Type uB}
variable [CommRing R] [IsLocalRing R]
variable [CommRing B] [Algebra R B]
variable [Module.Finite R B] [Module.Flat R B]

local notation "k" => IsLocalRing.ResidueField R

/-- The literal two-element family. -/
def oneX (x : B) : Fin 2 → B :=
  ![1, x]

@[simp] theorem oneX_zero (x : B) :
    oneX x (0 : Fin 2) = 1 := by
  simp [oneX]

@[simp] theorem oneX_one (x : B) :
    oneX x (1 : Fin 2) = x := by
  simp [oneX]

/--
If `{1,x}` becomes a supplied basis after residue-field base change, then
the same literal family is a basis over the local ring.
-/
theorem exists_basis_oneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    ∃ b : Basis (Fin 2) R B,
      (b : Fin 2 → B) = oneX x := by
  have hfamily :
      (TensorProduct.mk R k B 1 ∘ oneX x) =
        (b₀ : Fin 2 → k ⊗[R] B) := by
    funext i
    exact hb₀ i
  have hk :
      Function.Bijective
        (Finsupp.linearCombination k
          (TensorProduct.mk R k B 1 ∘ oneX x)) := by
    rw [hfamily]
    exact
      ⟨b₀.linearIndependent,
        fun y => ⟨b₀.repr y, b₀.linearCombination_repr y⟩⟩
  have hR :
      Function.Bijective
        (Finsupp.linearCombination R (oneX x)) :=
    Module.IsLocalRing.linearCombination_bijective_of_flat
      (R := R) (M := B) (oneX x) hk
  have hspan :
      ⊤ ≤ Submodule.span R (Set.range (oneX x)) := by
    rw [← Finsupp.range_linearCombination]
    exact (LinearMap.range_eq_top.mpr hR.2).ge
  refine ⟨Basis.mk hR.1 hspan, ?_⟩
  exact Basis.coe_mk hR.1 hspan

/-- A chosen integral basis with underlying family literally `{1,x}`. -/
def basisOneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    Basis (Fin 2) R B :=
  Classical.choose (exists_basis_oneX (R := R) (B := B) x b₀ hb₀)

@[simp] theorem coe_basisOneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    (basisOneX (R := R) (B := B) x b₀ hb₀ : Fin 2 → B) =
      oneX x :=
  Classical.choose_spec
    (exists_basis_oneX (R := R) (B := B) x b₀ hb₀)

@[simp] theorem basisOneX_zero
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    basisOneX (R := R) (B := B) x b₀ hb₀ (0 : Fin 2) = 1 := by
  rw [show
    basisOneX (R := R) (B := B) x b₀ hb₀ (0 : Fin 2) =
      oneX x (0 : Fin 2) by
    exact congrFun (coe_basisOneX (R := R) (B := B) x b₀ hb₀) 0]
  exact oneX_zero x

@[simp] theorem basisOneX_one
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    basisOneX (R := R) (B := B) x b₀ hb₀ (1 : Fin 2) = x := by
  rw [show
    basisOneX (R := R) (B := B) x b₀ hb₀ (1 : Fin 2) =
      oneX x (1 : Fin 2) by
    exact congrFun (coe_basisOneX (R := R) (B := B) x b₀ hb₀) 1]
  exact oneX_one x

/-- The lifted literal basis gives the power basis consumed by the
characteristic-polynomial quotient algebra. -/
def powerBasisOneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    PowerBasis R B :=
  N13RankTwoQuotientAlgebra.powerBasisOfOneX
    x (basisOneX x b₀ hb₀)
    (basisOneX_zero x b₀ hb₀)
    (basisOneX_one x b₀ hb₀)

end

end MazurProof.N13FiniteFlatBasisLift


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodModelTwo
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# A good characteristic-two model of `X₁(13)`

The completed-square sextic is not the model to reduce modulo two.  This file
uses the generalized hyperelliptic equation

`y² + (x³+x+1)y = x⁵+x⁴`.

Over the rationals, completing the square gives the existing N13 sextic.
In characteristic two, the affine chart and the chart at infinity both have
nonzero derivative in the second coordinate.  The `F₂`- and `F₄`-point
counts are obtained from Frobenius and the Artin--Schreier map, not by
enumerating field elements.
-/

namespace MazurProof.N13GoodModelTwo

noncomputable section

open scoped CharTwo
open Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient of `y` in the generalized equation. -/
def h (x : R) : R := x ^ 3 + x + 1

/-- The right-hand side of the generalized equation. -/
def rhs (x : R) : R := x ^ 5 + x ^ 4

/-- The affine equation with zero on the right. -/
def affineResidual (x y : R) : R :=
  y ^ 2 + h x * y - rhs x

/-- The affine generalized hyperelliptic equation. -/
def AffineEquation (x y : R) : Prop :=
  y ^ 2 + h x * y = rhs x

theorem affineEquation_iff_residual (x y : R) :
    AffineEquation x y ↔ affineResidual x y = 0 := by
  simp [AffineEquation, affineResidual, sub_eq_zero]

/-- Its completed-square polynomial. -/
def completedSextic (x : R) : R :=
  x ^ 6 + 4 * x ^ 5 + 6 * x ^ 4 + 2 * x ^ 3 + x ^ 2 + 2 * x + 1

theorem h_sq_add_four_rhs (x : R) :
    h x ^ 2 + 4 * rhs x = completedSextic x := by
  simp only [h, rhs, completedSextic]
  ring

/-- Completing the square before reduction. -/
theorem completed_square_identity (x y : R) :
    (2 * y + h x) ^ 2 =
      completedSextic x + 4 * (y ^ 2 + h x * y - rhs x) := by
  rw [← h_sq_add_four_rhs]
  ring

theorem completedSextic_rat (x : ℚ) :
    completedSextic x = N13CurveModel.sexticF13 x := by
  rfl

/-- The good generalized model maps to the standard sextic over `ℚ`. -/
theorem good_to_sextic
    {x y : ℚ} (hp : AffineEquation x y) :
    N13CurveModel.C13SexticEq x (2 * y + h x) := by
  rw [N13CurveModel.C13SexticEq, ← completedSextic_rat]
  rw [completed_square_identity]
  have hz : y ^ 2 + h x * y - rhs x = 0 :=
    sub_eq_zero.mpr hp
  rw [hz]
  ring

/-- The inverse completed-square coordinate over `ℚ`. -/
def sexticToGoodY (x Y : ℚ) : ℚ :=
  (Y - h x) / 2

theorem good_sextic_y_roundtrip (x y : ℚ) :
    sexticToGoodY x (2 * y + h x) = y := by
  simp only [sexticToGoodY]
  ring

theorem sextic_good_y_roundtrip (x Y : ℚ) :
    2 * sexticToGoodY x Y + h x = Y := by
  simp only [sexticToGoodY]
  ring

/-- The standard sextic maps back to the good generalized model over `ℚ`. -/
theorem sextic_to_good
    {x Y : ℚ} (hp : N13CurveModel.C13SexticEq x Y) :
    AffineEquation x (sexticToGoodY x Y) := by
  have hs := completed_square_identity x (sexticToGoodY x Y)
  rw [sextic_good_y_roundtrip] at hs
  rw [N13CurveModel.C13SexticEq, ← completedSextic_rat] at hp
  rw [hp] at hs
  have hz :
      sexticToGoodY x Y ^ 2 + h x * sexticToGoodY x Y - rhs x = 0 := by
    linarith
  exact sub_eq_zero.mp hz

/-! ## The two charts of the weighted projective completion -/

/-- Weighted-homogeneous equation in coordinates of weights `(1,3,1)`. -/
def WeightedEquation (X Y Z : R) : Prop :=
  Y ^ 2 + (X ^ 3 + X * Z ^ 2 + Z ^ 3) * Y =
    X ^ 5 * Z + X ^ 4 * Z ^ 2

/-- Residual form of the weighted-homogeneous equation. -/
def weightedResidual (X Y Z : R) : R :=
  Y ^ 2 + (X ^ 3 + X * Z ^ 2 + Z ^ 3) * Y -
    (X ^ 5 * Z + X ^ 4 * Z ^ 2)

theorem weightedEquation_iff (X Y Z : R) :
    WeightedEquation X Y Z ↔ weightedResidual X Y Z = 0 := by
  simp [WeightedEquation, weightedResidual, sub_eq_zero]

/-- Weighted homogeneity in weights `(1,3,1)` on `(X,Y,Z)`. -/
theorem weightedResidual_homogeneous (a X Y Z : R) :
    weightedResidual (a * X) (a ^ 3 * Y) (a * Z) =
      a ^ 6 * weightedResidual X Y Z := by
  simp only [weightedResidual]
  ring

/-- The `Z=1` chart is the affine generalized equation. -/
theorem weighted_affine_chart (x y : R) :
    WeightedEquation x y 1 ↔ AffineEquation x y := by
  simp [WeightedEquation, AffineEquation, h, rhs]

/-- Equation on the `X=1` chart, with `t=Z/X` and `v=Y/X³`. -/
def InfinityChartEquation (t v : R) : Prop :=
  v ^ 2 + (1 + t ^ 2 + t ^ 3) * v = t + t ^ 2

/-- Residual form of the `X=1` chart. -/
def infinityChartResidual (t v : R) : R :=
  v ^ 2 + (1 + t ^ 2 + t ^ 3) * v - (t + t ^ 2)

theorem infinityChartEquation_iff (t v : R) :
    InfinityChartEquation t v ↔ infinityChartResidual t v = 0 := by
  simp [InfinityChartEquation, infinityChartResidual, sub_eq_zero]

theorem weighted_infinity_chart (t v : R) :
    WeightedEquation 1 v t ↔ InfinityChartEquation t v := by
  simp [WeightedEquation, InfinityChartEquation]

/-- Clearing the transition denominators identifies the two chart
residuals. -/
theorem overlap_residual
    {x t v : R} (hxt : x * t = 1) :
    affineResidual x (x ^ 3 * v) =
      x ^ 6 * infinityChartResidual t v := by
  have hx6t : x ^ 6 * t = x ^ 5 := by
    calc
      x ^ 6 * t = x ^ 5 * (x * t) := by ring
      _ = x ^ 5 := by rw [hxt, mul_one]
  have hx6t2 : x ^ 6 * t ^ 2 = x ^ 4 := by
    calc
      x ^ 6 * t ^ 2 = x ^ 4 * (x * t) ^ 2 := by ring
      _ = x ^ 4 := by rw [hxt, one_pow, mul_one]
  have hx6t3 : x ^ 6 * t ^ 3 = x ^ 3 := by
    calc
      x ^ 6 * t ^ 3 = x ^ 3 * (x * t) ^ 3 := by ring
      _ = x ^ 3 := by rw [hxt, one_pow, mul_one]
  calc
    affineResidual x (x ^ 3 * v) =
        x ^ 6 * v ^ 2 + (x ^ 6 + x ^ 4 + x ^ 3) * v -
          x ^ 5 - x ^ 4 := by
      simp only [affineResidual, h, rhs]
      ring
    _ = x ^ 6 * v ^ 2 +
          (x ^ 6 + x ^ 6 * t ^ 2 + x ^ 6 * t ^ 3) * v -
          x ^ 6 * t - x ^ 6 * t ^ 2 := by
      rw [hx6t, hx6t2, hx6t3]
    _ = x ^ 6 * infinityChartResidual t v := by
      simp only [infinityChartResidual]
      ring

/-- The two equations agree on the overlap `xt=1`. -/
theorem affine_iff_infinity_on_overlap
    {x t v : R} (hxt : x * t = 1) :
    AffineEquation x (x ^ 3 * v) ↔ InfinityChartEquation t v := by
  have hx : IsUnit x := IsUnit.of_mul_eq_one t hxt
  have hx6 : IsUnit (x ^ 6) := hx.pow 6
  rw [affineEquation_iff_residual, infinityChartEquation_iff,
    overlap_residual hxt]
  constructor
  · intro hz
    exact hx6.mul_left_cancel (by simpa using hz)
  · intro hz
    rw [hz, mul_zero]

/-- Derivative of the affine equation with respect to `y`. -/
def affineDerivativeY (x y : R) : R :=
  2 * y + h x

/-- Derivative of the affine equation with respect to `x`, specialized to
characteristic two. -/
def affineDerivativeXCharTwo (x y : R) : R :=
  (x ^ 2 + 1) * y + x ^ 4

/-- Derivative of the infinity-chart equation with respect to `v`. -/
def infinityDerivativeV (t v : R) : R :=
  2 * v + (1 + t ^ 2 + t ^ 3)

/-- The affine equation as a polynomial in the second coordinate. -/
def affineFiber (x : R) : R[X] :=
  X ^ 2 + C (h x) * X - C (rhs x)

/-- The infinity-chart equation as a polynomial in the second coordinate. -/
def infinityFiber (t : R) : R[X] :=
  X ^ 2 + C (1 + t ^ 2 + t ^ 3) * X - C (t + t ^ 2)

@[simp] theorem affineFiber_eval (x y : R) :
    (affineFiber x).eval y = affineResidual x y := by
  simp [affineFiber, affineResidual]

@[simp] theorem infinityFiber_eval (t v : R) :
    (infinityFiber t).eval v = infinityChartResidual t v := by
  simp [infinityFiber, infinityChartResidual]

theorem affineFiber_derivative (x : R) :
    (affineFiber x).derivative = 2 * X + C (h x) := by
  simp only [affineFiber, derivative_sub, derivative_add, derivative_pow,
    derivative_X, derivative_mul, derivative_C, zero_mul, zero_add, mul_one,
    sub_zero]
  norm_num [map_natCast]
  rw [C_ofNat]

theorem infinityFiber_derivative (t : R) :
    (infinityFiber t).derivative =
      2 * X + C (1 + t ^ 2 + t ^ 3) := by
  simp only [infinityFiber, derivative_sub, derivative_add, derivative_pow,
    derivative_X, derivative_mul, derivative_C, zero_mul, zero_add, mul_one,
    sub_zero]
  norm_num [map_natCast]
  rw [C_ofNat]

theorem affineFiber_derivative_eval (x y : R) :
    (affineFiber x).derivative.eval y = affineDerivativeY x y := by
  rw [affineFiber_derivative]
  simp [affineDerivativeY]

theorem infinityFiber_derivative_eval (t v : R) :
    (infinityFiber t).derivative.eval v = infinityDerivativeV t v := by
  rw [infinityFiber_derivative]
  simp [infinityDerivativeV]

/-! ## Structural characteristic-two point classification -/

variable {K : Type u} [Field K] [CharP K 2]

/-- Elements fixed by the characteristic-two Frobenius. -/
abbrev FixedTwo (K : Type u) [Field K] :=
  {x : K // x ^ 2 = x}

omit [CharP K 2] in
theorem fixedTwo_eq_zero_or_one (x : K) (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 := by
  have hfac : x * (x - 1) = 0 := by
    calc
      x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := sub_eq_zero.mpr hx
  rcases mul_eq_zero.mp hfac with hx0 | hx1
  · exact Or.inl hx0
  · exact Or.inr (sub_eq_zero.mp hx1)

/-- Frobenius-fixed elements are precisely the prime subfield. -/
def fixedTwoEquivPrimeSubfield :
    FixedTwo K ≃ (⊥ : Subfield K) where
  toFun x :=
    ⟨x.1, (Subfield.mem_bot_iff_pow_eq_self (F := K) 2).mpr x.2⟩
  invFun x :=
    ⟨x.1, (Subfield.mem_bot_iff_pow_eq_self (F := K) 2).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem fixedTwo_card [Finite K] :
    Nat.card (FixedTwo K) = 2 := by
  rw [Nat.card_congr (fixedTwoEquivPrimeSubfield (K := K)),
    Subfield.card_bot K 2]

/-- In a field with four-power Frobenius, an affine point has both
coordinates in the prime subfield.  The non-prime-field branch is excluded
by the Artin--Schreier identity, not by a finite table. -/
theorem affineEquation_iff_fixed
    (hfour : ∀ z : K, z ^ 4 = z) (x y : K) :
    AffineEquation x y ↔ x ^ 2 = x ∧ y ^ 2 = y := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro hp
    have hidem : (x ^ 2 + x) ^ 2 = x ^ 2 + x := by
      linear_combination hfour x + x ^ 3 * htwo
    have hcases : x ^ 2 + x = 0 ∨ x ^ 2 + x = 1 := by
      have hfac : (x ^ 2 + x) * ((x ^ 2 + x) - 1) = 0 := by
        calc
          (x ^ 2 + x) * ((x ^ 2 + x) - 1) =
              (x ^ 2 + x) ^ 2 - (x ^ 2 + x) := by ring
          _ = 0 := sub_eq_zero.mpr hidem
      rcases mul_eq_zero.mp hfac with hzero | hone
      · exact Or.inl hzero
      · exact Or.inr (sub_eq_zero.mp hone)
    rcases hcases with hprime | hnonprime
    · have hx : x ^ 2 = x := by
        linear_combination hprime - x * htwo
      have hx3 : x ^ 3 = x := by
        calc
          x ^ 3 = x * x ^ 2 := by ring
          _ = x * x := by rw [hx]
          _ = x := by simpa [pow_two] using hx
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x := by simpa [pow_two] using hx
      have hh : h x = 1 := by
        simp only [h]
        linear_combination hx3 + x * htwo
      have hrhs : rhs x = 0 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + x * htwo
      have hy : y ^ 2 = y := by
        unfold AffineEquation at hp
        rw [hh, hrhs] at hp
        linear_combination hp - y * htwo
      exact ⟨hx, hy⟩
    · have hx3 : x ^ 3 = 1 := by
        linear_combination x * hnonprime - hnonprime + (x - 1) * htwo
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x ^ 2 := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x ^ 2 := by ring
      have hh : h x = x := by
        simp only [h]
        linear_combination hx3 + htwo
      have hrhs : rhs x = 1 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + hnonprime
      have hp' : y ^ 2 + x * y = 1 := by
        simpa [AffineEquation, hh, hrhs] using hp
      let t : K := y * x ^ 2
      have ht : t ^ 2 + t = x := by
        have hx4' : x ^ 4 = x := hfour x
        calc
          t ^ 2 + t = y ^ 2 * x ^ 4 + y * x ^ 2 := by
            simp only [t]
            ring
          _ = y ^ 2 * x + y * x ^ 2 := by rw [hx4']
          _ = x * (y ^ 2 + x * y) := by ring
          _ = x := by rw [hp']; ring
      have htFixed : (t ^ 2 + t) ^ 2 = t ^ 2 + t := by
        linear_combination hfour t + t ^ 3 * htwo
      rw [ht] at htFixed
      have hsumzero : x ^ 2 + x = 0 := by
        linear_combination htFixed + x * htwo
      have hzeroone : (0 : K) = 1 := hsumzero.symm.trans hnonprime
      exact (zero_ne_one hzeroone).elim
  · rintro ⟨hx, hy⟩
    have hx3 : x ^ 3 = x := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ = x * x := by rw [hx]
        _ = x := by simpa [pow_two] using hx
    have hx4 : x ^ 4 = x := hfour x
    have hx5 : x ^ 5 = x := by
      calc
        x ^ 5 = x * x ^ 4 := by ring
        _ = x * x := by rw [hx4]
        _ = x := by simpa [pow_two] using hx
    have hh : h x = 1 := by
      simp only [h]
      linear_combination hx3 + x * htwo
    have hrhs : rhs x = 0 := by
      simp only [rhs]
      linear_combination hx5 + hx4 + x * htwo
    unfold AffineEquation
    rw [hh, hrhs, hy]
    linear_combination y * htwo

/-- Affine points as a finite type. -/
abbrev AffinePoint (K : Type u) [Field K] :=
  {p : K × K // AffineEquation p.1 p.2}

def affinePointEquivFixed
    (hfour : ∀ z : K, z ^ 4 = z) :
    AffinePoint K ≃ FixedTwo K × FixedTwo K where
  toFun P :=
    let hxy := (affineEquation_iff_fixed hfour P.1.1 P.1.2).mp P.2
    (⟨P.1.1, hxy.1⟩, ⟨P.1.2, hxy.2⟩)
  invFun P :=
    ⟨((P.1 : K), (P.2 : K)),
      (affineEquation_iff_fixed hfour (P.1 : K) (P.2 : K)).mpr
        ⟨P.1.property, P.2.property⟩⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv P := by
    ext <;> rfl

theorem affinePoint_card [Finite K]
    (hfour : ∀ z : K, z ^ 4 = z) :
    Nat.card (AffinePoint K) = 4 := by
  rw [Nat.card_congr (affinePointEquivFixed hfour), Nat.card_prod,
    fixedTwo_card]

/-- Points on the fibre `t=0` of the infinity chart. -/
abbrev InfinityPoint (K : Type u) [Field K] :=
  {v : K // InfinityChartEquation 0 v}

theorem infinityChartEquation_zero_iff_fixed (v : K) :
    InfinityChartEquation 0 v ↔ v ^ 2 = v := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  unfold InfinityChartEquation
  constructor <;> intro hv
  · linear_combination hv - v * htwo
  · linear_combination hv + v * htwo

def infinityPointEquivFixed :
    InfinityPoint K ≃ FixedTwo K where
  toFun P := ⟨P.1, (infinityChartEquation_zero_iff_fixed P.1).mp P.2⟩
  invFun P := ⟨P.1, (infinityChartEquation_zero_iff_fixed P.1).mpr P.2⟩
  left_inv P := by apply Subtype.ext; rfl
  right_inv P := by apply Subtype.ext; rfl

theorem infinityPoint_card [Finite K] :
    Nat.card (InfinityPoint K) = 2 := by
  rw [Nat.card_congr (infinityPointEquivFixed (K := K)), fixedTwo_card]

/-- The point type presented by the affine chart and its two infinity points. -/
abbrev CompletedPoint (K : Type u) [Field K] :=
  AffinePoint K ⊕ InfinityPoint K

theorem completedPoint_card [Finite K]
    (hfour : ∀ z : K, z ^ 4 = z) :
    Nat.card (CompletedPoint K) = 6 := by
  rw [Nat.card_sum, affinePoint_card hfour, infinityPoint_card]

/-- On every affine point, the second-coordinate derivative is one. -/
theorem affineDerivativeY_eq_one
    (hfour : ∀ z : K, z ^ 4 = z)
    {x y : K} (hp : AffineEquation x y) :
    affineDerivativeY x y = 1 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hx := (affineEquation_iff_fixed hfour x y).mp hp |>.1
  have hx3 : x ^ 3 = x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * x := by rw [hx]
      _ = x := by simpa [pow_two] using hx
  simp only [affineDerivativeY, h]
  linear_combination y * htwo + hx3 + x * htwo

/-- The two points at infinity are smooth in the `X=1` chart. -/
theorem infinityDerivativeV_zero_eq_one (v : K) :
    infinityDerivativeV 0 v = 1 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [infinityDerivativeV]
  linear_combination v * htwo

/-- The affine chart is geometrically smooth in characteristic two.  If the
`y`-derivative vanished, the curve equation would force `y=1`; the
`x`-derivative would then force `x=1`, contradicting `h(x)=0`. -/
theorem no_affine_singular_point (x y : K) :
    ¬(AffineEquation x y ∧
      affineDerivativeY x y = 0 ∧
      affineDerivativeXCharTwo x y = 0) := by
  rintro ⟨hp, hdy, hdx⟩
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hhzero : h x = 0 := by
    unfold affineDerivativeY at hdy
    linear_combination hdy - y * htwo
  have hx3 : x ^ 3 = x + 1 := by
    simp only [h] at hhzero
    linear_combination hhzero - (x + 1) * htwo
  have hx4 : x ^ 4 = x ^ 2 + x := by
    simp only [h] at hhzero
    linear_combination x * hhzero - (x ^ 2 + x) * htwo
  have hx5 : x ^ 5 = x ^ 2 + x + 1 := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ = x * (x ^ 2 + x) := by rw [hx4]
      _ = x ^ 3 + x ^ 2 := by ring
      _ = x ^ 2 + x + 1 := by rw [hx3]; ring
  have hrhs : rhs x = 1 := by
    simp only [rhs]
    rw [hx5, hx4]
    linear_combination (x ^ 2 + x) * htwo
  have hy2 : y ^ 2 = 1 := by
    unfold AffineEquation at hp
    rw [hhzero, zero_mul, add_zero, hrhs] at hp
    exact hp
  have hyplus_sq : (y + 1) ^ 2 = 0 := by
    linear_combination hy2 + (y + 1) * htwo
  have hyplus : y + 1 = 0 := by
    exact (sq_eq_zero_iff).mp hyplus_sq
  have hy : y = 1 := by
    linear_combination hyplus - htwo
  have hxplus : x + 1 = 0 := by
    unfold affineDerivativeXCharTwo at hdx
    rw [hy, hx4] at hdx
    linear_combination hdx - x ^ 2 * htwo
  have hx : x = 1 := by
    linear_combination hxplus - htwo
  subst x
  simp only [h] at hhzero
  have hone : (1 : K) = 0 := by
    linear_combination hhzero - htwo
  exact one_ne_zero hone

/-- On the hyperplane at infinity, a nonzero weighted point has `X ≠ 0`;
therefore the `X=1` chart covers all points missing from the affine chart. -/
theorem infinity_has_nonzero_X
    {X Y Z : K}
    (hp : WeightedEquation X Y Z)
    (hnonzero : X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0)
    (hZ : Z = 0) :
    X ≠ 0 := by
  intro hX
  subst X
  subst Z
  have hy2 : Y ^ 2 = 0 := by
    simpa [WeightedEquation] using hp
  have hY : Y = 0 := (sq_eq_zero_iff).mp hy2
  exact hnonzero.elim (fun hx => hx rfl)
    (fun hrest => hrest.elim (fun hy => hy hY) (fun hz => hz rfl))

/-! ## The fields `F₂` and `F₄` -/

abbrev F2 := ZMod 2
abbrev F4 := GaloisField 2 2

theorem f2_fourth_eq (x : F2) : x ^ 4 = x := by
  have hx : x ^ 2 = x := ZMod.pow_card x
  calc
    x ^ 4 = (x ^ 2) ^ 2 := by ring
    _ = x ^ 2 := congrArg (fun z : F2 => z ^ 2) hx
    _ = x := hx

local instance instFintypeF4 : Fintype F4 := Fintype.ofFinite F4

theorem f4_card : Fintype.card F4 = 4 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem f4_fourth_eq (x : F4) : x ^ 4 = x := by
  have hx := FiniteField.pow_card x
  rwa [f4_card] at hx

theorem completed_points_f2_card :
    Nat.card (CompletedPoint F2) = 6 :=
  completedPoint_card f2_fourth_eq

theorem completed_points_f4_card :
    Nat.card (CompletedPoint F4) = 6 :=
  completedPoint_card f4_fourth_eq

end

end MazurProof.N13GoodModelTwo


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/

open Polynomial

namespace MazurProof.N13GeneralizedMumfordIntegral

noncomputable section

universe u

variable {R : Type u} [CommRing R]

def hPoly : R[X] :=
  X ^ 3 + X + 1

def rhsPoly : R[X] :=
  X ^ 5 + X ^ 4

def curvePoly : R[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem curvePoly_monic : (curvePoly : R[X][X]).Monic := by
  unfold curvePoly
  monicity <;> norm_num

theorem curvePoly_natDegree [Nontrivial R] :
    (curvePoly : R[X][X]).natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num

abbrev CoordinateRing : Type u :=
  AdjoinRoot (curvePoly : R[X][X])

noncomputable instance instAlgebraCoordinateRing : Algebra R (CoordinateRing (R := R)) :=
  inferInstance

noncomputable instance instAlgebraPolynomialCoordinateRing : Algebra R[X] (CoordinateRing (R := R)) :=
  inferInstance

def mk : R[X][X] →+* CoordinateRing (R := R) :=
  AdjoinRoot.mk (curvePoly (R := R))

def xClass (p : R[X]) : CoordinateRing (R := R) :=
  mk (R := R) (C p)

def yClass : CoordinateRing (R := R) :=
  mk (R := R) X

def xClassHom : R[X] →+* CoordinateRing (R := R) :=
  AdjoinRoot.of (curvePoly (R := R))

@[simp] theorem xClassHom_apply (p : R[X]) :
    xClassHom p = xClass p := rfl

@[simp] theorem xClass_zero : xClass (0 : R[X]) = 0 :=
  map_zero xClassHom

@[simp] theorem xClass_one : xClass (1 : R[X]) = 1 :=
  map_one xClassHom

@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : R[X]) =
      (n : CoordinateRing (R := R)) :=
  map_natCast xClassHom n

@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q

@[simp] theorem xClass_sub (p q : R[X]) :
    xClass (p - q) = xClass p - xClass q :=
  map_sub xClassHom p q

@[simp] theorem xClass_neg (p : R[X]) :
    xClass (-p) = -xClass p :=
  map_neg xClassHom p

@[simp] theorem xClass_mul (p q : R[X]) :
    xClass (p * q) = xClass p * xClass q :=
  map_mul xClassHom p q

@[simp] theorem xClass_pow (p : R[X]) (n : ℕ) :
    xClass (p ^ n) = xClass p ^ n :=
  map_pow xClassHom p n

def normalPoly :
    CoordinateRing (R := R) →ₗ[R[X]] R[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic (R := R))

def coeff0 :
    CoordinateRing (R := R) →ₗ[R[X]] R[X] :=
  (Polynomial.lcoeff R[X] 0).comp (normalPoly (R := R))

def coeffY :
    CoordinateRing (R := R) →ₗ[R[X]] R[X] :=
  (Polynomial.lcoeff R[X] 1).comp (normalPoly (R := R))

private theorem curvePoly_degree [Nontrivial R] :
    (curvePoly : R[X][X]).degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X
    [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem recompose [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    xClass (coeff0 z) + xClass (coeffY z) * yClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass (coeff0 (mk g)) +
              xClass (coeffY (mk g)) * yClass =
            mk
              (C (coeff0 (mk g)) +
                C (coeffY (mk g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = mk (normalPoly (mk g)) := by
              rw [normalPoly_eq_C_add_C_mul_X]
        _ = mk g :=
          AdjoinRoot.mk_leftInverse curvePoly_monic (mk g)

@[simp] theorem coeff0_xClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)

@[simp] theorem coeffY_xClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)

@[simp] theorem coeff0_yClass [Nontrivial R] :
    coeff0 (yClass (R := R)) = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num

@[simp] theorem coeffY_yClass [Nontrivial R] :
    coeffY (yClass (R := R)) = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num

@[simp] theorem coeff0_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem coeffY_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = p
  rw [← Algebra.smul_def]
  simp

/-- Equality in the generalized affine coordinate ring is coefficientwise
with respect to the basis `1, Y` over `R[X]`. -/
theorem eq_iff_coeff [Nontrivial R]
    (z w : CoordinateRing (R := R)) :
    z = w ↔ coeff0 z = coeff0 w ∧ coeffY z = coeffY w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose z, ← recompose w, h0, hY]

/-- The generalized graph relation; no smoothness assumption is needed for
the evaluation-kernel and saturation theorems. -/
structure SemiMumford where
  u : R[X]
  v : R[X]
  w : R[X]
  u_monic : u.Monic
  curve_eq : v ^ 2 + hPoly * v - rhsPoly = u * w

/-- Hyperelliptic conjugation sends a graph value `v` to `-h-v`. -/
def conjugateV (v : R[X]) : R[X] :=
  -hPoly - v

def ySubClass (v : R[X]) : CoordinateRing (R := R) :=
  yClass - xClass v

def mumfordIdeal (u v : R[X]) :
    Ideal (CoordinateRing (R := R)) :=
  Ideal.span {xClass u, ySubClass v}

theorem xClass_mem_mumfordIdeal (u v : R[X]) :
    xClass u ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_mumfordIdeal (u v : R[X]) :
    ySubClass v ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

@[simp] theorem yClass_relation :
    yClass (R := R) ^ 2 +
        xClass (R := R) (hPoly (R := R)) *
          yClass (R := R) =
      xClass (R := R) (rhsPoly (R := R)) := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

/-- The product of the two raw graph functions is the negative substituted
curve equation.  No divisibility or smoothness hypothesis is needed. -/
theorem ySubClass_mul_conjugateV_raw
    (v : R[X]) :
    ySubClass v * ySubClass (conjugateV v) =
      -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
  calc
    ySubClass v * ySubClass (conjugateV v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass v ^ 2 + xClass hPoly * xClass v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (v ^ 2 + hPoly * v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
      rw [xClass_sub]
      ring

/-- The two conjugate graph functions multiply to the negative Cantor
quotient.  This identity is valid integrally, before reduction modulo two. -/
theorem ySubClass_mul_conjugate
    (D : SemiMumford (R := R)) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) :=
      ySubClass_mul_conjugateV_raw D.v
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]

/-- A smooth generalized Mumford graph and its hyperelliptic conjugate
multiply to the principal ideal `(u)`.  The only smoothness input is the
displayed Bézout identity, so the theorem works over an arbitrary
commutative base ring. -/
theorem mumfordIdeal_mul_conj_integral
    (D : SemiMumford (R := R))
    (hbez :
      ∃ a b c : R[X],
        a * D.u + b * (2 * D.v + hPoly) + c * D.w = 1) :
    mumfordIdeal D.u D.v *
        mumfordIdeal D.u (conjugateV D.v) =
      Ideal.span
        ({xClass D.u} :
          Set (CoordinateRing (R := R))) := by
  let I := mumfordIdeal D.u D.v
  let J := mumfordIdeal D.u (conjugateV D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine ⟨p₀ * q₀ * xClass D.u +
        p₀ * qY * ySubClass (conjugateV D.v) +
        pY * q₀ * ySubClass D.v -
        pY * qY * xClass D.w, ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination pY * qY * ySubClass_mul_conjugate D
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, habc⟩ := hbez
    have huI : xClass D.u ∈ I :=
      xClass_mem_mumfordIdeal D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hvI : ySubClass D.v ∈ I :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hvJ : ySubClass (conjugateV D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv :
        xClass D.u * xClass (2 * D.v + hPoly) ∈ I * J := by
      have hp :
          xClass D.u * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [two_mul, ySubClass, conjugateV, xClass_neg, xClass_sub,
        xClass_add]
      ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass D.v * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b *
          (xClass D.u * xClass (2 * D.v + hPoly)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b *
              (xClass D.u * xClass (2 * D.v + hPoly)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + hPoly) + c * D.w) := by
          simp only [two_mul, xClass_add, xClass_mul]
          ring
        _ = xClass D.u * 1 := by rw [habc, xClass_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum

abbrev MumfordResidue
    (D : SemiMumford (R := R)) : Type u :=
  R[X] ⧸ Ideal.span ({D.u} : Set R[X])

private theorem mumford_root_relation
    (D : SemiMumford (R := R)) :
    curvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v) = 0 := by
  change (X ^ 2 + C hPoly * X - C rhsPoly).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X]))
    (D.v ^ 2 + hPoly * D.v - rhsPoly) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩

def mumfordEval (D : SemiMumford (R := R)) :
    CoordinateRing (R := R) →+* MumfordResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v)
    (mumford_root_relation D)

@[simp] theorem mumfordEval_xClass
    (D : SemiMumford (R := R)) (p : R[X]) :
    mumfordEval D (xClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) p := by
  change mumfordEval D (AdjoinRoot.of curvePoly p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation D)

@[simp] theorem mumfordEval_yClass
    (D : SemiMumford (R := R)) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)

@[simp] theorem mumfordEval_ySubClass
    (D : SemiMumford (R := R)) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker
    (D : SemiMumford (R := R)) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D

theorem ker_mumfordEval
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : R[X] := coeff0 z
    let q : R[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass D.u ∈ mumfordIdeal D.u D.v :=
      xClass_mem_mumfordIdeal D.u D.v
    have hyv : ySubClass D.v ∈ mumfordIdeal D.u D.v :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hbase : xClass (p + q * D.v) ∈
        mumfordIdeal D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass s) hu
    have hgraph : xClass q * ySubClass D.v ∈
        mumfordIdeal D.u D.v :=
      Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass q) hyv
    rw [← recompose z]
    have hdecomp :
        xClass p + xClass q * yClass =
          xClass (p + q * D.v) +
            xClass q * ySubClass D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker D

/-- Membership in a generalized Mumford graph ideal is the single monic
divisibility condition obtained by substituting `Y = v`. -/
theorem mem_mumfordIdeal_iff
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    z ∈ mumfordIdeal D.u D.v ↔
      D.u ∣ coeff0 z + coeffY z * D.v := by
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  conv_lhs =>
    rw [← recompose z]
  simp only [map_add, map_mul, mumfordEval_xClass,
    mumfordEval_yClass]
  change
    Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X]))
        (coeff0 z + coeffY z * D.v) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem mumfordEval_surjective
    (D : SemiMumford (R := R)) :
    Function.Surjective (mumfordEval D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass p, mumfordEval_xClass D p⟩

noncomputable def mumfordQuotientEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))

/-- The graph quotient equivalence sends a quotient class to its graph
evaluation. -/
@[simp] theorem mumfordQuotientEquiv_apply_mk
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient algebra. -/
noncomputable def mumfordQuotientAlgEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[R]
      MumfordResidue D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv D)
    (by
      intro r
      change
        mumfordQuotientEquiv D
            (Ideal.Quotient.mk
              (mumfordIdeal D.u D.v) (xClass (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set R[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

/-- A monic graph quotient is free over the base. -/
noncomputable instance mumfordResidueFree
    (D : SemiMumford (R := R)) :
    Module.Free R (MumfordResidue D) :=
  D.u_monic.free_quotient

/-- A generalized Mumford graph ideal is saturated with respect to every
nonzero scalar from a domain base. -/
theorem scalar_saturated
    [IsDomain R]
    (D : SemiMumford (R := R))
    (r : R) (hr : r ≠ 0)
    (z : CoordinateRing (R := R))
    (hz : xClass (C r) * z ∈ mumfordIdeal D.u D.v) :
    z ∈ mumfordIdeal D.u D.v := by
  have hker :
      xClass (C r) * z ∈ RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval]
    exact hz
  have hmap :
      mumfordEval D (xClass (C r) * z) = 0 :=
    hker
  have hscalar :
      r • mumfordEval D z =
        Ideal.Quotient.mk
          (Ideal.span ({D.u} : Set R[X])) (C r) *
            mumfordEval D z := by
    obtain ⟨p, hp⟩ :=
      Ideal.Quotient.mk_surjective (mumfordEval D z)
    rw [← hp]
    change
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (r • p) =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (C r) *
          Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) p
    rw [Polynomial.smul_eq_C_mul]
    exact
      (Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))).map_mul (C r) p
  have hsmul : r • mumfordEval D z = 0 := by
    rw [hscalar]
    simpa only [map_mul, mumfordEval_xClass] using hmap
  have heval : mumfordEval D z = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hr
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  exact heval

namespace TwoAdic

abbrev R₂ : Type := ℤ_[2]

abbrev CoordinateRing₂ : Type :=
  CoordinateRing (R := R₂)

abbrev SemiMumford₂ : Type :=
  SemiMumford (R := R₂)

/-- In particular, integral graph ideals over `ℤ₂` are vertically
two-saturated. -/
theorem two_saturated
    (D : SemiMumford₂)
    (z : CoordinateRing₂)
    (hz :
      xClass (R := R₂) (C (2 : R₂)) * z ∈
        mumfordIdeal D.u D.v) :
    z ∈ mumfordIdeal D.u D.v :=
  scalar_saturated D 2 (by norm_num) z hz

end TwoAdic

end

end MazurProof.N13GeneralizedMumfordIntegral


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.N13GoodCoordinateRingTwo

noncomputable section

abbrev K := N13GoodModelTwo.F2

/-- The coefficient of `Y` in polynomial form. -/
def hPoly : K[X] :=
  X ^ 3 + X + 1

/-- The right-hand side in polynomial form. -/
def rhsPoly : K[X] :=
  X ^ 5 + X ^ 4

/-- The outer variable is `Y`, with coefficients in `F₂[X]`. -/
def curvePoly : K[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem hPoly_monic : hPoly.Monic := by
  unfold hPoly
  (monicity; norm_num)

theorem hPoly_natDegree : hPoly.natDegree = 3 := by
  unfold hPoly
  (compute_degree; norm_num)

theorem rhsPoly_monic : rhsPoly.Monic := by
  unfold rhsPoly
  monicity <;> norm_num

theorem rhsPoly_natDegree : rhsPoly.natDegree = 5 := by
  unfold rhsPoly
  compute_degree <;> norm_num

theorem curvePoly_monic : curvePoly.Monic := by
  unfold curvePoly
  monicity <;> norm_num

theorem curvePoly_natDegree : curvePoly.natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num

private theorem zmod_two_nonzero_eq_one (z : K) (hz : z ≠ 0) :
    z = 1 := by
  simpa [K] using ZMod.pow_card_sub_one_eq_one hz

private theorem artinSchreier_degree_le_three
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    q.natDegree ≤ 3 := by
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    have : (rhsPoly : K[X]) = 0 := by simpa using heq.symm
    exact rhsPoly_monic.ne_zero this
  by_contra hdeg
  have h4 : 4 ≤ q.natDegree := by omega
  have hlt :
      (hPoly * q).natDegree < (q ^ 2).natDegree := by
    rw [natDegree_mul hPoly_monic.ne_zero hq0, hPoly_natDegree,
      natDegree_pow]
    omega
  have hsum :
      (q ^ 2 + hPoly * q).natDegree = (q ^ 2).natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hlt
  rw [heq, rhsPoly_natDegree, natDegree_pow] at hsum
  omega

private theorem artinSchreier_reduce_degree
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    ∃ r : K[X],
      r.natDegree ≤ 2 ∧
      r ^ 2 + hPoly * r = rhsPoly := by
  have hdeg := artinSchreier_degree_le_three q heq
  by_cases hq3 : q.natDegree = 3
  · have hq0 : q ≠ 0 := by
      intro hq
      subst q
      norm_num at hq3
    have hlead : q.leadingCoeff = 1 :=
      zmod_two_nonzero_eq_one q.leadingCoeff
        (leadingCoeff_ne_zero.mpr hq0)
    have hqMonic : q.Monic := hlead
    have hqDegree : IsMonicOfDegree q 3 := ⟨hq3, hqMonic⟩
    have hhDegree : IsMonicOfDegree hPoly 3 :=
      ⟨hPoly_natDegree, hPoly_monic⟩
    refine ⟨q - hPoly, ?_, ?_⟩
    · have hlt :
          (q - hPoly).natDegree < 3 :=
        hqDegree.natDegree_sub_lt (n := 3) (by norm_num) hhDegree
      omega
    · have htwo : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      calc
        (q - hPoly) ^ 2 + hPoly * (q - hPoly) =
            q ^ 2 + hPoly * q - 2 * (q * hPoly) := by ring
        _ = q ^ 2 + hPoly * q := by rw [htwo, zero_mul, sub_zero]
        _ = rhsPoly := heq
  · refine ⟨q, ?_, heq⟩
    omega

private theorem no_artinSchreier_polynomial_root
    (q : K[X]) :
    q ^ 2 + hPoly * q ≠ rhsPoly := by
  intro heq
  obtain ⟨r, hrdeg, hre⟩ := artinSchreier_reduce_degree q heq
  have hr :
      r =
        C (r.coeff 2) * X ^ 2 +
          C (r.coeff 1) * X +
            C (r.coeff 0) := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n = 1
    · subst n
      simp
    by_cases hn2 : n = 2
    · subst n
      simp
    have hn : 2 < n := by omega
    have hrzero : r.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (hrdeg.trans_lt hn)
    have h1n : 1 ≠ n := by omega
    rw [hrzero]
    simp [coeff_X, coeff_C, hn0, h1n, hn2]
  rw [hr] at hre
  simp only [hPoly, rhsPoly] at hre
  ring_nf at hre
  have hcoeffFive :=
    congrArg (fun p : K[X] => p.coeff 5) hre
  have hcoeffTwo :=
    congrArg (fun p : K[X] => p.coeff 2) hre
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  simp only [← C_pow] at hcoeffFive hcoeffTwo
  simp [coeff_add, coeff_C_mul, coeff_mul_C, coeff_X_pow, htwoK] at hcoeffFive hcoeffTwo
  have hbb : r.coeff 1 + r.coeff 1 = 0 := by
    rw [← two_mul, htwoK, zero_mul]
  have hzero : r.coeff 2 = 0 := by
    linear_combination hcoeffTwo - hbb
  rw [hzero] at hcoeffFive
  exact zero_ne_one hcoeffFive

private theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot curvePoly q := by
  intro hq
  have heq :
      q ^ 2 + hPoly * q = rhsPoly := by
    have hzero :
        q ^ 2 + hPoly * q - rhsPoly = 0 := by
      simpa only [IsRoot.def, curvePoly, eval_sub, eval_add, eval_pow,
        eval_X, eval_C, eval_mul] using hq
    exact sub_eq_zero.mp hzero
  exact no_artinSchreier_polynomial_root q heq

theorem curvePoly_irreducible : Irreducible curvePoly := by
  rw [curvePoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot q
      ((mem_roots curvePoly_monic.ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]

instance curvePolyIrreducibleFact : Fact (Irreducible curvePoly) :=
  ⟨curvePoly_irreducible⟩

/-- The affine coordinate ring of the special fibre. -/
abbrev CoordinateRing : Type :=
  AdjoinRoot curvePoly

/-- Its fraction field. -/
abbrev FunctionField : Type :=
  FractionRing CoordinateRing

instance instIsDomainCoordinateRing : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime curvePoly_irreducible.prime

noncomputable instance instAlgebraKCoordinateRing : Algebra K CoordinateRing :=
  inferInstance

noncomputable instance instAlgebraPolynomialKCoordinateRing : Algebra K[X] CoordinateRing :=
  inferInstance

/-- Quotient map to the affine coordinate ring. -/
def mk : K[X][X] →+* CoordinateRing :=
  AdjoinRoot.mk curvePoly

/-- Embed a polynomial in the `X` coordinate. -/
def xClass (p : K[X]) : CoordinateRing :=
  mk (C p)

/-- The class of the `Y` coordinate. -/
def yClass : CoordinateRing :=
  mk X

/-- The polynomial-coordinate embedding. -/
def xClassHom : K[X] →+* CoordinateRing :=
  AdjoinRoot.of curvePoly

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom p = xClass p := rfl

@[simp] theorem xClass_zero : xClass 0 = 0 :=
  map_zero xClassHom

@[simp] theorem xClass_one : xClass 1 = 1 :=
  map_one xClassHom

@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : K[X]) = (n : CoordinateRing) :=
  map_natCast xClassHom n

@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass (p - q) = xClass p - xClass q :=
  map_sub xClassHom p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass (-p) = -xClass p :=
  map_neg xClassHom p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass (p * q) = xClass p * xClass q :=
  map_mul xClassHom p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass (p ^ n) = xClass p ^ n :=
  map_pow xClassHom p n

/-- The canonical degree-less-than-two polynomial representative. -/
def normalPoly : CoordinateRing →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom curvePoly_monic

/-- Constant coefficient in the `1,Y` basis. -/
def coeff0 : CoordinateRing →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp normalPoly

/-- `Y` coefficient in the `1,Y` basis. -/
def coeffY : CoordinateRing →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp normalPoly

@[simp] theorem normalPoly_mk (g : K[X][X]) :
    normalPoly (mk g) = g %ₘ curvePoly := rfl

@[simp] theorem coeff0_mk (g : K[X][X]) :
    coeff0 (mk g) = (g %ₘ curvePoly).coeff 0 := rfl

@[simp] theorem coeffY_mk (g : K[X][X]) :
    coeffY (mk g) = (g %ₘ curvePoly).coeff 1 := rfl

private theorem curvePoly_degree : curvePoly.degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

/-- Every coordinate-ring element has a unique rank-two expression. -/
theorem recompose (z : CoordinateRing) :
    xClass (coeff0 z) + xClass (coeffY z) * yClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass (coeff0 (mk g)) +
              xClass (coeffY (mk g)) * yClass =
            mk
              (C (coeff0 (mk g)) +
                C (coeffY (mk g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = mk (normalPoly (mk g)) := by
              rw [normalPoly_eq_C_add_C_mul_X]
        _ = mk g :=
          AdjoinRoot.mk_leftInverse curvePoly_monic (mk g)

@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)

@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)

@[simp] theorem coeff0_yClass :
    coeff0 yClass = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num

@[simp] theorem coeffY_yClass :
    coeffY yClass = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num

@[simp] theorem coeff0_xClass_mul_yClass (p : K[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0 ((algebraMap K[X] CoordinateRing p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem coeffY_xClass_mul_yClass (p : K[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY ((algebraMap K[X] CoordinateRing p) * yClass) = p
  rw [← Algebra.smul_def]
  simp

/-- Equality in the special-fibre coordinate ring is coefficientwise in
the rank-two basis `1,Y`. -/
theorem eq_iff_coeff (z w : CoordinateRing) :
    z = w ↔ coeff0 z = coeff0 w ∧ coeffY z = coeffY w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose z, ← recompose w, h0, hY]

@[simp] theorem yClass_relation :
    yClass ^ 2 + xClass hPoly * yClass = xClass rhsPoly := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt curvePoly_monic
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)

/-! ## Generalized Mumford graph ideals -/

/-- Hyperelliptic conjugation sends a graph value `v` to `-h-v`. -/
def conjugateV (v : K[X]) : K[X] :=
  -hPoly - v

/-- Integral generalized Mumford data, including the Cantor quotient and
the precise smoothness Bézout identity needed for ideal invertibility. -/
structure SemiMumford where
  u : K[X]
  v : K[X]
  w : K[X]
  u_monic : u.Monic
  curve_eq : v ^ 2 + hPoly * v - rhsPoly = u * w
  bezout :
    ∃ a b c : K[X],
      a * u + b * (2 * v + hPoly) + c * w = 1

/-- The graph function `Y-v(X)`. -/
def ySubClass (v : K[X]) : CoordinateRing :=
  yClass - xClass v

/-- The integral graph ideal `(u,Y-v)`. -/
def mumfordIdeal (u v : K[X]) : Ideal CoordinateRing :=
  Ideal.span {xClass u, ySubClass v}

theorem xClass_mem_mumfordIdeal (u v : K[X]) :
    xClass u ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass v ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

/-! ## Evaluation at a generalized Mumford graph -/

abbrev MumfordResidue (D : SemiMumford) : Type :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])

private theorem mumford_root_relation (D : SemiMumford) :
    curvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 + C hPoly * X - C rhsPoly).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 + hPoly * D.v - rhsPoly) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩

/-- Evaluation `X ↦ X mod u`, `Y ↦ v mod u`. -/
def mumfordEval (D : SemiMumford) :
    CoordinateRing →+* MumfordResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation D)

@[simp] theorem mumfordEval_xClass
    (D : SemiMumford) (p : K[X]) :
    mumfordEval D (xClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval D (AdjoinRoot.of curvePoly p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation D)

@[simp] theorem mumfordEval_yClass (D : SemiMumford) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)

@[simp] theorem mumfordEval_ySubClass (D : SemiMumford) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker (D : SemiMumford) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D

/-- The generalized Mumford graph ideal is exactly the evaluation kernel. -/
theorem ker_mumfordEval (D : SemiMumford) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 z
    let q : K[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set K[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass D.u ∈ mumfordIdeal D.u D.v :=
      xClass_mem_mumfordIdeal D.u D.v
    have hyv : ySubClass D.v ∈ mumfordIdeal D.u D.v :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hbase : xClass (p + q * D.v) ∈
        mumfordIdeal D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass s) hu
    have hgraph : xClass q * ySubClass D.v ∈
        mumfordIdeal D.u D.v :=
      Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass q) hyv
    rw [← recompose z]
    have hdecomp :
        xClass p + xClass q * yClass =
          xClass (p + q * D.v) +
            xClass q * ySubClass D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker D

theorem mumfordEval_surjective (D : SemiMumford) :
    Function.Surjective (mumfordEval D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass p, mumfordEval_xClass D p⟩

/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))

@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford) (z : CoordinateRing) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[K]
      MumfordResidue D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv D)
    (by
      intro r
      change
        mumfordQuotientEquiv D
            (Ideal.Quotient.mk
              (mumfordIdeal D.u D.v) (xClass (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

/-- The two graph generators multiply to the negative Cantor quotient. -/
theorem ySubClass_mul_conjugate (D : SemiMumford) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass D.v ^ 2 + xClass hPoly * xClass D.v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (D.v ^ 2 + hPoly * D.v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) := by
      rw [xClass_sub]
      ring
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]

/-- The characteristic-two generalized graph ideal satisfies
`(u,Y-v)(u,Y+h+v)=(u)`. -/
theorem mumfordIdeal_mul_conj_integral (D : SemiMumford) :
    mumfordIdeal D.u D.v * mumfordIdeal D.u (conjugateV D.v) =
      Ideal.span ({xClass D.u} : Set CoordinateRing) := by
  let I := mumfordIdeal D.u D.v
  let J := mumfordIdeal D.u (conjugateV D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine ⟨p₀ * q₀ * xClass D.u +
        p₀ * qY * ySubClass (conjugateV D.v) +
        pY * q₀ * ySubClass D.v -
        pY * qY * xClass D.w, ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination pY * qY * ySubClass_mul_conjugate D
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := D.bezout
    have huI : xClass D.u ∈ I :=
      xClass_mem_mumfordIdeal D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hvI : ySubClass D.v ∈ I :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hvJ : ySubClass (conjugateV D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv :
        xClass D.u * xClass (2 * D.v + hPoly) ∈ I * J := by
      have hp :
          xClass D.u * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub,
        xClass_add, xClass_mul]
      have htwoPoly : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      have htwoCoord : (2 : CoordinateRing) = 0 := by
        calc
          (2 : CoordinateRing) = xClass (2 : K[X]) :=
            (xClass_natCast 2).symm
          _ = xClass 0 := by rw [htwoPoly]
          _ = 0 := xClass_zero
      rw [htwoPoly, xClass_zero, zero_mul, zero_add]
      have hvadd : xClass D.v + xClass D.v = 0 := by
        rw [← two_mul, htwoCoord, zero_mul]
      calc
        xClass D.u * xClass hPoly =
            xClass D.u * xClass hPoly +
              xClass D.u * (xClass D.v + xClass D.v) := by
          rw [hvadd, mul_zero, add_zero]
        _ = xClass D.u *
              (yClass - (-xClass hPoly - xClass D.v)) -
            (yClass - xClass D.v) * xClass D.u := by ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass D.v * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b *
          (xClass D.u * xClass (2 * D.v + hPoly)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b *
              (xClass D.u * xClass (2 * D.v + hPoly)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + hPoly) + c * D.w) := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = xClass D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford) :
    (mumfordIdeal D.u D.v :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) =
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

/-- Invertible fractional ideals of the special affine coordinate ring. -/
abbrev InvFrac :=
  (FractionalIdeal CoordinateRing⁰ FunctionField)ˣ

/-- A generalized Mumford graph ideal as a unit fractional ideal. -/
def mumfordIdealUnit (D : SemiMumford) : InvFrac :=
  Units.mkOfMulEqOne
    (mumfordIdeal D.u D.v :
      FractionalIdeal CoordinateRing⁰ FunctionField)
    ((mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField)⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        FunctionField (xClass_ne_zero D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford) :
    (mumfordIdealUnit D :
      FractionalIdeal CoordinateRing⁰ FunctionField) =
      mumfordIdeal D.u D.v := rfl

end

end MazurProof.N13GoodCoordinateRingTwo


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Reduction of integral N13 Mumford graphs at two

The good integral equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

has the same coefficients after reduction from `ℤ₂` to `𝔽₂`.  Hence
coefficientwise reduction induces a canonical ring homomorphism between
the two affine coordinate rings.  This file proves that the homomorphism
preserves both coordinates and carries every generalized Mumford graph
ideal exactly to the corresponding special-fibre graph ideal.
-/

open Polynomial

namespace MazurProof.N13GeneralizedMumfordReduction

noncomputable section

abbrev R₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.R₂

abbrev K : Type :=
  N13GoodCoordinateRingTwo.K

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev SpecialRing : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- Coefficient reduction from the two-adic integers to `𝔽₂`. -/
def reduceBase : R₂ →+* K :=
  PadicInt.toZMod

/-- Coefficientwise reduction of polynomials in the `X` coordinate. -/
def reducePoly : R₂[X] →+* K[X] :=
  Polynomial.mapRingHom reduceBase

@[simp] theorem reducePoly_apply (p : R₂[X]) :
    reducePoly p = p.map reduceBase := rfl

@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  rw [← RingHom.mem_ker, reduceBase, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)

@[simp] theorem reduce_hPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.hPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodCoordinateRingTwo.hPoly]

@[simp] theorem reduce_rhsPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.rhsPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.rhsPoly,
    N13GoodCoordinateRingTwo.rhsPoly]

theorem reduce_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly =
      N13GoodCoordinateRingTwo.curvePoly := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    N13GoodCoordinateRingTwo.curvePoly, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (reducePoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (reducePoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 + C N13GoodCoordinateRingTwo.hPoly * X -
        C N13GoodCoordinateRingTwo.rhsPoly
  rw [reduce_hPoly, reduce_rhsPoly]

private theorem special_curve_dvd :
    N13GoodCoordinateRingTwo.curvePoly ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly := by
  rw [reduce_curvePoly]

/-- Reduction on the affine coordinate ring of the good equation. -/
def reduceCoordinate : IntegralRing →+* SpecialRing :=
  AdjoinRoot.map reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_xClass (p : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GoodCoordinateRingTwo.xClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd p

@[simp] theorem reduce_yClass :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GoodCoordinateRingTwo.yClass := by
  exact AdjoinRoot.map_root
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_ySubClass (v : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GoodCoordinateRingTwo.ySubClass (reducePoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass,
    N13GoodCoordinateRingTwo.ySubClass]

/-- Coefficientwise reduction of polynomials is onto. -/
theorem reducePoly_surjective :
    Function.Surjective reducePoly :=
  Polynomial.map_surjective
    reduceBase
    (ZMod.ringHom_surjective PadicInt.toZMod)

/-- The integral good-model coordinate ring reduces onto its special fibre.
This follows from the common rank-two normal form, not from a presentation
calculation in the quotient. -/
theorem reduceCoordinate_surjective :
    Function.Surjective reduceCoordinate := by
  intro z
  obtain ⟨p, hp⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeff0 z)
  obtain ⟨q, hq⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeffY z)
  refine ⟨
    N13GeneralizedMumfordIntegral.xClass p +
      N13GeneralizedMumfordIntegral.xClass q *
        N13GeneralizedMumfordIntegral.yClass,
    ?_⟩
  simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
    hp, hq]
  exact N13GoodCoordinateRingTwo.recompose z

@[simp] theorem reduce_coeff0 (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeff0 z) := by
  calc
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeff0
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeff0_xClass,
        N13GoodCoordinateRingTwo.coeff0_xClass_mul_yClass,
        add_zero]

@[simp] theorem reduce_coeffY (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeffY z) := by
  calc
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeffY
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeffY_xClass,
        N13GoodCoordinateRingTwo.coeffY_xClass_mul_yClass,
        zero_add]

private theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
    (p : R₂[X]) (hp : reducePoly p = 0) :
    ∃ q : R₂[X], p = C (2 : R₂) * q := by
  have hmem :
      p ∈ RingHom.ker reducePoly :=
    RingHom.mem_ker.mpr hp
  rw [reducePoly, Polynomial.ker_mapRingHom, reduceBase,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  exact hmem

/-- Reduction has exactly the vertical principal ideal `(2)` as kernel.
The proof combines the rank-two normal form with the polynomial-map kernel
theorem and the standard description of the maximal ideal of `ℤ₂`. -/
theorem ker_reduceCoordinate :
    RingHom.ker reduceCoordinate =
      Ideal.span
        ({algebraMap R₂ IntegralRing (2 : R₂)} :
          Set IntegralRing) := by
  apply le_antisymm
  · intro z hz
    have hz0 : reduceCoordinate z = 0 :=
      RingHom.mem_ker.mp hz
    have h0 :
        reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) = 0 := by
      rw [← reduce_coeff0 z, hz0]
      simp
    have hY :
        reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) = 0 := by
      rw [← reduce_coeffY z, hz0]
      simp
    obtain ⟨p, hp⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ h0
    obtain ⟨q, hq⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ hY
    rw [Ideal.mem_span_singleton]
    refine ⟨
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass,
      ?_⟩
    rw [← N13GeneralizedMumfordIntegral.recompose z, hp, hq]
    calc
      N13GeneralizedMumfordIntegral.xClass (C 2 * p) +
          N13GeneralizedMumfordIntegral.xClass (C 2 * q) *
            N13GeneralizedMumfordIntegral.yClass =
        N13GeneralizedMumfordIntegral.xClass (C 2) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := by
          simp only [mul_add,
            N13GeneralizedMumfordIntegral.xClass_mul]
          ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      algebraMap R₂ IntegralRing (2 : R₂) ∈
        RingHom.ker reduceCoordinate
    rw [RingHom.mem_ker]
    change reduceCoordinate
      (N13GeneralizedMumfordIntegral.xClass (C (2 : R₂))) = 0
    rw [reduce_xClass]
    simp [reducePoly]

/-- Reduction carries the integral graph ideal onto, rather than merely
into, the graph ideal with reduced coefficients. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reducePoly u) (reducePoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GoodCoordinateRingTwo.mumfordIdeal, Ideal.map_span,
    Set.image_pair, reduce_xClass, reduce_ySubClass]

/-- Integral generalized Mumford data carrying the smoothness Bézout
identity.  This is precisely the extra condition needed for the reduced
graph ideal to be invertible. -/
structure SmoothMumford₂ : Type
    extends
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂ where
  bezout :
    ∃ a b c : R₂[X],
      a * u + b * (2 * v +
        N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
          c * w = 1

/-- The integral graph ideal of smooth two-adic Mumford data has the
expected explicit inverse numerator: its product with the conjugate graph
ideal is the principal ideal `(u)`. -/
theorem integral_mumfordIdeal_mul_conj
    (D : SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v *
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u
          (N13GeneralizedMumfordIntegral.conjugateV D.v) =
      Ideal.span
        ({N13GeneralizedMumfordIntegral.xClass D.u} :
          Set IntegralRing) :=
  N13GeneralizedMumfordIntegral.mumfordIdeal_mul_conj_integral
    D.toSemiMumford D.bezout

/-- Hyperelliptic conjugation commutes with coefficient reduction. -/
theorem reduce_conjugateV
    (v : R₂[X]) :
    reducePoly
        (N13GeneralizedMumfordIntegral.conjugateV v) =
      N13GoodCoordinateRingTwo.conjugateV
        (reducePoly v) := by
  unfold N13GeneralizedMumfordIntegral.conjugateV
    N13GoodCoordinateRingTwo.conjugateV
  rw [map_sub, map_neg, reduce_hPoly]

/-- Smooth integral Mumford data reduce to the already constructed smooth
special-fibre data. -/
def reduceSmoothMumford
    (D : SmoothMumford₂) :
    N13GoodCoordinateRingTwo.SemiMumford where
  u := reducePoly D.u
  v := reducePoly D.v
  w := reducePoly D.w
  u_monic := D.u_monic.map reduceBase
  curve_eq := by
    have h := congrArg reducePoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      reduce_hPoly, reduce_rhsPoly] using h
  bezout := by
    obtain ⟨a, b, c, habc⟩ := D.bezout
    refine ⟨reducePoly a, reducePoly b, reducePoly c, ?_⟩
    have h := congrArg reducePoly habc
    simpa only [map_add, map_mul, map_ofNat, map_one,
      reduce_hPoly] using h

@[simp] theorem reduceSmoothMumford_u
    (D : SmoothMumford₂) :
    (reduceSmoothMumford D).u = reducePoly D.u := rfl

@[simp] theorem reduceSmoothMumford_v
    (D : SmoothMumford₂) :
    (reduceSmoothMumford D).v = reducePoly D.v := rfl

/-- The exact ideal reduction theorem, now stated for smooth integral data. -/
theorem map_smoothMumfordIdeal
    (D : SmoothMumford₂) :
    Ideal.map reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reduceSmoothMumford D).u
        (reduceSmoothMumford D).v := by
  simpa using map_mumfordIdeal D.u D.v

/-- Consequently the reduced graph ideal is represented by the canonical
unit fractional ideal on the special fibre. -/
def reducedIdealUnit
    (D : SmoothMumford₂) :
    N13GoodCoordinateRingTwo.InvFrac :=
  N13GoodCoordinateRingTwo.mumfordIdealUnit
    (reduceSmoothMumford D)

@[simp] theorem coe_reducedIdealUnit
    (D : SmoothMumford₂) :
    (reducedIdealUnit D :
      FractionalIdeal (nonZeroDivisors SpecialRing)
        N13GoodCoordinateRingTwo.FunctionField) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reducePoly D.u) (reducePoly D.v) := by
  exact N13GoodCoordinateRingTwo.coe_mumfordIdealUnit
    (reduceSmoothMumford D)

end

end MazurProof.N13GeneralizedMumfordReduction


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Completing the square on the N13 coordinate rings

Over any field of characteristic zero, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/

open Polynomial

namespace MazurProof.N13GoodSexticCoordinateEquiv

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

abbrev M : SexticMumford.Model K :=
  N13Mumford.model K

abbrev GoodRing : Type u :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := K)

abbrev SexticRing : Type u :=
  N13Mumford.CoordinateRing K

def goodXHom : K[X] →+* GoodRing (K := K) :=
  N13GeneralizedMumfordIntegral.xClassHom

def sexticXHom : K[X] →+* SexticRing (K := K) :=
  AdjoinRoot.of (SexticMumford.curvePoly (M (K := K)))

@[simp] theorem goodXHom_apply (p : K[X]) :
    goodXHom (K := K) p =
      N13GeneralizedMumfordIntegral.xClass p := rfl

@[simp] theorem sexticXHom_apply (p : K[X]) :
    sexticXHom (K := K) p =
      SexticMumford.xClass (M (K := K)) p := rfl

abbrev hPoly : K[X] :=
  N13GeneralizedMumfordIntegral.hPoly

abbrev rhsPoly : K[X] :=
  N13GeneralizedMumfordIntegral.rhsPoly

/-- The polynomial identity behind completion of the square. -/
theorem sextic_eq_h_sq_add_four_rhs :
    N13Mumford.f K = hPoly ^ 2 + 4 * rhsPoly := by
  simp only [N13Mumford.f, hPoly, rhsPoly,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly]
  ring

/-- The good `y` coordinate inside the sextic coordinate ring. -/
def goodYInSextic : SexticRing (K := K) :=
  (1 / 2 : K) •
    (SexticMumford.yClass (M (K := K)) -
      sexticXHom (K := K) hPoly)

/-- The sextic `Y` coordinate inside the good coordinate ring. -/
def sexticYInGood : GoodRing (K := K) :=
  2 * N13GeneralizedMumfordIntegral.yClass +
    goodXHom (K := K) hPoly

private theorem goodYInSextic_root :
    (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂
      (sexticXHom (K := K)) (goodYInSextic (K := K)) = 0 := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  have hy := SexticMumford.yClass_sq (M (K := K))
  change
    SexticMumford.yClass (M (K := K)) ^ 2 =
      sexticXHom (K := K) (N13Mumford.f K) at hy
  rw [sextic_eq_h_sq_add_four_rhs (K := K)] at hy
  simp only [map_add, map_mul, map_pow, map_ofNat] at hy
  let a : SexticRing (K := K) :=
    (algebraMap K (SexticRing (K := K))) (1 / 2)
  let Y : SexticRing (K := K) :=
    SexticMumford.yClass (M (K := K))
  let H : SexticRing (K := K) :=
    sexticXHom (K := K) (hPoly (K := K))
  let R : SexticRing (K := K) :=
    sexticXHom (K := K) (rhsPoly (K := K))
  simp only [goodYInSextic, Algebra.smul_def]
  change (a * (Y - H)) ^ 2 + H * (a * (Y - H)) - R = 0
  have hy' : Y ^ 2 = H ^ 2 + 4 * R := hy
  have ha : 2 * a = 1 := by
    dsimp only [a]
    rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
      ← map_mul]
    norm_num
  linear_combination
    a ^ 2 * hy' +
      (-a * Y * H + a * H ^ 2 + (2 * a + 1) * R) * ha

private theorem good_root_relation :
    N13GeneralizedMumfordIntegral.yClass ^ 2 +
        goodXHom (K := K) (hPoly (K := K)) *
          N13GeneralizedMumfordIntegral.yClass -
      goodXHom (K := K) (rhsPoly (K := K)) = 0 := by
  apply sub_eq_zero.mpr
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13GeneralizedMumfordIntegral.curvePoly]
  ring

private theorem sexticYInGood_root :
    (SexticMumford.curvePoly (M (K := K))).eval₂
      (goodXHom (K := K)) (sexticYInGood (K := K)) = 0 := by
  simp only [SexticMumford.curvePoly,
    eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change
    sexticYInGood (K := K) ^ 2 -
      goodXHom (K := K) (N13Mumford.f K) = 0
  rw [sextic_eq_h_sq_add_four_rhs (K := K)]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  unfold sexticYInGood
  linear_combination 4 * good_root_relation (K := K)

/-- Completion of the square as a ring homomorphism from the good model to
the sextic model. -/
def toSextic :
    GoodRing (K := K) →+* SexticRing (K := K) :=
  AdjoinRoot.lift (sexticXHom (K := K))
    (goodYInSextic (K := K))
    (goodYInSextic_root (K := K))

/-- The inverse change of variables. -/
def toGood :
    SexticRing (K := K) →+* GoodRing (K := K) :=
  AdjoinRoot.lift (goodXHom (K := K))
    (sexticYInGood (K := K))
    (sexticYInGood_root (K := K))

@[simp] theorem toSextic_xClass (p : K[X]) :
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass (M (K := K)) p := by
  change
    toSextic (K := K)
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := K)) p) =
      sexticXHom (K := K) p
  exact AdjoinRoot.lift_of (goodYInSextic_root (K := K))

@[simp] theorem toSextic_algebraMap (z : K) :
    toSextic (K := K)
        (algebraMap K (GoodRing (K := K)) z) =
      algebraMap K (SexticRing (K := K)) z := by
  change
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass (C z)) =
      SexticMumford.xClass (M (K := K)) (C z)
  exact toSextic_xClass (K := K) (C z)

@[simp] theorem toSextic_yClass :
    toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  AdjoinRoot.lift_root (goodYInSextic_root (K := K))

@[simp] theorem toGood_xClass (p : K[X]) :
    toGood (K := K) (SexticMumford.xClass (M (K := K)) p) =
      N13GeneralizedMumfordIntegral.xClass p := by
  change
    toGood (K := K)
        (AdjoinRoot.of
          (SexticMumford.curvePoly (M (K := K))) p) =
      goodXHom (K := K) p
  exact AdjoinRoot.lift_of (sexticYInGood_root (K := K))

@[simp] theorem toGood_algebraMap (z : K) :
    toGood (K := K)
        (algebraMap K (SexticRing (K := K)) z) =
      algebraMap K (GoodRing (K := K)) z := by
  change
    toGood (K := K)
        (SexticMumford.xClass (M (K := K)) (C z)) =
      N13GeneralizedMumfordIntegral.xClass (C z)
  exact toGood_xClass (K := K) (C z)

@[simp] theorem toGood_yClass :
    toGood (K := K) (SexticMumford.yClass (M (K := K))) =
      sexticYInGood (K := K) :=
  AdjoinRoot.lift_root (sexticYInGood_root (K := K))

private theorem invTwo_mul_two_good :
    (algebraMap K (GoodRing (K := K))) (2 : K)⁻¹ *
        (2 : GoodRing (K := K)) = 1 := by
  rw [← map_ofNat
      (algebraMap K (GoodRing (K := K))) 2,
    ← map_mul]
  norm_num

private theorem two_mul_invTwo_sextic :
    (2 : SexticRing (K := K)) *
        (algebraMap K (SexticRing (K := K))) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
    ← map_mul]
  norm_num

private theorem toGood_comp_toSextic :
    (toGood (K := K)).comp (toSextic (K := K)) =
      RingHom.id (GoodRing (K := K)) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toGood (K := K)
          (toSextic (K := K) (goodXHom (K := K) p)) =
        goodXHom (K := K) p
    rw [goodXHom_apply, toSextic_xClass, toGood_xClass]
  · change
      toGood (K := K) (toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass) =
          N13GeneralizedMumfordIntegral.yClass
    rw [toSextic_yClass (K := K)]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [← mul_assoc, invTwo_mul_two_good (K := K), one_mul]

private theorem toSextic_comp_toGood :
    (toSextic (K := K)).comp (toGood (K := K)) =
      RingHom.id (SexticRing (K := K)) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toSextic (K := K)
          (toGood (K := K) (sexticXHom (K := K) p)) =
        sexticXHom (K := K) p
    rw [sexticXHom_apply, toGood_xClass, toSextic_xClass]
  · change
      toSextic (K := K)
          (toGood (K := K)
            (SexticMumford.yClass (M (K := K)))) =
        SexticMumford.yClass (M (K := K))
    rw [toGood_yClass (K := K)]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [map_ofNat, ← mul_assoc,
      two_mul_invTwo_sextic (K := K)]
    ring

/-- The coordinate-ring isomorphism induced by completion of the square. -/
def coordinateRingEquiv :
    GoodRing (K := K) ≃+* SexticRing (K := K) where
  toFun := toSextic (K := K)
  invFun := toGood (K := K)
  left_inv z := by
    have h :=
      DFunLike.congr_fun (toGood_comp_toSextic (K := K)) z
    simpa using h
  right_inv z := by
    have h :=
      DFunLike.congr_fun (toSextic_comp_toGood (K := K)) z
    simpa using h
  map_mul' := map_mul (toSextic (K := K))
  map_add' := map_add (toSextic (K := K))

@[simp] theorem coordinateRingEquiv_xClass (p : K[X]) :
    coordinateRingEquiv (K := K)
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass (M (K := K)) p :=
  toSextic_xClass (K := K) p

@[simp] theorem coordinateRingEquiv_yClass :
    coordinateRingEquiv (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  toSextic_yClass (K := K)

end

end MazurProof.N13GoodSexticCoordinateEquiv


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Transporting N13 Mumford graph ideals through completion of the square

The rational change of coordinates

`Y = 2y + (X³ + X + 1)`

does more than identify the two affine coordinate rings.  It sends the
generalized graph ideal `(u, y - v)` exactly to the sextic graph ideal
`(u, Y - (2v + X³ + X + 1))`.  The factor `1 / 2` appearing on the second
generator is a unit in the base field, so it does not change the generated
ideal.
-/

open Polynomial

namespace MazurProof.N13GoodSexticMumfordTransport

noncomputable section

open N13GoodSexticCoordinateEquiv

/-- Multiplying one generator of a two-generated ideal by a unit does not
change the ideal. -/
theorem span_pair_mul_right_unit
    {R : Type*} [CommRing R] (x a y : R) (ha : IsUnit a) :
    Ideal.span {x, a * y} = Ideal.span {x, y} := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      exact Ideal.mul_mem_left _ a (Ideal.subset_span (by simp))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      obtain ⟨b, hab⟩ := isUnit_iff_exists_inv.mp ha
      have hba : b * a = 1 := by
        simpa [mul_comm] using hab
      have hay : a * y ∈ Ideal.span {x, a * y} :=
        Ideal.subset_span (by simp)
      have hby : b * (a * y) ∈ Ideal.span {x, a * y} :=
        Ideal.mul_mem_left _ b hay
      simpa [← mul_assoc, hba] using hby

universe u

variable {K : Type u} [Field K] [CharZero K]

local notation "ModelK" =>
  N13GoodSexticCoordinateEquiv.M (K := K)

local notation "SexticRingK" =>
  N13GoodSexticCoordinateEquiv.SexticRing (K := K)

local notation "toSexticK" =>
  N13GoodSexticCoordinateEquiv.toSextic (K := K)

local notation "sexticXHomK" =>
  N13GoodSexticCoordinateEquiv.sexticXHom (K := K)

/-- The sextic graph polynomial corresponding to a generalized graph
polynomial `v`. -/
def completedGraph (v : K[X]) : K[X] :=
  2 * v + N13GeneralizedMumfordIntegral.hPoly

private theorem two_mul_invTwo :
    (2 : SexticRingK) *
        (algebraMap K SexticRingK) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat (algebraMap K SexticRingK) 2, ← map_mul]
  norm_num

/-- Under completion of the square, the generalized graph generator is
`1 / 2` times the corresponding sextic graph generator. -/
@[simp] theorem toSextic_ySubClass (v : K[X]) :
    toSexticK
        (N13GeneralizedMumfordIntegral.ySubClass v) =
      (algebraMap K SexticRingK) (2 : K)⁻¹ *
        SexticMumford.ySubClass ModelK (completedGraph v) := by
  simp only [N13GeneralizedMumfordIntegral.ySubClass, map_sub,
    N13GoodSexticCoordinateEquiv.toSextic_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    N13GoodSexticCoordinateEquiv.goodYInSextic,
    SexticMumford.ySubClass, completedGraph, Algebra.smul_def]
  have hhalf :
      (algebraMap K SexticRingK) (1 / 2 : K) =
        (algebraMap K SexticRingK) (2 : K)⁻¹ := by
    norm_num
  have hx :
      SexticMumford.xClass ModelK
          (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
        2 * SexticMumford.xClass ModelK v +
          SexticMumford.xClass ModelK
            N13GeneralizedMumfordIntegral.hPoly := by
    change sexticXHomK
        (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
      2 * sexticXHomK v +
        sexticXHomK N13GeneralizedMumfordIntegral.hPoly
    rw [map_add, map_mul, map_ofNat]
  rw [hhalf, hx]
  let a : SexticRingK :=
    (algebraMap K SexticRingK) (2 : K)⁻¹
  let Y : SexticRingK := SexticMumford.yClass ModelK
  let H : SexticRingK :=
    SexticMumford.xClass ModelK
      N13GeneralizedMumfordIntegral.hPoly
  let V : SexticRingK :=
    SexticMumford.xClass ModelK v
  change a * (Y - H) - V = a * (Y - (2 * V + H))
  have ha : 2 * a = 1 := two_mul_invTwo
  linear_combination V * ha

private theorem invTwo_isUnit :
    IsUnit ((algebraMap K SexticRingK) (2 : K)⁻¹) := by
  exact
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K)⁻¹ ≠ 0)).map
      (algebraMap K SexticRingK)

/-- Completion of the square maps each generalized Mumford graph ideal
exactly onto the corresponding sextic Mumford graph ideal. -/
theorem map_mumfordIdeal (u v : K[X]) :
    Ideal.map toSexticK
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal ModelK u (completedGraph v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    SexticMumford.mumfordIdeal, Ideal.map_span, Set.image_pair,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    toSextic_ySubClass]
  exact span_pair_mul_right_unit _ _ _ invTwo_isUnit

/-- Congruent graph polynomials define the same sextic graph ideal. -/
theorem sextic_mumfordIdeal_eq_of_dvd_sub
    (u v w : K[X]) (hvw : u ∣ v - w) :
    SexticMumford.mumfordIdeal ModelK u v =
      SexticMumford.mumfordIdeal ModelK u w := by
  obtain ⟨q, hq⟩ := hvw
  have hxsub :
      SexticMumford.xClass ModelK (v - w) =
        SexticMumford.xClass ModelK v -
          SexticMumford.xClass ModelK w := by
    change sexticXHomK (v - w) =
      sexticXHomK v - sexticXHomK w
    exact map_sub sexticXHomK v w
  have hxmul :
      SexticMumford.xClass ModelK (u * q) =
        SexticMumford.xClass ModelK u *
          SexticMumford.xClass ModelK q := by
    change sexticXHomK (u * q) =
      sexticXHomK u * sexticXHomK q
    exact map_mul sexticXHomK u q
  have hyw :
      SexticMumford.ySubClass ModelK w =
        SexticMumford.ySubClass ModelK v +
          SexticMumford.xClass ModelK u *
            SexticMumford.xClass ModelK q := by
    unfold SexticMumford.ySubClass
    rw [← hxmul, ← hq, hxsub]
    ring
  have hyv :
      SexticMumford.ySubClass ModelK v =
        SexticMumford.ySubClass ModelK w -
          SexticMumford.xClass ModelK u *
            SexticMumford.xClass ModelK q := by
    rw [hyw]
    ring
  have hxv :
      SexticMumford.xClass ModelK u ∈
        SexticMumford.mumfordIdeal ModelK u v :=
    SexticMumford.xClass_mem_mumfordIdeal ModelK u v
  have hxw :
      SexticMumford.xClass ModelK u ∈
        SexticMumford.mumfordIdeal ModelK u w :=
    SexticMumford.xClass_mem_mumfordIdeal ModelK u w
  have hyvmem :
      SexticMumford.ySubClass ModelK v ∈
        SexticMumford.mumfordIdeal ModelK u v := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hywmem :
      SexticMumford.ySubClass ModelK w ∈
        SexticMumford.mumfordIdeal ModelK u w := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hmulv :
      SexticMumford.xClass ModelK u *
          SexticMumford.xClass ModelK q ∈
        SexticMumford.mumfordIdeal ModelK u v := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal ModelK u v)
        (SexticMumford.xClass ModelK q) hxv
  have hmulw :
      SexticMumford.xClass ModelK u *
          SexticMumford.xClass ModelK q ∈
        SexticMumford.mumfordIdeal ModelK u w := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal ModelK u w)
        (SexticMumford.xClass ModelK q) hxw
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxw
    · rw [hz, hyv]
      exact Ideal.sub_mem
        (SexticMumford.mumfordIdeal ModelK u w)
        hywmem
        hmulw
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxv
    · rw [hz, hyw]
      exact Ideal.add_mem
        (SexticMumford.mumfordIdeal ModelK u v)
        hyvmem
        hmulv

/-- The reduced sextic graph polynomial attached to generalized data. -/
def reducedCompletedGraph (u v : K[X]) : K[X] :=
  completedGraph v % u

private theorem dvd_sub_mod (p u : K[X]) :
    u ∣ p - p % u := by
  refine ⟨p / u, ?_⟩
  have h := EuclideanDomain.mod_add_div p u
  calc
    p - p % u = (p % u + u * (p / u)) - p % u := by
      rw [h]
    _ = u * (p / u) := by ring

/-- The exact transport theorem with the sextic graph polynomial reduced
modulo `u`, as required by the standard Mumford representation. -/
theorem map_mumfordIdeal_reduced (u v : K[X]) :
    Ideal.map toSexticK
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal ModelK u
        (reducedCompletedGraph u v) := by
  rw [map_mumfordIdeal]
  exact sextic_mumfordIdeal_eq_of_dvd_sub _ _ _
    (dvd_sub_mod (completedGraph v) u)

/-- Completing the square carries the generalized Mumford equation to the
standard sextic equation. -/
theorem completedGraph_curve_eq
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    N13Mumford.f K - completedGraph D.v ^ 2 =
      D.u * (-4 * D.w) := by
  rw [N13GoodSexticCoordinateEquiv.sextic_eq_h_sq_add_four_rhs
    (K := K)]
  unfold completedGraph
  linear_combination -4 * D.curve_eq

/-- Reducing the completed graph polynomial modulo `u` preserves the
sextic divisibility relation. -/
theorem reducedCompletedGraph_curve_dvd
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    D.u ∣ N13Mumford.f K -
      reducedCompletedGraph D.u D.v ^ 2 := by
  let V : K[X] := completedGraph D.v
  let Vred : K[X] := reducedCompletedGraph D.u D.v
  obtain ⟨q, hq⟩ := dvd_sub_mod V D.u
  change V - Vred = D.u * q at hq
  refine ⟨-4 * D.w + q * (V + Vred), ?_⟩
  calc
    N13Mumford.f K - Vred ^ 2 =
        (N13Mumford.f K - V ^ 2) +
          (V - Vred) * (V + Vred) := by ring
    _ =
        D.u * (-4 * D.w) +
          (D.u * q) * (V + Vred) := by
      rw [completedGraph_curve_eq D, hq]
    _ = D.u * (-4 * D.w + q * (V + Vred)) := by ring

/-- A generalized Mumford representative over a characteristic-zero field,
written as a standard reduced sextic semirepresentative. -/
def toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    SexticMumford.SemiMumford ModelK where
  u := D.u
  v := reducedCompletedGraph D.u D.v
  nInf := nInf
  u_monic := D.u_monic
  v_reduced := by
    apply (Polynomial.mod_eq_self_iff D.u_monic.ne_zero).2
    exact Polynomial.degree_mod_lt _ D.u_monic.ne_zero
  curve_dvd := by
    simpa only [N13Mumford.model_f] using
      reducedCompletedGraph_curve_dvd D

@[simp] theorem toSexticSemi_u
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).u = D.u := rfl

@[simp] theorem toSexticSemi_v
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).v =
      reducedCompletedGraph D.u D.v := rfl

@[simp] theorem toSexticSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).nInf = nInf := rfl

/-- The reduced standard semirepresentative has exactly the transported
generalized graph ideal. -/
theorem map_mumfordIdeal_toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    Ideal.map toSexticK
        (N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) =
      SexticMumford.mumfordIdeal ModelK
        (toSexticSemi D nInf).u
        (toSexticSemi D nInf).v := by
  simpa only [toSexticSemi_u, toSexticSemi_v] using
    map_mumfordIdeal_reduced D.u D.v

end

end MazurProof.N13GoodSexticMumfordTransport


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Transporting integral N13 Mumford data to the two-adic sextic model

Smooth generalized Mumford data over `ℤ₂` first extend coefficientwise to
`ℚ₂`.  Completion of the square then gives a standard reduced sextic
semirepresentative.  This file records that passage without choosing
coordinates or enumerating residue classes.
-/

open Polynomial

namespace MazurProof.N13TwoAdicMumfordTransport

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev Q₂ : Type :=
  ℚ_[2]

def coeffMap : R₂ →+* Q₂ :=
  algebraMap R₂ Q₂

def mapPoly : R₂[X] →+* Q₂[X] :=
  Polynomial.mapRingHom coeffMap

@[simp] theorem mapPoly_apply (p : R₂[X]) :
    mapPoly p = p.map coeffMap := rfl

@[simp] theorem mapPoly_hPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.hPoly (R := Q₂) := by
  simp [mapPoly, coeffMap,
    N13GeneralizedMumfordIntegral.hPoly]

@[simp] theorem mapPoly_rhsPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂) := by
  simp [mapPoly, coeffMap,
    N13GeneralizedMumfordIntegral.rhsPoly]

/-- Coefficient extension does not require the additional special-fibre
smoothness witness. -/
def baseChangeSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    N13GeneralizedMumfordIntegral.SemiMumford (R := Q₂) where
  u := mapPoly D.u
  v := mapPoly D.v
  w := mapPoly D.w
  u_monic := D.u_monic.map coeffMap
  curve_eq := by
    have h := congrArg mapPoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      mapPoly_hPoly, mapPoly_rhsPoly] using h

@[simp] theorem baseChangeSemi_u
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).u = mapPoly D.u := rfl

@[simp] theorem baseChangeSemi_v
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).v = mapPoly D.v := rfl

@[simp] theorem baseChangeSemi_w
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).w = mapPoly D.w := rfl

/-- Coefficient extension of an integral generalized Mumford datum. -/
def baseChange
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.SemiMumford (R := Q₂) where
  u := mapPoly D.u
  v := mapPoly D.v
  w := mapPoly D.w
  u_monic := D.u_monic.map coeffMap
  curve_eq := by
    have h := congrArg mapPoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      mapPoly_hPoly, mapPoly_rhsPoly] using h

@[simp] theorem baseChange_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).u = mapPoly D.u := rfl

@[simp] theorem baseChange_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).v = mapPoly D.v := rfl

@[simp] theorem baseChange_w
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).w = mapPoly D.w := rfl

/-- The smoothness Bézout identity survives coefficient extension. -/
theorem baseChange_bezout
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    ∃ a b c : Q₂[X],
      a * (baseChange D).u +
          b * (2 * (baseChange D).v +
            N13GeneralizedMumfordIntegral.hPoly (R := Q₂)) +
        c * (baseChange D).w = 1 := by
  obtain ⟨a, b, c, habc⟩ := D.bezout
  refine ⟨mapPoly a, mapPoly b, mapPoly c, ?_⟩
  have h := congrArg mapPoly habc
  simpa only [baseChange_u, baseChange_v, baseChange_w,
    map_add, map_mul, map_ofNat, map_one, mapPoly_hPoly] using h

/-- The standard reduced sextic semirepresentative attached to arbitrary
integral generalized Mumford data. -/
def sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChangeSemi D) nInf

@[simp] theorem sexticSemiOfSemi_u
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).u = mapPoly D.u := rfl

@[simp] theorem sexticSemiOfSemi_v
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl

@[simp] theorem sexticSemiOfSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).nInf = nInf := rfl

/-- Completion of the square transports every integral generalized graph
ideal, independently of a vertical Bézout witness. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChangeSemi D).u (baseChangeSemi D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemiOfSemi D nInf).u
        (sexticSemiOfSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChangeSemi D) nInf

/-- The standard reduced sextic semirepresentative over `ℚ₂`. -/
def sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChange D) nInf

@[simp] theorem sexticSemi_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).u = mapPoly D.u := rfl

@[simp] theorem sexticSemi_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl

@[simp] theorem sexticSemi_nInf
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).nInf = nInf := rfl

/-- The two-adic sextic graph ideal is exactly the image of the generalized
graph ideal under completion of the square. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChange D).u (baseChange D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemi D nInf).u
        (sexticSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChange D) nInf

end

end MazurProof.N13TwoAdicMumfordTransport


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Base change of the N13 integral coordinate ring to `ℚ₂`

Coefficient extension from `ℤ₂` to `ℚ₂` induces a map between the two
generalized-hyperelliptic coordinate rings.  It carries an integral Mumford
graph ideal exactly onto the graph ideal obtained by coefficient extension.
Composing with completion of the square therefore sends the integral graph
directly to the standard sextic Mumford graph over `ℚ₂`.
-/

open Polynomial

namespace MazurProof.N13TwoAdicCoordinateBaseChange

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicMumfordTransport.R₂

abbrev Q₂ : Type :=
  N13TwoAdicMumfordTransport.Q₂

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev GoodRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := Q₂)

def coeffMap : R₂ →+* Q₂ :=
  N13TwoAdicMumfordTransport.coeffMap

def mapPoly : R₂[X] →+* Q₂[X] :=
  N13TwoAdicMumfordTransport.mapPoly

@[simp] theorem mapPoly_apply (p : R₂[X]) :
    mapPoly p = p.map coeffMap := rfl

/-- Coefficient extension from `ℤ₂[X]` to `ℚ₂[X]` is faithful. -/
theorem mapPoly_injective : Function.Injective mapPoly :=
  Polynomial.map_injective coeffMap
    (IsFractionRing.injective R₂ Q₂)

@[simp] theorem mapPoly_hPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.hPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_hPoly

@[simp] theorem mapPoly_rhsPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_rhsPoly

theorem map_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly =
      N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (mapPoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (mapPoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 +
          C (N13GeneralizedMumfordIntegral.hPoly (R := Q₂)) * X -
        C (N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂))
  rw [mapPoly_hPoly, mapPoly_rhsPoly]

private theorem target_curve_dvd :
    N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly := by
  rw [map_curvePoly]

/-- Coefficient extension on the affine coordinate ring of the good model. -/
def extendCoordinate : IntegralRing →+* GoodRing :=
  AdjoinRoot.map mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_xClass (p : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GeneralizedMumfordIntegral.xClass
        (R := Q₂) (mapPoly p) := by
  exact AdjoinRoot.map_of
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd p

@[simp] theorem extend_yClass :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GeneralizedMumfordIntegral.yClass (R := Q₂) := by
  exact AdjoinRoot.map_root
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_ySubClass (v : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GeneralizedMumfordIntegral.ySubClass
        (R := Q₂) (mapPoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass]

/-- Coefficient extension preserves the `1`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeff0_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeff0
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeff0 z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp

/-- Coefficient extension preserves the `Y`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeffY_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeffY
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeffY z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp

/-- Base change from the integral good model to its generic fibre loses no
functions.  This is the rank-two basis argument, not a localization
calculation in coordinates. -/
theorem extendCoordinate_injective :
    Function.Injective extendCoordinate := by
  intro z w h
  apply
    (N13GeneralizedMumfordIntegral.eq_iff_coeff z w).2
  constructor
  · apply mapPoly_injective
    simpa only [coeff0_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeff0 h
  · apply mapPoly_injective
    simpa only [coeffY_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeffY h

/-- Coefficient extension maps an integral graph ideal onto the
coefficient-extended graph ideal. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := Q₂) (mapPoly u) (mapPoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    Ideal.map_span, Set.image_pair, extend_xClass,
    extend_ySubClass]

/-- Extension followed by contraction fixes every integral generalized
Mumford graph.  The proof only uses monicity and coefficientwise
divisibility descent; no special-fibre smoothness witness is involved. -/
theorem comap_map_mumfordIdeal_semi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v)).comap extendCoordinate =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) D.u D.v := by
  ext z
  rw [Ideal.mem_comap, map_mumfordIdeal]
  change
    extendCoordinate z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13TwoAdicMumfordTransport.baseChangeSemi D).u
          (N13TwoAdicMumfordTransport.baseChangeSemi D).v ↔
      z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v
  rw [
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff
      (N13TwoAdicMumfordTransport.baseChangeSemi D),
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff D]
  simp only [N13TwoAdicMumfordTransport.baseChangeSemi_u,
    N13TwoAdicMumfordTransport.baseChangeSemi_v,
    coeff0_extendCoordinate, coeffY_extendCoordinate]
  change
    D.u.map coeffMap ∣
          (N13GeneralizedMumfordIntegral.coeff0 z).map coeffMap +
            (N13GeneralizedMumfordIntegral.coeffY z).map coeffMap *
              D.v.map coeffMap ↔
      D.u ∣
        N13GeneralizedMumfordIntegral.coeff0 z +
          N13GeneralizedMumfordIntegral.coeffY z * D.v
  rw [← Polynomial.map_mul, ← Polynomial.map_add]
  exact Polynomial.map_dvd_map coeffMap
    (IsFractionRing.injective R₂ Q₂) D.u_monic

/-- Extending a smooth integral graph to the generic fibre and contracting
it back recovers the original graph.  The reason is exactly that divisibility
by a monic polynomial descends along an injective coefficient map. -/
theorem comap_map_mumfordIdeal
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v)).comap extendCoordinate =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) D.u D.v := by
  ext z
  rw [Ideal.mem_comap, map_mumfordIdeal]
  change
    extendCoordinate z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13TwoAdicMumfordTransport.baseChange D).u
          (N13TwoAdicMumfordTransport.baseChange D).v ↔
      z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          D.toSemiMumford.u D.toSemiMumford.v
  rw [
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff
      (N13TwoAdicMumfordTransport.baseChange D),
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff
      D.toSemiMumford]
  simp only [N13TwoAdicMumfordTransport.baseChange_u,
    N13TwoAdicMumfordTransport.baseChange_v,
    coeff0_extendCoordinate, coeffY_extendCoordinate]
  change
    D.u.map coeffMap ∣
          (N13GeneralizedMumfordIntegral.coeff0 z).map coeffMap +
            (N13GeneralizedMumfordIntegral.coeffY z).map coeffMap *
              D.v.map coeffMap ↔
      D.u ∣
        N13GeneralizedMumfordIntegral.coeff0 z +
          N13GeneralizedMumfordIntegral.coeffY z * D.v
  rw [← Polynomial.map_mul, ← Polynomial.map_add]
  exact Polynomial.map_dvd_map coeffMap
    (IsFractionRing.injective R₂ Q₂) D.u_monic

/-- Consequently coefficient extension is injective on smooth integral
Mumford graph ideals. -/
theorem map_mumfordIdeal_injective
    {D E : N13GeneralizedMumfordReduction.SmoothMumford₂}
    (h :
      Ideal.map extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) D.u D.v) =
        Ideal.map extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) E.u E.v)) :
    N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) E.u E.v := by
  rw [← comap_map_mumfordIdeal D,
    ← comap_map_mumfordIdeal E, h]

/-- The full integral-to-sextic coordinate map over `ℚ₂`. -/
def integralToSextic :
    IntegralRing →+*
      N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂) :=
  (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂)).comp
    extendCoordinate

/-- An integral smooth graph ideal becomes exactly the standard reduced
sextic Mumford graph attached by `sexticSemi`. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemi
      D nInf

/-- The same coordinate transport theorem for arbitrary integral
semigraphs. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemiOfSemi
      D nInf

end

end MazurProof.N13TwoAdicCoordinateBaseChange


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralModelContraction
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Vertical localization and ideal contraction for the N13 integral model

The affine coordinate ring of the N13 generic fibre is obtained from the
integral good-model coordinate ring by inverting only the nonzero scalars of
`ℤ₂`.  The proof uses the rank-two normal form `p(x) + q(x)y`: a common
scalar denominator clears the two coefficient polynomials simultaneously.

Consequently every ideal on the generic affine fibre has a canonical
contraction to the integral model, and extending this contraction recovers
the original ideal exactly.  The contraction is vertically saturated.  This
is the algebraic integral-model layer needed before taking a reflexive hull
or lifting a section; it does not assert that the contracted ideal is already
invertible on the two-dimensional integral surface.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralModelContraction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicCoordinateBaseChange.R₂

abbrev Q₂ : Type :=
  N13TwoAdicCoordinateBaseChange.Q₂

abbrev IntegralRing : Type :=
  N13TwoAdicCoordinateBaseChange.IntegralRing

abbrev GoodRing : Type :=
  N13TwoAdicCoordinateBaseChange.GoodRing

abbrev RationalRing : Type :=
  N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂)

abbrev Pic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)

abbrev IntegralOrientedRep : Type :=
  SexticMumford.IntegralOrientedRep
    (N13Mumford.model Q₂)

/-- The integral good model maps to its generalized generic fibre. -/
def integralToGood : IntegralRing →+* GoodRing :=
  N13TwoAdicCoordinateBaseChange.extendCoordinate

local instance integralGoodAlgebra :
    Algebra IntegralRing GoodRing :=
  integralToGood.toAlgebra

/-- The vertical multiplicative set consists exactly of nonzero `ℤ₂`
scalars inside the integral coordinate ring. -/
def verticalScalars : Submonoid IntegralRing :=
  (nonZeroDivisors R₂).map
    (algebraMap R₂ IntegralRing)

local instance polynomialAlgebra :
    Algebra R₂[X] Q₂[X] :=
  Polynomial.algebra R₂ Q₂

local instance polynomialLocalization :
    IsLocalization
      ((nonZeroDivisors R₂).map
        (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom)
      Q₂[X] :=
  Polynomial.isLocalization (nonZeroDivisors R₂) Q₂

@[simp] theorem integralToGood_algebraMap
    (a : R₂) :
    integralToGood (algebraMap R₂ IntegralRing a) =
      algebraMap Q₂ GoodRing
        (N13TwoAdicCoordinateBaseChange.coeffMap a) := by
  change
    N13TwoAdicCoordinateBaseChange.extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C a)) =
      N13GeneralizedMumfordIntegral.xClass
        (C (N13TwoAdicCoordinateBaseChange.coeffMap a))
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass]
  simp [N13TwoAdicCoordinateBaseChange.mapPoly,
    N13TwoAdicCoordinateBaseChange.coeffMap]

/-- Inverting the vertical nonzero scalars produces the generalized generic
fibre coordinate ring. -/
theorem goodRing_isLocalization :
    IsLocalization verticalScalars GoodRing := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs := s.property
    change
      ∃ r : R₂, r ∈ nonZeroDivisors R₂ ∧
        algebraMap R₂ IntegralRing r =
          (s : IntegralRing) at hs
    obtain ⟨r, hr, hs⟩ := hs
    change IsUnit (integralToGood (s : IntegralRing))
    rw [← hs, integralToGood_algebraMap]
    have hr0 :
        N13TwoAdicCoordinateBaseChange.coeffMap r ≠ 0 := by
      change algebraMap R₂ Q₂ r ≠ 0
      simpa using
        (IsFractionRing.injective R₂ Q₂).ne
          (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    exact IsUnit.map (algebraMap Q₂ GoodRing)
      (isUnit_iff_ne_zero.mpr hr0)
  · intro z
    obtain ⟨p, q, d, hp, hq⟩ :=
      IsLocalization.surj₂
        ((nonZeroDivisors R₂).map
          (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom)
        Q₂[X]
        (N13GeneralizedMumfordIntegral.coeff0 z)
        (N13GeneralizedMumfordIntegral.coeffY z)
    obtain ⟨r, hr, hd⟩ := d.property
    change C r = (d : R₂[X]) at hd
    rw [← hd] at hp hq
    rw [Polynomial.algebraMap_def] at hp hq
    have hp0 :
        N13GeneralizedMumfordIntegral.coeff0 z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly p := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hp
    have hq0 :
        N13GeneralizedMumfordIntegral.coeffY z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly q := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hq
    let numerator : IntegralRing :=
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass
    let denominator : verticalScalars :=
      ⟨algebraMap R₂ IntegralRing r,
        ⟨r, hr, rfl⟩⟩
    refine ⟨⟨numerator, denominator⟩, ?_⟩
    change
      z * integralToGood (denominator : IntegralRing) =
        integralToGood numerator
    dsimp only [denominator, numerator]
    rw [← N13GeneralizedMumfordIntegral.recompose z]
    rw [integralToGood_algebraMap]
    unfold integralToGood
    simp only [map_add, map_mul,
      N13TwoAdicCoordinateBaseChange.extend_xClass,
      N13TwoAdicCoordinateBaseChange.extend_yClass]
    have hscalar :
        algebraMap Q₂ GoodRing
            (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13GeneralizedMumfordIntegral.xClass
            (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) :=
      rfl
    rw [hscalar]
    have hp' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hp0
    have hq' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hq0
    simp only [
      N13GeneralizedMumfordIntegral.xClass_mul] at hp' hq'
    calc
      (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) *
            N13GeneralizedMumfordIntegral.xClass
              (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) =
          N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) *
              N13GeneralizedMumfordIntegral.xClass
                (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) +
            (N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.xClass
                  (C (N13TwoAdicCoordinateBaseChange.coeffMap r))) *
              N13GeneralizedMumfordIntegral.yClass := by ring
      _ =
          N13GeneralizedMumfordIntegral.xClass
              (N13TwoAdicCoordinateBaseChange.mapPoly p) +
            N13GeneralizedMumfordIntegral.xClass
                (N13TwoAdicCoordinateBaseChange.mapPoly q) *
              N13GeneralizedMumfordIntegral.yClass := by
            rw [hp', hq']
  · intro x y hxy
    exact
      ⟨1, by
        simpa using
          N13TwoAdicCoordinateBaseChange.extendCoordinate_injective hxy⟩

local instance goodRingLocalization :
    IsLocalization verticalScalars GoodRing :=
  goodRing_isLocalization

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- Completion of the square is an equivalence over the integral model. -/
def goodToSextic :
    GoodRing ≃ₐ[IntegralRing] RationalRing where
  __ :=
    N13GoodSexticCoordinateEquiv.coordinateRingEquiv
      (K := Q₂)
  commutes' _ := rfl

/-- The standard sextic generic-fibre coordinate ring is the same vertical
localization. -/
theorem rationalRing_isLocalization :
    IsLocalization verticalScalars RationalRing :=
  IsLocalization.isLocalization_of_algEquiv
    verticalScalars goodToSextic

local instance rationalRingLocalization :
    IsLocalization verticalScalars RationalRing :=
  rationalRing_isLocalization

/-- Canonical contraction of a generic-fibre ideal to the integral model. -/
def contractIdeal
    (J : Ideal RationalRing) :
    Ideal IntegralRing :=
  J.under IntegralRing

/-- Extending the canonical contraction recovers the generic-fibre ideal
exactly. -/
theorem map_contractIdeal
    (J : Ideal RationalRing) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (contractIdeal J) =
      J := by
  exact IsLocalization.map_under
    verticalScalars RationalRing J

/-- Contraction loses no nonzero ideal. -/
theorem contractIdeal_ne_bot
    {J : Ideal RationalRing}
    (hJ : J ≠ ⊥) :
    contractIdeal J ≠ ⊥ := by
  intro hbot
  apply hJ
  rw [← map_contractIdeal J, hbot, Ideal.map_bot]

/-- The contracted ideal is saturated with respect to every nonzero
vertical scalar. -/
theorem contractIdeal_vertical_saturated
    (J : Ideal RationalRing)
    {a : IntegralRing}
    (r : R₂) (hr : r ≠ 0)
    (ha :
      algebraMap R₂ IntegralRing r * a ∈
        contractIdeal J) :
    a ∈ contractIdeal J := by
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic
        (algebraMap R₂ IntegralRing r * a) ∈ J at ha
  rw [map_mul] at ha
  let s : verticalScalars :=
    ⟨algebraMap R₂ IntegralRing r,
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩
  have hs :
      IsUnit
        (algebraMap IntegralRing RationalRing s) :=
    IsLocalization.map_units RationalRing s
  exact (Ideal.unit_mul_mem_iff_mem J hs).mp ha

/-- Every local oriented Picard class therefore has a canonical integral
model ideal whose generic fibre is exactly an integral ideal representative
of that class.  This statement does not yet promote the contraction to an
invertible ideal on the integral surface. -/
theorem exists_integralModelIdeal
    (c : Pic) :
    ∃ J₀ : Ideal IntegralRing,
      ∃ R : IntegralOrientedRep,
        J₀ ≠ ⊥ ∧
          Ideal.map
              N13TwoAdicCoordinateBaseChange.integralToSextic
              J₀ =
            R.ideal ∧
          R.picClass
              (N13Mumford.model Q₂)
              (N13Infinity.positiveInfinityOrder Q₂) =
            c := by
  obtain ⟨R, hR⟩ :=
    SexticMumford.exists_integralRepresentative
      (N13Mumford.model Q₂)
      (N13Infinity.positiveInfinityOrder Q₂)
      c
  exact
    ⟨contractIdeal R.ideal, R,
      contractIdeal_ne_bot
        (R.ideal_ne_bot (N13Mumford.model Q₂)),
      map_contractIdeal R.ideal, hR⟩

end

end MazurProof.N13IntegralModelContraction


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13QuotientReduction
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Reduction of N13 affine quotients

A surjective ambient reduction map descends along a literal mapped-ideal
equality.  The kernel of the descended map is exactly the image of the
ambient kernel.  For the N13 integral model this is the principal ideal
generated by the quotient class of `2`.

No flatness, saturation, or chosen Mumford presentation is used here.
-/

namespace MazurProof.N13QuotientReduction

noncomputable section

universe uA uS

variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]

private theorem sourceIdeal_le_ker_quotientComp
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    I ≤ RingHom.ker ((Ideal.Quotient.mk J).comp f) := by
  intro a ha
  rw [RingHom.mem_ker, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem, ← hmap]
  exact Ideal.mem_map_of_mem f ha

/-- The quotient map induced by a ring map carrying the source ideal
literally onto the target ideal. -/
def inducedQuotientMap
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    A ⧸ I →+* S ⧸ J :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk J).comp f)
    (sourceIdeal_le_ker_quotientComp f I J hmap)

@[simp] theorem inducedQuotientMap_mk
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J)
    (a : A) :
    inducedQuotientMap f I J hmap
        (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f a) :=
  rfl

/-- Surjectivity descends to the quotient rings. -/
theorem inducedQuotientMap_surjective
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    Function.Surjective
      (inducedQuotientMap f I J hmap) := by
  unfold inducedQuotientMap
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact Ideal.Quotient.mk_surjective.comp hf

/-- For a surjective ambient map, the quotient kernel is the image of the
ambient kernel. -/
theorem ker_inducedQuotientMap_eq_map_ker
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.map (Ideal.Quotient.mk I) (RingHom.ker f) := by
  have hkerComp :
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
        I ⊔ RingHom.ker f := by
    calc
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
          Ideal.comap f
            (RingHom.ker (Ideal.Quotient.mk J)) :=
        (RingHom.comap_ker (Ideal.Quotient.mk J) f).symm
      _ = Ideal.comap f J := by
        rw [Ideal.mk_ker]
      _ = Ideal.comap f (Ideal.map f I) :=
        congrArg (Ideal.comap f) hmap.symm
      _ = I ⊔ Ideal.comap f (⊥ : Ideal S) :=
        Ideal.comap_map_of_surjective f hf I
      _ = I ⊔ RingHom.ker f := by
        rfl
  unfold inducedQuotientMap
  rw [Ideal.ker_quotient_lift, hkerComp,
    Ideal.map_sup, Ideal.map_quotient_self]
  simp

/-- A principal ambient kernel remains principal after quotienting. -/
theorem ker_inducedQuotientMap_eq_span
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J)
    (r : A)
    (hker :
      RingHom.ker f = Ideal.span ({r} : Set A)) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.span
        ({Ideal.Quotient.mk I r} : Set (A ⧸ I)) := by
  rw [ker_inducedQuotientMap_eq_map_ker
      f hf I J hmap,
    hker, Ideal.map_span]
  simp

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13GeneralizedMumfordReduction.R₂

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordReduction.IntegralRing

abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

/-- N13 coefficient reduction descended along a mapped-ideal equality. -/
def reduceCoordinateQuotient
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    IntegralRing ⧸ I →+* SpecialRing ⧸ J :=
  inducedQuotientMap
    N13GeneralizedMumfordReduction.reduceCoordinate I J hmap

@[simp] theorem reduceCoordinateQuotient_mk
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J)
    (a : IntegralRing) :
    reduceCoordinateQuotient I J hmap
        (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J
        (N13GeneralizedMumfordReduction.reduceCoordinate a) :=
  rfl

theorem reduceCoordinateQuotient_surjective
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    Function.Surjective
      (reduceCoordinateQuotient I J hmap) := by
  exact
    inducedQuotientMap_surjective
      N13GeneralizedMumfordReduction.reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
      I J hmap

/-- The descended N13 reduction kernel is generated by the quotient class
of the vertical parameter `2`. -/
theorem ker_reduceCoordinateQuotient
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceCoordinateQuotient I J hmap) =
      Ideal.span
        ({Ideal.Quotient.mk I
            (algebraMap R₂ IntegralRing (2 : R₂))} :
          Set (IntegralRing ⧸ I)) := by
  exact
    ker_inducedQuotientMap_eq_span
      N13GeneralizedMumfordReduction.reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
      I J hmap
      (algebraMap R₂ IntegralRing (2 : R₂))
      N13GeneralizedMumfordReduction.ker_reduceCoordinate

/-- Equivalent scalar-algebra-map spelling of the same kernel. -/
theorem ker_reduceCoordinateQuotient_eq_span_two
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceCoordinateQuotient I J hmap) =
      Ideal.span
        ({algebraMap R₂ (IntegralRing ⧸ I) (2 : R₂)} :
          Set (IntegralRing ⧸ I)) := by
  simpa only [Ideal.Quotient.mk_algebraMap] using
    ker_reduceCoordinateQuotient I J hmap

end

end MazurProof.N13QuotientReduction


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The literal basis of a quadratic sextic Mumford quotient

For a monic degree-two Mumford polynomial `u`, graph evaluation identifies
the affine quotient by `(u,Y-v)` with `K[X]/(u)`.  Transporting the canonical
power basis gives the literal quotient basis `{1,x}`.
-/

open Module
open Polynomial

namespace MazurProof.SexticMumfordQuotientBasis

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)

/-- The monic polynomial quotient has its canonical quadratic power basis. -/
def residueBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K (AdjoinRoot D.u) :=
  (AdjoinRoot.powerBasis' D.u_monic).basis.reindex
    (finCongr hdeg)

theorem residueBasis_apply
    (hdeg : D.u.natDegree = 2) (i : Fin 2) :
    residueBasis M D hdeg i =
      AdjoinRoot.root D.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' D.u_monic).basis.reindex
        (finCongr hdeg)) i =
      AdjoinRoot.root D.u ^ (i : ℕ)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

@[simp] theorem residueBasis_zero
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]

@[simp] theorem residueBasis_one
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (1 : Fin 2) =
      AdjoinRoot.root D.u := by
  simp [residueBasis_apply]

/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K
      (SexticMumford.CoordinateRing M ⧸
        SexticMumford.mumfordIdeal M D.u D.v) :=
  (residueBasis M D hdeg).map
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm.toLinearEquiv

@[simp] theorem quotientBasis_zero
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (0 : Fin 2) = 1 := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 0) = 1
  rw [residueBasis_zero]
  exact map_one (SexticMumford.mumfordQuotientAlgEquiv M D).symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem quotientBasis_one
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (1 : Fin 2) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X) := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 1) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X)
  rw [residueBasis_one]
  apply (SexticMumford.mumfordQuotientAlgEquiv M D).injective
  rw [(SexticMumford.mumfordQuotientAlgEquiv M D).apply_symm_apply]
  simp only [SexticMumford.mumfordQuotientAlgEquiv]
  change
    AdjoinRoot.root D.u =
      SexticMumford.mumfordEval M D
        (SexticMumford.xClass M X)
  rw [SexticMumford.mumfordEval_xClass]
  rfl

/-- The transported basis family is literally `{1,x}`. -/
theorem coe_quotientBasis
    (hdeg : D.u.natDegree = 2) :
    (quotientBasis M D hdeg :
        Fin 2 →
          SexticMumford.CoordinateRing M ⧸
            SexticMumford.mumfordIdeal M D.u D.v) =
      ![1,
        Ideal.Quotient.mk
          (SexticMumford.mumfordIdeal M D.u D.v)
          (SexticMumford.xClass M X)] := by
  funext i
  fin_cases i <;> simp

end

end MazurProof.SexticMumfordQuotientBasis


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Generic quotient of a canonical N13 contraction

Extending a canonical vertical contraction to the generic fibre recovers the
original ideal.  The induced map on affine quotients is injective: membership
in the contraction is definitionally membership of the image in the generic
ideal.  For a quadratic Mumford graph, this map carries the literal integral
classes of `1` and `x` to the literal generic quotient basis `{1,x}`.
-/

open Polynomial

namespace MazurProof.N13CanonicalContractionQuotient

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- The quotient map from a canonical contraction to its generic ideal. -/
def genericQuotientMap (J : Ideal RationalRing) :
    IntegralRing ⧸ N13IntegralModelContraction.contractIdeal J →+*
      RationalRing ⧸ J :=
  N13QuotientReduction.inducedQuotientMap
    N13TwoAdicCoordinateBaseChange.integralToSextic
    (N13IntegralModelContraction.contractIdeal J)
    J
    (N13IntegralModelContraction.map_contractIdeal J)

@[simp] theorem genericQuotientMap_mk
    (J : Ideal RationalRing) (a : IntegralRing) :
    genericQuotientMap J
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal J) a) =
      Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) :=
  rfl

/-- No element is lost when passing from the contracted quotient to the
generic quotient. -/
theorem genericQuotientMap_injective
    (J : Ideal RationalRing) :
    Function.Injective (genericQuotientMap J) := by
  intro z w hzw
  apply sub_eq_zero.mp
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (z - w)
  rw [← ha]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  calc
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) =
        genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a) := rfl
    _ = genericQuotientMap J (z - w) :=
      congrArg (genericQuotientMap J) ha
    _ = genericQuotientMap J z -
        genericQuotientMap J w := map_sub _ z w
    _ = 0 := by rw [hzw, sub_self]

/-- The generic quotient map respects the two-adic coefficient action. -/
theorem genericQuotientMap_comp_algebraMap
    (J : Ideal RationalRing) :
    (genericQuotientMap J).comp
        (algebraMap R₂
          (IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal J)) =
      algebraMap R₂ (RationalRing ⧸ J) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk J (algebraMap R₂ RationalRing r)
  congr 1
  change
    N13GoodSexticCoordinateEquiv.toSextic
        (N13IntegralModelContraction.integralToGood
          (algebraMap R₂ IntegralRing r)) =
      algebraMap R₂ RationalRing r
  rw [N13IntegralModelContraction.integralToGood_algebraMap,
    N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
  exact
    (IsScalarTower.algebraMap_apply R₂ Q₂ RationalRing r).symm

/-- The integral affine `x` coordinate. -/
def integralX : IntegralRing :=
  N13GeneralizedMumfordIntegral.xClass (R := R₂) X

@[simp] theorem integralToSextic_integralX :
    N13TwoAdicCoordinateBaseChange.integralToSextic integralX =
      SexticMumford.xClass Model X := by
  simp [integralX,
    N13TwoAdicCoordinateBaseChange.integralToSextic]

/-- The generic graph ideal of sextic Mumford data. -/
abbrev graphIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal Model D.u D.v

/-- The canonical contraction map sends `1` to the zero-th literal generic
basis vector. -/
theorem genericQuotientMap_one_eq_basis_zero
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    genericQuotientMap (graphIdeal D)
        (1 :
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (graphIdeal D)) =
      SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg 0 := by
  simp

/-- The canonical contraction map sends the integral class of `x` to the
first literal generic basis vector. -/
theorem genericQuotientMap_x_eq_basis_one
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    genericQuotientMap (graphIdeal D)
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal
            (graphIdeal D))
          integralX) =
      SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg 1 := by
  rw [genericQuotientMap_mk,
    integralToSextic_integralX,
    SexticMumfordQuotientBasis.quotientBasis_one]

end

end MazurProof.N13CanonicalContractionQuotient


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GenericQuotientLocalization
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The generic fibre of a canonical N13 contraction

The quotient by a canonical vertical contraction becomes the original
Mumford quotient after inverting the nonzero two-adic scalars.  Consequently,
a contracted quadratic Mumford quotient has rank two over the two-adic
integers.  No preferred integral basis is used.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13GenericQuotientLocalization

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev Q₂ : Type := N13IntegralModelContraction.Q₂
abbrev IntegralRing : Type := N13IntegralModelContraction.IntegralRing
abbrev RationalRing : Type := N13IntegralModelContraction.RationalRing
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

/-- The generic quotient map as a two-adic algebra homomorphism. -/
def genericQuotientAlgHom (J : Ideal RationalRing) :
    (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) →ₐ[R₂]
      (RationalRing ⧸ J) where
  toRingHom :=
    N13CanonicalContractionQuotient.genericQuotientMap J
  commutes' r :=
    DFunLike.congr_fun
      (N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap J)
      r

/-- The generic quotient map is localization at the nonzero two-adic
scalars. -/
theorem genericQuotient_isLocalized
    (J : Ideal RationalRing) :
    IsLocalizedModule (nonZeroDivisors R₂)
      (genericQuotientAlgHom J).toLinearMap := by
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro s
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hs :
          algebraMap R₂ Q₂ (s : R₂) ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      apply_fun
        (fun z : G ↦
          (algebraMap R₂ Q₂ (s : R₂))⁻¹ • z) at hxy
      simpa [Module.algebraMap_end_apply,
        ← IsScalarTower.algebraMap_smul Q₂, hs] using hxy
    · intro y
      let c : Q₂ := algebraMap R₂ Q₂ (s : R₂)
      have hc : c ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      refine ⟨c⁻¹ • y, ?_⟩
      change c • (c⁻¹ • y) = y
      exact smul_inv_smul₀ hc y
  · intro y
    obtain ⟨z, rfl⟩ :=
      Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, s⟩, hz⟩ :=
      IsLocalization.surj
        N13IntegralModelContraction.verticalScalars z
    obtain ⟨r, hr, hs⟩ := s.property
    refine
      ⟨⟨Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a,
          ⟨r, hr⟩⟩,
        ?_⟩
    change
      r • Ideal.Quotient.mk J z =
        N13CanonicalContractionQuotient.genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a)
    rw [N13CanonicalContractionQuotient.genericQuotientMap_mk,
      Algebra.smul_def]
    change
      Ideal.Quotient.mk J
          (algebraMap R₂ RationalRing r * z) =
        Ideal.Quotient.mk J
          (N13TwoAdicCoordinateBaseChange.integralToSextic a)
    apply congrArg (Ideal.Quotient.mk J)
    rw [mul_comm]
    calc
      z * algebraMap R₂ RationalRing r =
          z *
            N13TwoAdicCoordinateBaseChange.integralToSextic
              (s : IntegralRing) := by
        rw [← hs]
        congr 1
        symm
        change
          N13GoodSexticCoordinateEquiv.toSextic
              (N13IntegralModelContraction.integralToGood
                (algebraMap R₂ IntegralRing r)) =
            algebraMap R₂ RationalRing r
        rw [N13IntegralModelContraction.integralToGood_algebraMap,
          N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
        exact
          (IsScalarTower.algebraMap_apply
            R₂ Q₂ RationalRing r).symm
      _ = N13TwoAdicCoordinateBaseChange.integralToSextic a := hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [one_smul]
    exact
      N13CanonicalContractionQuotient.genericQuotientMap_injective J hxy

/-- A quadratic generic Mumford quotient forces its canonical contracted
quotient to have rank two over the two-adic integers. -/
theorem contractQuotient_finrank_eq_two
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    Module.finrank R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (SexticMumford.mumfordIdeal Model D.u D.v)) =
      2 := by
  let J : Ideal RationalRing :=
    SexticMumford.mumfordIdeal Model D.u D.v
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  let q : B →ₗ[R₂] G :=
    (genericQuotientAlgHom J).toLinearMap
  letI : IsLocalizedModule (nonZeroDivisors R₂) q :=
    genericQuotient_isLocalized J
  have hloc :
      Module.finrank R₂ G =
        Module.finrank R₂ B :=
    IsLocalizedModule.finrank_eq
      (nonZeroDivisors R₂) q le_rfl
  have hrank :
      Module.rank Q₂ G =
        Module.rank R₂ G :=
    IsLocalization.rank_eq
      Q₂ (nonZeroDivisors R₂) le_rfl
  have hfield :
      Module.finrank Q₂ G =
        Module.finrank R₂ G := by
    simpa only [Module.finrank] using
      congrArg Cardinal.toNat hrank
  have hgeneric :
      Module.finrank Q₂ G = 2 := by
    rw [Module.finrank_eq_card_basis
      (SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg)]
    rfl
  change Module.finrank R₂ B = 2
  calc
    Module.finrank R₂ B =
        Module.finrank R₂ G := hloc.symm
    _ = Module.finrank Q₂ G := hfield.symm
    _ = 2 := hgeneric

end

end MazurProof.N13GenericQuotientLocalization


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Vertical saturation gives flat N13 quotients

The canonical contraction of a generic ideal is saturated with respect to
every nonzero two-adic scalar.  Consequently its affine quotient has no
two-adic torsion.  Since the two-adic integers form a Dedekind domain, the
quotient is flat even before finiteness has been established.

This separates the easy vertical part of the two-fibre argument from the
genuine no-escape/finiteness step.
-/

namespace MazurProof.N13QuotientVerticalFlatness

noncomputable section

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]

/--
An ideal saturated with respect to every nonzero base scalar has a
torsion-free quotient over the base.
-/
theorem quotient_isTorsionFree_of_scalar_saturated
    (I : Ideal A)
    (hsaturated :
      ∀ (r : R), r ≠ 0 →
        ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I) :
    Module.IsTorsionFree R (A ⧸ I) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hrz
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hsaturated r hr a
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    change
      algebraMap R (A ⧸ I) r *
          Ideal.Quotient.mk I a = 0
    simpa only [Algebra.smul_def] using hrz

/-- Torsion-freeness of an ideal quotient recovers cancellation by every
nonzero scalar from the base domain.

Together with `quotient_isTorsionFree_of_scalar_saturated`, this identifies
vertical saturation exactly with relative torsion-freeness of the quotient;
there is no additional ideal-theoretic hypothesis hidden in that change of
language. -/
theorem scalar_saturated_of_quotient_isTorsionFree
    (I : Ideal A)
    (hfree : Module.IsTorsionFree R (A ⧸ I)) :
    ∀ (r : R), r ≠ 0 →
      ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I := by
  letI : Module.IsTorsionFree R (A ⧸ I) := hfree
  intro r hr a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hzero :
      r • Ideal.Quotient.mk I a = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [Algebra.smul_def] using ha
  exact (smul_eq_zero.mp hzero).resolve_left hr

/-- Vertical scalar saturation is equivalent to torsion-freeness of the
quotient module over the base domain. -/
theorem scalar_saturated_iff_quotient_isTorsionFree
    (I : Ideal A) :
    (∀ (r : R), r ≠ 0 →
        ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I) ↔
      Module.IsTorsionFree R (A ⧸ I) := by
  constructor
  · exact quotient_isTorsionFree_of_scalar_saturated I
  · exact scalar_saturated_of_quotient_isTorsionFree I

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- The quotient by a canonical vertical contraction is two-adically
torsion-free. -/
theorem contractQuotient_isTorsionFree
    (J : Ideal RationalRing) :
    Module.IsTorsionFree R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  apply quotient_isTorsionFree_of_scalar_saturated
  intro r hr a ha
  exact
    N13IntegralModelContraction.contractIdeal_vertical_saturated
      J r hr ha

/-- Over the two-adic DVR the same quotient is flat, with no finiteness
assumption. -/
theorem contractQuotient_flat
    (J : Ideal RationalRing) :
    Module.Flat R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  letI :
      Module.IsTorsionFree R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal J) :=
    contractQuotient_isTorsionFree J
  infer_instance

end

end MazurProof.N13QuotientVerticalFlatness


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TensorSpecialFiber
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Identifying a tensor special fibre from its quotient map

Suppose a surjective quotient-reduction map has kernel generated by the
image of a uniformizer.  Tensoring with the residue field then gives the
target quotient exactly.  The proof uses pure tensors and moves the
uniformizer to the residue-field factor; it does not identify a separate
quotient of the source ideal.
-/

open scoped TensorProduct
open Module

namespace MazurProof.N13TensorSpecialFiber

noncomputable section

universe uR uk uB uC uι

variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [CommRing k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]

/-- Regard a ring homomorphism as an `R`-algebra homomorphism through the
supplied scalar factorization. -/
def factoredAlgHom
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k)) :
    B →ₐ[R] C where
  toRingHom := g
  commutes' r := by
    calc
      g (algebraMap R B r) =
          algebraMap k C (algebraMap R k r) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor r
      _ = algebraMap R C r :=
        (IsScalarTower.algebraMap_apply R k C r).symm

@[simp] theorem factoredAlgHom_apply
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (b : B) :
    factoredAlgHom g hfactor b = g b :=
  rfl

/-- The canonical map `a ⊗ b ↦ a • g(b)`. -/
def tensorLinearMap
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k)) :
    k ⊗[R] B →ₗ[k] C :=
  (factoredAlgHom g hfactor).toLinearMap.liftBaseChange k

@[simp] theorem tensorLinearMap_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (a : k) (b : B) :
    tensorLinearMap g hfactor (a ⊗ₜ[R] b) =
      a • g b := by
  simp [tensorLinearMap]

private theorem tensorLinearMap_eq_zero
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    {z : k ⊗[R] B}
    (hz : tensorLinearMap g hfactor z = 0) :
    z = 0 := by
  obtain ⟨b, rfl⟩ :=
    (TensorProduct.mk_surjective R B k hq) z
  change
    tensorLinearMap g hfactor
        ((1 : k) ⊗ₜ[R] b) = 0 at hz
  change (1 : k) ⊗ₜ[R] b = 0
  have hgb : g b = 0 := by
    simpa only [tensorLinearMap_tmul, one_smul] using hz
  have hbker : b ∈ RingHom.ker g :=
    RingHom.mem_ker.mpr hgb
  rw [hker, Ideal.mem_span_singleton] at hbker
  obtain ⟨c, rfl⟩ := hbker
  calc
    (1 : k) ⊗ₜ[R] (algebraMap R B π * c) =
        (1 : k) ⊗ₜ[R] (π • c) := by
      rw [Algebra.smul_def]
    _ = (π • (1 : k)) ⊗ₜ[R] c :=
      (TensorProduct.smul_tmul
        (R := R) π (1 : k) c).symm
    _ = 0 := by
      simp only [Algebra.smul_def, hπ, zero_mul,
        TensorProduct.zero_tmul]

theorem tensorLinearMap_injective
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B)) :
    Function.Injective (tensorLinearMap g hfactor) := by
  intro z₁ z₂ hz
  have hzero :
      tensorLinearMap g hfactor (z₁ - z₂) = 0 := by
    simpa only [map_sub, hz, sub_self]
  exact sub_eq_zero.mp
    (tensorLinearMap_eq_zero
      (g := g) (hfactor := hfactor)
      (hq := hq) (π := π) (hπ := hπ)
      (hker := hker) hzero)

theorem tensorLinearMap_surjective
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hg : Function.Surjective g) :
    Function.Surjective (tensorLinearMap g hfactor) := by
  intro c
  obtain ⟨b, rfl⟩ := hg c
  exact ⟨(1 : k) ⊗ₜ[R] b, by simp⟩

/-- The explicit linear equivalence between the tensor special fibre and
the target quotient. -/
def tensorLinearEquiv
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B)) :
    k ⊗[R] B ≃ₗ[k] C :=
  LinearEquiv.ofBijective (tensorLinearMap g hfactor)
    ⟨tensorLinearMap_injective
        (g := g) (hfactor := hfactor)
        (hq := hq) (π := π) (hπ := hπ)
        (hker := hker),
      tensorLinearMap_surjective
        (g := g) (hfactor := hfactor) hg⟩

@[simp] theorem tensorLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : k) (b : B) :
    tensorLinearEquiv g hfactor hq π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact tensorLinearMap_tmul g hfactor a b

section ResidueField

variable [IsLocalRing R]

local notation "κ" => IsLocalRing.ResidueField R

variable [Algebra (IsLocalRing.ResidueField R) C]
variable [IsScalarTower R (IsLocalRing.ResidueField R) C]

theorem residueFactor
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap κ C).comp (IsLocalRing.residue R)) :
    g.comp (algebraMap R B) =
      (algebraMap κ C).comp (algebraMap R κ) := by
  simpa only [IsLocalRing.ResidueField.algebraMap_eq R] using hfactor

theorem residueAlgebraMap_surjective :
    Function.Surjective (algebraMap R κ) := by
  simpa only [IsLocalRing.ResidueField.algebraMap_eq R] using
    (IsLocalRing.residue_surjective (R := R))

theorem residueElement_eq_zero
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R) :
    algebraMap R κ π = 0 := by
  rw [IsLocalRing.ResidueField.algebraMap_eq R,
    IsLocalRing.residue_eq_zero_iff]
  exact hπ

/-- Residue-field specialization of `tensorLinearEquiv`. -/
def residueLinearEquiv
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap κ C).comp (IsLocalRing.residue R))
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B)) :
    κ ⊗[R] B ≃ₗ[κ] C :=
  tensorLinearEquiv
    (g := g)
    (hfactor := residueFactor g hfactor)
    (hq := residueAlgebraMap_surjective (R := R))
    (π := π)
    (hπ := residueElement_eq_zero π hπ)
    (hg := hg)
    (hker := hker)

@[simp] theorem residueLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap κ C).comp (IsLocalRing.residue R))
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : κ) (b : B) :
    residueLinearEquiv g hfactor π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact
    tensorLinearEquiv_tmul
      (g := g)
      (hfactor := residueFactor g hfactor)
      (hq := residueAlgebraMap_surjective (R := R))
      (π := π)
      (hπ := residueElement_eq_zero π hπ)
      (hg := hg)
      (hker := hker)
      a b

end ResidueField

section BasisTransport

variable {ι : Type uι}

/-- Pull a target basis back through the special-fibre equivalence. -/
def pullbackBasis
    (e : k ⊗[R] B ≃ₗ[k] C)
    (bC : Basis ι k C) :
    Basis ι k (k ⊗[R] B) :=
  bC.map e.symm

@[simp] theorem pullbackBasis_apply
    (e : k ⊗[R] B ≃ₗ[k] C)
    (bC : Basis ι k C)
    (i : ι) :
    pullbackBasis e bC i = e.symm (bC i) := by
  simp [pullbackBasis]

theorem mk_eq_pullbackBasis
    (e : k ⊗[R] B ≃ₗ[k] C)
    (v : ι → B)
    (bC : Basis ι k C)
    (heval :
      ∀ i : ι,
        e (TensorProduct.mk R k B 1 (v i)) = bC i) :
    ∀ i : ι,
      TensorProduct.mk R k B 1 (v i) =
        pullbackBasis e bC i := by
  intro i
  apply e.injective
  simpa [pullbackBasis] using heval i

end BasisTransport

end

end MazurProof.N13TensorSpecialFiber


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoGeneratorFiberBasis
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# A two-generator basis dichotomy in dimension two

The special N13 affine coordinate ring, and every one of its quotients, is
generated by the literal coordinates `x` and `y`.  In a two-dimensional
quotient over a field, this implies structurally that either `{1,x}` or
`{1,y}` is a basis.
-/

open Module
open Polynomial

namespace MazurProof.N13TwoGeneratorFiberBasis

noncomputable section

universe uK uB

variable {K : Type uK} {B : Type uB}
variable [Field K] [CommRing B] [Algebra K B] [Nontrivial B]

/-- If a two-dimensional algebra is generated by `x` and `y`, then one of
`{1,x}` and `{1,y}` is linearly independent. -/
theorem oneX_or_oneY_linearIndependent
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    LinearIndependent K ![1, x] ∨
      LinearIndependent K ![1, y] := by
  by_contra h
  have hxNot : ¬ LinearIndependent K ![1, x] :=
    fun hx ↦ h (Or.inl hx)
  have hyNot : ¬ LinearIndependent K ![1, y] :=
    fun hy ↦ h (Or.inr hy)
  have hx :
      ∃ a : K, algebraMap K B a = x := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hxNot
    push Not at hxNot
    obtain ⟨a, ha⟩ := hxNot
    exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
  have hy :
      ∃ b : K, algebraMap K B b = y := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hyNot
    push Not at hyNot
    obtain ⟨b, hb⟩ := hyNot
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hbot : (⊥ : Subalgebra K B) = ⊤ := by
    apply top_unique
    rw [← hgen, Algebra.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  have hsurj : Function.Surjective (algebraMap K B) := by
    intro z
    have hz : z ∈ (⊥ : Subalgebra K B) := by
      rw [hbot]
      trivial
    simpa only [Algebra.mem_bot, Set.mem_range] using hz
  have hbij :
      Function.Bijective (algebraMap K B) :=
    ⟨FaithfulSMul.algebraMap_injective K B, hsurj⟩
  have hrank :
      Module.finrank K B = 1 :=
    Module.finrank_of_bijective_algebraMap hbij
  omega

/-- Basis-valued form of `oneX_or_oneY_linearIndependent`. -/
theorem exists_basis_oneX_or_oneY
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, x]) ∨
      (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, y]) := by
  rcases oneX_or_oneY_linearIndependent x y hfinrank hgen with hx | hy
  · left
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hx (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩
  · right
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hy (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩

abbrev SpecialField : Type := N13GoodCoordinateRingTwo.K
abbrev SpecialRing : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- Every polynomial in the special `x` coordinate lies in the subalgebra
generated by the literal `x` and `y` coordinates. -/
theorem xClass_mem_coordinateAdjoin
    (p : SpecialField[X]) :
    N13GoodCoordinateRingTwo.xClass p ∈
      Algebra.adjoin SpecialField
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) := by
  let S : Subalgebra SpecialField SpecialRing :=
    Algebra.adjoin SpecialField
      ({N13GoodCoordinateRingTwo.xClass X,
        N13GoodCoordinateRingTwo.yClass} :
        Set SpecialRing)
  change N13GoodCoordinateRingTwo.xClass p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [N13GoodCoordinateRingTwo.xClass_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial,
        N13GoodCoordinateRingTwo.xClass_mul,
        N13GoodCoordinateRingTwo.xClass_pow]
      apply S.mul_mem
      · change algebraMap SpecialField SpecialRing a ∈ S
        exact S.algebraMap_mem a
      · exact S.pow_mem
          (Algebra.subset_adjoin
            (Set.mem_insert
              (N13GoodCoordinateRingTwo.xClass X)
              {N13GoodCoordinateRingTwo.yClass}))
          n

/-- The special affine coordinate ring is generated by its literal
coordinates. -/
theorem coordinate_adjoin_eq_top :
    Algebra.adjoin SpecialField
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) =
      ⊤ := by
  apply Algebra.eq_top_iff.2
  intro z
  obtain ⟨p, rfl⟩ :=
    AdjoinRoot.mk_surjective z
  let S : Subalgebra SpecialField SpecialRing :=
    Algebra.adjoin SpecialField
      ({N13GoodCoordinateRingTwo.xClass X,
        N13GoodCoordinateRingTwo.yClass} :
        Set SpecialRing)
  change N13GoodCoordinateRingTwo.mk p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      change
        N13GoodCoordinateRingTwo.xClass a *
            N13GoodCoordinateRingTwo.yClass ^ n ∈ S
      apply S.mul_mem
      · exact xClass_mem_coordinateAdjoin a
      · exact S.pow_mem
          (Algebra.subset_adjoin
            (Set.mem_insert_iff.mpr
              (Or.inr
                (Set.mem_singleton
                  N13GoodCoordinateRingTwo.yClass))))
          n

/-- Every quotient of the special affine coordinate ring is still generated
by the images of its literal coordinates. -/
theorem quotient_coordinate_adjoin_eq_top
    (I : Ideal SpecialRing) :
    Algebra.adjoin SpecialField
        ({Ideal.Quotient.mk I
            (N13GoodCoordinateRingTwo.xClass X),
          Ideal.Quotient.mk I
            N13GoodCoordinateRingTwo.yClass} :
          Set (SpecialRing ⧸ I)) =
      ⊤ := by
  let π : SpecialRing →ₐ[SpecialField] SpecialRing ⧸ I :=
    Ideal.Quotient.mkₐ SpecialField I
  rw [show
    ({Ideal.Quotient.mk I
        (N13GoodCoordinateRingTwo.xClass X),
      Ideal.Quotient.mk I
        N13GoodCoordinateRingTwo.yClass} :
      Set (SpecialRing ⧸ I)) =
      π ''
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) by
    exact
      (Set.image_pair π
        (N13GoodCoordinateRingTwo.xClass X)
        N13GoodCoordinateRingTwo.yClass).symm]
  rw [← AlgHom.map_adjoin, coordinate_adjoin_eq_top,
    Algebra.map_top, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective

end

end MazurProof.N13TwoGeneratorFiberBasis


end


