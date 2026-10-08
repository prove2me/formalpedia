-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNFDivision_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_TateNFDivision_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:44:42.971137+00:00
-- url     : https://prove2.me/theorems/d20a4e4b-4f26-49f1-8cc7-ab807ca469ad
-- title:
--   FLT.Assumptions.MazurProof.TateNFDivision source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.TateNFDivision

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TateNFDivision
Original leading source comments and nonproject imports are retained below. -/
import Mathlib

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


