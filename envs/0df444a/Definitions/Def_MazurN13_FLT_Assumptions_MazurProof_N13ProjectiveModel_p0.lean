-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ProjectiveModel_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ProjectiveModel_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:34:47.054987+00:00
-- url     : https://prove2.me/theorems/4bcba0e2-391f-4684-a24d-110763a1ff18
-- title:
--   FLT.Assumptions.MazurProof.N13ProjectiveModel source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ProjectiveModel

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ProjectiveModel
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ArithmeticBasics_p0
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

set_option autoImplicit false




set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazurProof.N13Arithmetic

/-- Rational affine points on the sextic model. -/
abbrev AffinePoint13 :=
  {xy : ℚ × ℚ // N13CurveModel.C13SexticEq xy.1 xy.2}

/-- The point encoding specified in the N13 arithmetic interface. -/
abbrev Point13 := AffinePoint13 ⊕ Bool

/-- Include an affine point in the projective point encoding. -/
def affine13 (X Y : ℚ) (h : N13CurveModel.C13SexticEq X Y) : Point13 :=
  Sum.inl ⟨(X, Y), h⟩

/-- The first infinity tag. -/
def O : Point13 := Sum.inr false

/-- The second infinity tag. -/
def T : Point13 := Sum.inr true

/-- Sextic point (0,-1); optimized point (-1,-1). -/
def D : Point13 :=
  affine13 0 (-1)
    (N13CurveModel.affine_cusp_mem (Or.inl rfl) (Or.inr rfl))

/-- Sextic point (-1,1); optimized point (0,0). -/
def A : Point13 :=
  affine13 (-1) 1
    (N13CurveModel.affine_cusp_mem (Or.inr rfl) (Or.inl rfl))

/-- Sextic point (-1,-1); optimized point (0,-1). -/
def B : Point13 :=
  affine13 (-1) (-1)
    (N13CurveModel.affine_cusp_mem (Or.inr rfl) (Or.inr rfl))

/-- Sextic point (0,1); optimized point (-1,0). -/
def C : Point13 :=
  affine13 0 1
    (N13CurveModel.affine_cusp_mem (Or.inl rfl) (Or.inl rfl))

/-- The six cusps, in the required order [O,T,D,A,B,C]. -/
def cusp13 (i : Fin 6) : Point13 :=
  match i.val with
  | 0 => O
  | 1 => T
  | 2 => D
  | 3 => A
  | 4 => B
  | _ => C

/-- An integer polynomial certificate for the characteristic-two affine
Jacobian calculation. This identity itself holds in every commutative ring.
The final summand vanishes in characteristic two. -/
theorem optimized_char_two_affine_certificate
    {K : Type*} [CommRing K] (u v : K) :
    u ^ 2 =
      u ^ 4 *
          (v ^ 2 + (u ^ 3 + u ^ 2 + 1) * v - (u ^ 2 + u)) -
        (u ^ 2 * v + 1) ^ 2 +
        (u ^ 3 + 1 - u ^ 4 * v) * (u ^ 3 + u ^ 2 + 1) +
        2 * (u ^ 2 * v - u ^ 3) := by
  ring

/-- A06: the two affine partial derivatives cannot vanish simultaneously
at a point of the optimized N13 curve in characteristic two. -/
theorem optimized_char_two_nonsingular
    {K : Type*} [Field K] [CharP K 2] (u v : K)
    (h : OptEquation13 u v) :
    u ^ 3 + u ^ 2 + 1 ≠ 0 ∨ u ^ 2 * v + 1 ≠ 0 := by
  classical
  by_cases hdu : u ^ 3 + u ^ 2 + 1 = 0
  · right
    intro hdv
    have heq :
        v ^ 2 + (u ^ 3 + u ^ 2 + 1) * v - (u ^ 2 + u) = 0 := by
      exact sub_eq_zero.mpr h
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hu2 : u ^ 2 = 0 := by
      have hc := optimized_char_two_affine_certificate u v
      rw [heq, hdv, hdu, htwo] at hc
      simpa only [mul_zero, zero_mul,
        zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self, add_zero] using hc
    have hone : (1 : K) = 0 := by
      simpa only [hu2, zero_mul, zero_add] using hdv
    exact one_ne_zero hone
  · exact Or.inl hdu

/-- A07: In characteristic two, the derivative with respect to w of
w^2 + (1 + s + s^3) * w, specialized at s = 0, is 1.
The displayed algebraic identity is valid for every w. -/
theorem infinity_chart_derivative_two
    {K : Type*} [Field K] [CharP K 2] (w : K) :
    2 * w + 1 = (1 : K) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [h2, zero_mul, zero_add]

/-- A08: the six displayed cusps are pairwise distinct. -/
theorem cusp13_injective : Function.Injective cusp13 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

end MazurProof.N13Arithmetic


