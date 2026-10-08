-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ArithmeticBasics_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ArithmeticBasics_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:33:59.866689+00:00
-- url     : https://prove2.me/theorems/ac9cf7a4-0fe4-40a0-a2f7-9c5a02d242fb
-- title:
--   FLT.Assumptions.MazurProof.N13ArithmeticBasics source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ArithmeticBasics

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ArithmeticBasics
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CurveModel_p0
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

set_option autoImplicit false




set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N13Arithmetic

/-- The optimized N13 affine equation over a commutative coefficient ring. -/
def OptEquation13 {K : Type*} [CommRing K] (u v : K) : Prop :=
  v ^ 2 + (u ^ 3 + u ^ 2 + 1) * v = u ^ 2 + u

/-- Affine solutions together with the two distinct infinity tags. -/
def OptPoint13 (K : Type*) [Field K] :=
  {uv : K × K // OptEquation13 uv.1 uv.2} ⊕ Bool

/-- The polynomial defining the standard sextic model of X₁(13). -/
def F13 (K : Type*) [CommRing K] : Polynomial K :=
  Polynomial.X ^ 6 + 4 * Polynomial.X ^ 5 +
    6 * Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 +
    Polynomial.X ^ 2 + 2 * Polynomial.X + 1

/-- The cubic occurring in the sum-of-squares identity for F13. -/
def A13 (K : Type*) [CommRing K] : Polynomial K :=
  Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 - Polynomial.X - 1

/-- The quadratic occurring in the sum-of-squares identity for F13. -/
def B13 (K : Type*) [CommRing K] : Polynomial K :=
  Polynomial.X * (Polynomial.X + 1)

/-- A03: polynomial evaluation agrees with the existing rational sextic. -/
theorem F13_eval (x : ℚ) :
    (F13 ℚ).eval x = N13CurveModel.sexticF13 x := by
  simp only [F13, N13CurveModel.sexticF13,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]

/-- A01: The sextic is a norm from the quadratic extension obtained by adjoining i. -/
theorem sexticF13_norm_identity (x : ℚ) :
    N13CurveModel.sexticF13 x =
      (x ^ 3 + 2 * x ^ 2 - x - 1) ^ 2 +
        4 * (x * (x + 1)) ^ 2 := by
  unfold N13CurveModel.sexticF13
  ring

/-- A02: In particular, no rational affine point is a hyperelliptic branch point. -/
theorem sexticF13_pos (x : ℚ) :
    0 < N13CurveModel.sexticF13 x := by
  by_cases h : x * (x + 1) = 0
  · rcases mul_eq_zero.mp h with hx | hx
    · subst x
      norm_num [N13CurveModel.sexticF13]
    · have hx' : x = -1 := by linarith
      rw [hx']
      norm_num [N13CurveModel.sexticF13]
  · rw [sexticF13_norm_identity]
    have hA : 0 ≤ (x ^ 3 + 2 * x ^ 2 - x - 1) ^ 2 :=
      sq_nonneg _
    have hB : 0 < (x * (x + 1)) ^ 2 :=
      sq_pos_of_ne_zero h
    nlinarith

/-- A05: Over a commutative ring containing a square root of -1, the sextic
factors as the product of the two indicated cubics. -/
theorem F13_quadratic_factorization
    {K : Type*} [CommRing K] (i : K) (hi : i ^ 2 = -1) :
    F13 K =
      (A13 K + Polynomial.C (2 * i) * B13 K) *
      (A13 K - Polynomial.C (2 * i) * B13 K) := by
  have hsq : (2 * i) ^ 2 = (-4 : K) := by
    calc
      (2 * i) ^ 2 = 4 * i ^ 2 := by ring
      _ = -4 := by
        rw [hi]
        ring
  have hC : (Polynomial.C (2 * i) : Polynomial K) ^ 2 = -4 := by
    simpa only [Polynomial.C_pow, map_neg, Polynomial.C_ofNat] using
      congrArg (fun a : K => (Polynomial.C a : Polynomial K)) hsq
  calc
    F13 K = A13 K ^ 2 + 4 * B13 K ^ 2 := by
      unfold F13 A13 B13
      ring
    _ = A13 K ^ 2 -
        (Polynomial.C (2 * i) : Polynomial K) ^ 2 * B13 K ^ 2 := by
      rw [hC]
      ring
    _ = (A13 K + Polynomial.C (2 * i) * B13 K) *
        (A13 K - Polynomial.C (2 * i) * B13 K) := by
      ring

end MazurProof.N13Arithmetic


