-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CurveModel_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CurveModel_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:48:59.83728+00:00
-- url     : https://prove2.me/theorems/e3a19d8b-05ab-4b3c-bed0-d4926a558cf6
-- title:
--   FLT.Assumptions.MazurProof.N13CurveModel source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CurveModel

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CurveModel
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TateBridge_p0

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


