-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Mumford_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13Mumford_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:54:30.103881+00:00
-- url     : https://prove2.me/theorems/a971b669-7b10-4ff4-8702-15094dc0bd59
-- title:
--   FLT.Assumptions.MazurProof.N13Mumford source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13Mumford

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13Mumford
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CurveModel_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumford_p0

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


