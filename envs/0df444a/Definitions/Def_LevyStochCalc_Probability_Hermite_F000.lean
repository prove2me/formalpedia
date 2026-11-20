-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Hermite_F000
-- name    : LevyStochCalc_Probability_Hermite_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:29:24.65818+00:00
-- url     : https://prove2.me/theorems/941cc819-e18d-4125-9ced-6f07cbb9d87c
-- title:
--   Source declarations: LevyStochCalc.Probability.Hermite
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.Hermite. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_GaussianMoments_F000
import Definitions.Def_SourceProof_b6e0ed871fbe873258573769
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Hermite polynomials of variance `v` and their Gaussian orthogonality

The probabilists' Hermite polynomials of variance `v` are given by the Appell recursion
`H_(n+1) = (x - v d/dx) H_n`, which makes the derivative `H_(n+1)' = (n+1) H_n` and the three-term
recursion `H_(n+2) = x H_(n+1) - (n+1) v H_n` immediate. For `v > 0` they rescale Mathlib's
family `Polynomial.hermite` by `H_n(x; v) = √v ^ n * He_n(x / √v)`, and `H_2(x; v) = x ^ 2 - v`.
Under the law `gaussianReal 0 v` they are orthogonal, with `E[H_n H_m] = δ_(n m) n! v ^ n`.

The opening section adds the derivative and the three-term recursion of Mathlib's
`Polynomial.hermite`, both of which belong with `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`.

## Main statements

* `Polynomial.derivative_hermite` — `He_(n+1)' = (n+1) He_n`.
* `Polynomial.hermite_succ_succ` — `He_(n+2) = X He_(n+1) - (n+1) He_n`.
* `LevyStochCalc.Probability.derivative_hermitePoly` — `H_(n+1)' = (n+1) H_n`.
* `LevyStochCalc.Probability.hermitePoly_succ_succ` — `H_(n+2) = X H_(n+1) - (n+1) v H_n`.
* `LevyStochCalc.Probability.hermiteScaled_two` — `H_2(x; v) = x ^ 2 - v`.
* `LevyStochCalc.Probability.hermiteScaled_eq` — `H_n(x; v) = √v ^ n * He_n(x / √v)` for `v > 0`.
* `LevyStochCalc.Probability.integral_hermitePoly_mul` — `E[H_n H_m] = δ_(n m) n! v ^ n`.
-/

namespace Polynomial

/-- The derivative of a probabilists' Hermite polynomial. -/
theorem derivative_hermite (n : ℕ) :
    derivative (hermite (n + 1)) = C ((n : ℤ) + 1) * hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_C_mul, hermite_succ n]
    push_cast
    simp only [C_add, C_1]
    ring
/-- The three-term recursion for the probabilists' Hermite polynomials. -/
theorem hermite_succ_succ (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - C ((n : ℤ) + 1) * hermite n := by
  rw [hermite_succ (n + 1), derivative_hermite n]
end Polynomial

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

/-- The probabilists' Hermite polynomial of variance `τ`, given by the Appell recursion
`H_(n+1) = (x - τ d/dx) H_n`. -/
noncomputable def hermitePoly (τ : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | (n + 1) => X * hermitePoly τ n - C τ * derivative (hermitePoly τ n)
@[simp] theorem hermitePoly_zero (τ : ℝ) : hermitePoly τ 0 = 1 := rfl
theorem hermitePoly_succ (τ : ℝ) (n : ℕ) :
    hermitePoly τ (n + 1) = X * hermitePoly τ n - C τ * derivative (hermitePoly τ n) := rfl
@[simp] theorem hermitePoly_one (τ : ℝ) : hermitePoly τ 1 = X := by
  rw [hermitePoly_succ]; simp
/-- The derivative of the Hermite polynomial of variance `τ`. -/
theorem derivative_hermitePoly (τ : ℝ) (n : ℕ) :
    derivative (hermitePoly τ (n + 1)) = C ((n : ℝ) + 1) * hermitePoly τ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermitePoly_succ τ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih]
    simp only [derivative_C_mul]
    rw [hermitePoly_succ τ n]
    push_cast
    simp only [C_add, C_1]
    ring
/-- The three-term recursion `H_(n+2) = x H_(n+1) - (n+1) τ H_n`. -/
theorem hermitePoly_succ_succ (τ : ℝ) (n : ℕ) :
    hermitePoly τ (n + 2)
      = X * hermitePoly τ (n + 1) - C (((n : ℝ) + 1) * τ) * hermitePoly τ n := by
  rw [hermitePoly_succ τ (n + 1), derivative_hermitePoly τ n, C_mul]
  ring
/-- The value `H_n(x; τ)` of the Hermite polynomial of variance `τ`. -/
noncomputable def hermiteScaled (n : ℕ) (τ x : ℝ) : ℝ := (hermitePoly τ n).eval x
@[simp] theorem hermiteScaled_zero (τ x : ℝ) : hermiteScaled 0 τ x = 1 := by
  simp [hermiteScaled]
@[simp] theorem hermiteScaled_one (τ x : ℝ) : hermiteScaled 1 τ x = x := by
  simp [hermiteScaled]
theorem hermiteScaled_succ_succ (n : ℕ) (τ x : ℝ) :
    hermiteScaled (n + 2) τ x
      = x * hermiteScaled (n + 1) τ x - ((n : ℝ) + 1) * τ * hermiteScaled n τ x := by
  simp [hermiteScaled, hermitePoly_succ_succ]
/-- The Hermite polynomial of degree two, `H_2(x; τ) = x ^ 2 - τ`. -/
theorem hermiteScaled_two (τ x : ℝ) : hermiteScaled 2 τ x = x ^ 2 - τ := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, hermiteScaled_succ_succ]
  simp; ring
/-- The Hermite polynomial of variance `τ` rescales the probabilists' Hermite polynomial,
`H_n(x; τ) = √τ ^ n * He_n(x / √τ)`. -/
theorem hermiteScaled_eq (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    hermiteScaled n τ x = Real.sqrt τ ^ n * aeval (x / Real.sqrt τ) (hermite n) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ τ = s ^ 2 :=
    ⟨Real.sqrt τ, Real.sqrt_pos.mpr hτ, (Real.sq_sqrt hτ.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp; field_simp
  | more n ih1 ih2 =>
    rw [hermiteScaled_succ_succ, ih2, ih1, hermite_succ_succ]
    simp only [map_sub, map_mul, aeval_X, map_intCast, eq_intCast]
    push_cast
    field_simp
    ring
/-- One step of the Hermite recursion under a centred real Gaussian law. -/
theorem integral_hermite_step (v : ℝ≥0) (p q : ℝ[X]) :
    ∫ x, (x * p.eval x - (v : ℝ) * (derivative p).eval x) * q.eval x ∂gaussianReal 0 v
      = (v : ℝ) * ∫ x, p.eval x * (derivative q).eval x ∂gaussianReal 0 v := by
  have hA : Integrable (fun x : ℝ => (derivative p * q).eval x) (gaussianReal 0 v) :=
    integrable_eval_gaussianReal v _
  have hB : Integrable (fun x : ℝ => (p * derivative q).eval x) (gaussianReal 0 v) :=
    integrable_eval_gaussianReal v _
  have h1 : Integrable (fun x : ℝ => x * (p * q).eval x) (gaussianReal 0 v) := by
    have h := integrable_eval_gaussianReal v (X * (p * q))
    simpa only [eval_mul, eval_X] using h
  have h2 : Integrable (fun x : ℝ => (v : ℝ) * (derivative p * q).eval x) (gaussianReal 0 v) :=
    hA.const_mul _
  have e : ∀ x : ℝ, (x * p.eval x - (v : ℝ) * (derivative p).eval x) * q.eval x
      = x * (p * q).eval x - (v : ℝ) * (derivative p * q).eval x := by
    intro x; simp only [eval_mul]; ring
  simp_rw [e]
  rw [integral_sub h1 h2, _root_.Prove2MeSourceProof.h_b6e0ed871fbe873258573769 v (p * q), derivative_mul]
  simp_rw [eval_add]
  rw [integral_add hA hB, integral_const_mul]
  simp only [eval_mul]
  ring
end LevyStochCalc.Probability


