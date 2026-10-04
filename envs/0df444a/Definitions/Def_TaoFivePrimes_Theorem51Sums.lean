-- Prove2me | Definitions.Def_TaoFivePrimes_Theorem51Sums
-- name    : TaoFivePrimes_Theorem51Sums
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-12T17:03:20.640429+00:00
-- url     : https://prove2.me/theorems/0638cceb-6d09-4432-b62a-48c625773961
-- title:
--   Concrete Type I and Type II sums for Tao Theorem 5.1
-- statement:
--   For positive real parameters x,U,V and a phase α, this interface defines the positive odd divisor set d≤UV, the Type I sum with amplitudes (log n+c_d log d)η₀(dn/x), and the Type II bilinear sum with d>U, w>V and centered coefficient g(w)=∑_{b∣w,b>V}Λ(b)−(log w)/2. Odd n in Type I are parametrized by 2j+1, j∈ℤ; nonpositive arguments contribute zero through η₀. All sums, estimates, and the Vaughan decomposition retain separate proof obligations; this file contains definitions only.
-- source:
--   Terence Tao, arXiv:1201.6656v4, Lemma 4.11, equation (4.19), and the Type I/II displays in Section 5 immediately preceding (5.8). https://arxiv.org/html/1201.6656v4#S5

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Algebra.Order.Floor.Semiring

/-! Concrete Type I and Type II sums from Tao, arXiv:1201.6656v4,
Lemma 4.11 and Section 5, immediately before (5.8).
Only definitions are provided here; all estimates and the Vaughan
decomposition are separate proof obligations. -/

namespace TaoFivePrimes
open Finset

/-- Positive odd divisor indices at most UV. -/
noncomputable def theorem51Divisors (U V : ℝ) : Finset ℕ :=
  (Icc 1 ⌊U * V⌋₊).filter (fun d => d.Coprime 2)

/-- Type I envelope, with odd integers parametrized by 2n+1. -/
noncomputable def theorem51TypeI (x alpha U V : ℝ) (c : ℕ → ℂ) : ℝ :=
  ∑ d ∈ theorem51Divisors U V, ‖∑' n : ℤ,
    (((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + c d * (Real.log d : ℂ)) *
      (eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) : ℂ)) *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖

/-- Centered von Mangoldt divisor coefficient, equation (4.19). -/
noncomputable def theorem51Centered (V : ℝ) (w : ℕ) : ℝ :=
  (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
    ArithmeticFunction.vonMangoldt b) - Real.log w / 2

/-- The literal smoothed bilinear Type II sum. The cutoff eta0 makes
the summation finite in the positive parameter regime. -/
noncomputable def theorem51TypeII (x alpha U V : ℝ) : ℝ :=
  ‖∑' d : ℕ, ∑' w : ℕ,
    if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
      (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
        expCircle (alpha * d * w) * (eta0 ((d : ℝ) * w / x) : ℂ)
    else 0‖

end TaoFivePrimes


