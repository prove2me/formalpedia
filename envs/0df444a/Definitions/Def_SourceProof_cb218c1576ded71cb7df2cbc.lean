-- Prove2me | Definitions.Def_SourceProof_cb218c1576ded71cb7df2cbc
-- name    : SourceProof_cb218c1576ded71cb7df2cbc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:11:11.752912+00:00
-- url     : https://prove2.me/theorems/ddfdea71-aea1-41e1-9190-b245bfd1f01e
-- title:
--   LevyStochCalc source module: SourceProof_cb218c1576ded71cb7df2cbc
-- statement:
--   The original source theorem `LevyStochCalc.Probability.hasSum_charlierScaled` comes from the `LevyStochCalc.Probability.CharlierGenerating` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Probability_CharlierGenerating_F000
import Definitions.Def_SourceProof_6e9f626cac2025a847c81060

open private add_one_injective from Definitions.Def_LevyStochCalc_Probability_CharlierGenerating_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generating function of the Charlier polynomials

At a natural argument `n` the Charlier polynomials with parameter `lam` (the mean of the Poisson
law that makes them orthogonal) are generated over `ℂ` by
`e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)`, obtained by induction on `n`: the value
`C_s(0; lam) = (-lam) ^ s` matches the exponential series at `n = 0`, and the forward difference
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)` turns the step into an index shift, which on the
generating side multiplies by `1 + t`. The same induction, run on the bound
`|T_(s+1)(n + 1)| ≤ |T_(s+1)(n)| + |t| |T_s(n)|` for the terms `T_s(n) = (t ^ s / s!) C_s(n; lam)`
and started from the exponential series at `n = 0`, shows that the series is absolutely summable
at every natural argument.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_zero_arg` — `C_s(0; lam) = (-lam) ^ s`.
* `LevyStochCalc.Probability.hasSum_charlierScaled` —
  `e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_charlierScaled` — absolute summability of
  `t ^ s / s! · C_s(n; lam)` at every natural argument.
-/

namespace LevyStochCalc.Probability

open Finset


theorem _root_.Prove2MeSourceProof.h_cb218c1576ded71cb7df2cbc (lam : ℝ) (n : ℕ) (t : ℂ) :
    HasSum (fun s : ℕ => t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ))
      (Complex.exp (-(lam * t)) * (1 + t) ^ n) := by
  induction n with
  | zero =>
    have h : ∀ s : ℕ, t ^ s / (s.factorial : ℂ) * (LevyStochCalc.Probability.charlierScaled s lam ((0 : ℕ) : ℝ) : ℂ)
        = (-(lam : ℂ) * t) ^ s / (s.factorial : ℂ) := by
      intro s
      rw [Nat.cast_zero, LevyStochCalc.Probability.charlierScaled_zero_arg]
      push_cast
      rw [mul_pow]
      ring
    rw [funext h]
    simp only [pow_zero, mul_one]
    rw [show -((lam : ℂ) * t) = -(lam : ℂ) * t by ring, Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  | succ n ih =>
    have hshift : HasSum
        (fun s : ℕ => t ^ s / (s.factorial : ℂ) * ((s : ℂ) * (LevyStochCalc.Probability.charlierScaled (s - 1) lam n : ℂ)))
        (t * (Complex.exp (-(lam * t)) * (1 + t) ^ n)) := by
      refine (Function.Injective.hasSum_iff add_one_injective ?_).mp ?_
      · intro m hm
        have hm0 : m = 0 := by
          by_contra hne
          refine hm (Set.mem_range.mpr ⟨m - 1, ?_⟩)
          show m - 1 + 1 = m
          omega
        simp [hm0]
      · have key : ∀ s : ℕ,
            ((fun s : ℕ => t ^ s / (s.factorial : ℂ)
                * ((s : ℂ) * (LevyStochCalc.Probability.charlierScaled (s - 1) lam n : ℂ)))
              ∘ (fun s : ℕ => s + 1)) s
              = t * (t ^ s / (s.factorial : ℂ) * (LevyStochCalc.Probability.charlierScaled s lam n : ℂ)) := by
          intro s
          simp only [Function.comp_apply, Nat.add_sub_cancel]
          have hf : ((s + 1).factorial : ℂ) = ((s : ℂ) + 1) * (s.factorial : ℂ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          have h0 : ((s.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
          have h1 : ((s : ℂ) + 1) ≠ 0 := by
            have : ((s : ℂ) + 1) = ((s + 1 : ℕ) : ℂ) := by push_cast; ring
            rw [this, Ne, Nat.cast_eq_zero]
            omega
          rw [hf]
          push_cast
          field_simp
          ring
        rw [funext key]
        exact ih.mul_left t
    have hsum := ih.add hshift
    have hterm : ∀ s : ℕ,
        t ^ s / (s.factorial : ℂ) * (LevyStochCalc.Probability.charlierScaled s lam n : ℂ)
          + t ^ s / (s.factorial : ℂ) * ((s : ℂ) * (LevyStochCalc.Probability.charlierScaled (s - 1) lam n : ℂ))
          = t ^ s / (s.factorial : ℂ) * (LevyStochCalc.Probability.charlierScaled s lam ((n : ℝ) + 1) : ℂ) := by
      intro s
      cases s with
      | zero => simp
      | succ m =>
        have hd := _root_.Prove2MeSourceProof.h_6e9f626cac2025a847c81060 m lam (n : ℝ)
        have : LevyStochCalc.Probability.charlierScaled (m + 1) lam ((n : ℝ) + 1)
            = LevyStochCalc.Probability.charlierScaled (m + 1) lam (n : ℝ)
              + ((m : ℝ) + 1) * LevyStochCalc.Probability.charlierScaled m lam (n : ℝ) := by
          linarith [hd]
        rw [this]
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
    rw [funext hterm] at hsum
    have hval : Complex.exp (-(lam * t)) * (1 + t) ^ n
        + t * (Complex.exp (-(lam * t)) * (1 + t) ^ n)
        = Complex.exp (-(lam * t)) * (1 + t) ^ (n + 1) := by
      rw [pow_succ]
      ring
    rw [hval] at hsum
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hsum
    exact hsum
end LevyStochCalc.Probability


