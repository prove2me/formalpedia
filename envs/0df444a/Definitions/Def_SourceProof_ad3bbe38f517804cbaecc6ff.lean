-- Prove2me | Definitions.Def_SourceProof_ad3bbe38f517804cbaecc6ff
-- name    : SourceProof_ad3bbe38f517804cbaecc6ff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:10:53.573255+00:00
-- url     : https://prove2.me/theorems/047db6b5-c3a5-4757-bf94-f7e67517cd16
-- title:
--   LevyStochCalc source module: SourceProof_ad3bbe38f517804cbaecc6ff
-- statement:
--   The original source theorem `LevyStochCalc.Probability.summable_norm_charlierScaled` comes from the `LevyStochCalc.Probability.CharlierGenerating` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_ad3bbe38f517804cbaecc6ff (lam : ℝ) (n : ℕ) (t : ℂ) :
    Summable fun s : ℕ => ‖t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ)‖ := by
  induction n with
  | zero =>
    have h : ∀ s : ℕ, ‖t ^ s / (s.factorial : ℂ) * (LevyStochCalc.Probability.charlierScaled s lam ((0 : ℕ) : ℝ) : ℂ)‖
        = ‖-(lam : ℂ) * t‖ ^ s / (s.factorial : ℝ) := by
      intro s
      have hs : t ^ s / (s.factorial : ℂ) * (LevyStochCalc.Probability.charlierScaled s lam ((0 : ℕ) : ℝ) : ℂ)
          = (-(lam : ℂ) * t) ^ s / (s.factorial : ℂ) := by
        rw [Nat.cast_zero, LevyStochCalc.Probability.charlierScaled_zero_arg]
        push_cast
        rw [mul_pow]
        ring
      rw [hs, norm_div, norm_pow, Complex.norm_natCast]
    rw [funext h]
    exact (NormedSpace.expSeries_div_hasSum_exp ‖-(lam : ℂ) * t‖).summable
  | succ n ih =>
    have hshift : Summable fun s : ℕ =>
        ‖t‖ * (if s = 0 then 0 else ‖t ^ (s - 1) / ((s - 1).factorial : ℂ)
          * (LevyStochCalc.Probability.charlierScaled (s - 1) lam (n : ℝ) : ℂ)‖) := by
      refine (Function.Injective.summable_iff add_one_injective ?_).mp ?_
      · intro m hm
        have hm0 : m = 0 := by
          by_contra hne
          refine hm (Set.mem_range.mpr ⟨m - 1, ?_⟩)
          show m - 1 + 1 = m
          omega
        subst hm0
        rw [if_pos rfl, mul_zero]
      · exact ih.mul_left ‖t‖
    refine Summable.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => ?_) (ih.add hshift)
    cases s with
    | zero => simp
    | succ m =>
      have hd := _root_.Prove2MeSourceProof.h_6e9f626cac2025a847c81060 m lam (n : ℝ)
      have hrec : LevyStochCalc.Probability.charlierScaled (m + 1) lam ((n : ℝ) + 1)
          = LevyStochCalc.Probability.charlierScaled (m + 1) lam (n : ℝ)
            + ((m : ℝ) + 1) * LevyStochCalc.Probability.charlierScaled m lam (n : ℝ) := by linarith [hd]
      have hcast : (((n + 1 : ℕ) : ℝ)) = ((n : ℝ) + 1) := by push_cast; ring
      have hsplit : t ^ (m + 1) / ((m + 1).factorial : ℂ)
            * (LevyStochCalc.Probability.charlierScaled (m + 1) lam ((n + 1 : ℕ) : ℝ) : ℂ)
          = t ^ (m + 1) / ((m + 1).factorial : ℂ)
              * (LevyStochCalc.Probability.charlierScaled (m + 1) lam (n : ℝ) : ℂ)
            + t * (t ^ m / (m.factorial : ℂ) * (LevyStochCalc.Probability.charlierScaled m lam (n : ℝ) : ℂ)) := by
        rw [hcast, hrec]
        have hf : (((m + 1).factorial : ℕ) : ℂ) = ((m : ℂ) + 1) * (m.factorial : ℂ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have h0 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
        have h1 : ((m : ℂ) + 1) ≠ 0 := by
          have hc : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [hc, Ne, Nat.cast_eq_zero]
          omega
        rw [hf]
        push_cast
        field_simp
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero m), norm_mul]
      exact le_refl _
end LevyStochCalc.Probability


