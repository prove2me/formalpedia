-- Prove2me | Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_Asymptotics
-- name    : Cslib_254e30e_Foundations_Data_Nat_Asymptotics
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:16.328197+00:00
-- url     : https://prove2.me/theorems/60f9119f-46bb-470d-8536-72b6aaa4def8
-- title:
--   Cslib.Foundations.Data.Nat.Asymptotics — Asymptotic bounds on natural numbers
-- statement:
--   This is module `Cslib.Foundations.Data.Nat.Asymptotics` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   For any natural base greater than one, exponentials eventually dominate fixed multiples of
--   powers, and fixed multiples of logarithms are eventually at most the input. The inequalities
--   are stated in `ℕ`; the polynomial bound specializes Mathlib's
--   `isLittleO_pow_const_const_pow_of_one_lt`.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_Asymptotics`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Foundations/Data/Nat/Asymptotics.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Foundations.Data.Nat.Asymptotics` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Asymptotic bounds on natural numbers

For any natural base greater than one, exponentials eventually dominate fixed multiples of
powers, and fixed multiples of logarithms are eventually at most the input. The inequalities
are stated in `ℕ`; the polynomial bound specializes Mathlib's
`isLittleO_pow_const_const_pow_of_one_lt`.
-/

public section

open Filter

namespace Nat

/-- Every fixed multiple of a power is eventually at most an exponential of base greater
than one. -/
theorem eventually_mul_pow_le_pow (c k : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, c * n ^ k ≤ b ^ n := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have h := Asymptotics.isLittleO_iff_nat_mul_le.mp
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k hbR) c
  filter_upwards [h] with n hn
  exact_mod_cast (by simpa using hn : (c : ℝ) * n ^ k ≤ (b : ℝ) ^ n)

/-- The quotient of an exponential of base greater than one by the input is eventually
at least the input plus one. -/
theorem eventually_add_one_le_pow_div {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, n + 1 ≤ b ^ n / n := by
  filter_upwards [eventually_mul_pow_le_pow 2 2 hb, eventually_ge_atTop 1] with n hn hn0
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  nlinarith

/-- Every fixed multiple of the logarithm in a base greater than one is eventually at most
the input. -/
theorem eventually_mul_log_le (c : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, c * log b n ≤ n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_mul_pow_le_pow c 1 hb)
  filter_upwards [eventually_ge_atTop (b ^ N)] with n hn
  have hn0 : n ≠ 0 := ne_of_gt ((pow_pos (by omega) N).trans_le hn)
  have hh : c * log b n ≤ b ^ log b n := by
    simpa using hN (log b n) (le_log_of_pow_le hb hn)
  exact hh.trans (pow_log_le_self b hn0)

/-- Every fixed multiple of the binary logarithm is eventually at most the input. -/
theorem eventually_mul_log2_le (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, c * log2 n ≤ n := by
  simpa only [log2_eq_log_two] using eventually_mul_log_le c one_lt_two

end Nat


