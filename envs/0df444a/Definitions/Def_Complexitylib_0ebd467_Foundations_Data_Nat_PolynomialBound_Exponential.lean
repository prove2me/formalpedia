-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_PolynomialBound_Exponential
-- name    : Complexitylib_0ebd467_Foundations_Data_Nat_PolynomialBound_Exponential
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:41.728749+00:00
-- url     : https://prove2.me/theorems/1083134a-cf76-4a0c-b40c-a30bbc56a070
-- title:
--   Complexity.Foundations.Data.Nat.PolynomialBound.Exponential — Polynomial bounds are eventually below exponentials
-- statement:
--   This is module `Complexity.Foundations.Data.Nat.PolynomialBound.Exponential` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A polynomially bounded function is eventually smaller than `2 ^ n`
--   (`PolynomiallyBounded.eventually_lt_two_pow`): exponential lower bounds rule out polynomial upper
--   bounds. Summing the finitely many exceptions, it is bounded everywhere by a constant multiple of
--   `2 ^ n` (`PolynomiallyBounded.exists_le_mul_two_pow`).
--
--   ### Main results
--
--   * `Cslib.PolynomiallyBounded.eventually_lt_two_pow`.
--   * `Cslib.PolynomiallyBounded.exists_le_mul_two_pow`.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_PolynomialBound_Exponential`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/Nat/PolynomialBound/Exponential.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_PolynomialBound
import Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/- Prove2me definition bundle for `Complexity.Foundations.Data.Nat.PolynomialBound.Exponential` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial bounds are eventually below exponentials

A polynomially bounded function is eventually smaller than `2 ^ n`
(`PolynomiallyBounded.eventually_lt_two_pow`): exponential lower bounds rule out polynomial upper
bounds. Summing the finitely many exceptions, it is bounded everywhere by a constant multiple of
`2 ^ n` (`PolynomiallyBounded.exists_le_mul_two_pow`).

## Main results

* `Cslib.PolynomiallyBounded.eventually_lt_two_pow`.
* `Cslib.PolynomiallyBounded.exists_le_mul_two_pow`.
-/

@[expose] public section

namespace Cslib.PolynomiallyBounded

open Filter

/-- **A polynomially bounded function is eventually below `2 ^ n`.** -/
theorem eventually_lt_two_pow {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∀ᶠ n in atTop, f n < 2 ^ n := by
  obtain ⟨d, hd⟩ := hf
  filter_upwards [hd, Nat.eventually_mul_pow_le_pow 2 d one_lt_two, eventually_ge_atTop 1]
    with n hn hpow hn1
  have := Nat.pow_pos (n := d) hn1
  omega

/-- A polynomially bounded function is bounded by a constant multiple of `2 ^ n`. -/
theorem exists_le_mul_two_pow {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    ∃ C, ∀ n, p n ≤ C * 2 ^ n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp.eventually_lt_two_pow
  refine ⟨∑ m ∈ Finset.range N, p m + 1, fun n => ?_⟩
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases le_or_gt N n with hn | hn
  · exact (hN n hn).le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  · have := Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
    exact this.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hpow))

end Cslib.PolynomiallyBounded


