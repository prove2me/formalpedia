-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Log
-- name    : Complexitylib_0ebd467_Foundations_Data_Nat_Log
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:58.254482+00:00
-- url     : https://prove2.me/theorems/5074634f-5ce6-4fcb-8f90-ed6aa68e2087
-- title:
--   Complexity.Foundations.Data.Nat.Log — Powers with logarithmic exponents
-- statement:
--   This is module `Complexity.Foundations.Data.Nat.Log` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The power `b ^ ⌈log_b n⌉` overshoots `n` by less than a factor `b` (`Nat.pow_clog_le_mul`), so
--   `m ^ ⌈log_b n⌉`, which is at most `(b ^ ⌈log_b m⌉) ^ ⌈log_b n⌉ = (b ^ ⌈log_b n⌉) ^ ⌈log_b m⌉`, is
--   at most `b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉` (`Nat.pow_clog_le_pow_clog_mul_pow_clog`): a factor `m`
--   applied `⌈log_b n⌉` times is polynomial in `n`. This is how the size of an iterated construction
--   stays polynomial after logarithmically many rounds. Similarly `2 ^ (⌊log₂ n⌋ + 1)` and
--   `2 ^ ⌈log₂ n⌉` are at most `2 (n + 1)` (`Nat.two_pow_log2_succ_le`, `Nat.two_pow_clog_two_le`).
--
--   ### Main results
--
--   * `Nat.pow_clog_le_mul`: `b ^ ⌈log_b n⌉ ≤ b * n` for `n ≠ 0`.
--   * `Nat.pow_clog_le_pow_clog_mul_pow_clog`: `m ^ ⌈log_b n⌉ ≤ b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉` for
--     `n ≠ 0`.
--   * `Nat.two_pow_log2_succ_le`: `2 ^ (⌊log₂ n⌋ + 1) ≤ 2 (n + 1)`.
--   * `Nat.two_pow_clog_two_le`: `2 ^ ⌈log₂ n⌉ ≤ 2 (n + 1)`, also for `n = 0`.
--   * `Nat.log_add_one_le`: `⌊log_b (n + 1)⌋ ≤ ⌊log_b n⌋ + 1`.
--   * `Nat.mul_log_le_add_sq`: `m * ⌊log_b n⌋ ≤ n + m * m` for `1 < b`.
--   * `Nat.clog_two_le_two_mul_of_le_two_mul`: `⌈log₂ n⌉ ≤ 2 * ⌈log₂ n'⌉` when `n ≤ 2 * n'` and
--     `2 ≤ n'`.
--   * `Nat.clog_two_add_two_le_three_mul_log_two`: `⌈log₂ (n + 2)⌉ ≤ 3 ⌊log₂ n⌋` for `n ≥ 2`.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Log`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/Nat/Log.lean

/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Log.lean`)

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.Nat.Log

/- Prove2me definition bundle for `Complexity.Foundations.Data.Nat.Log` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Powers with logarithmic exponents

The power `b ^ ⌈log_b n⌉` overshoots `n` by less than a factor `b` (`Nat.pow_clog_le_mul`), so
`m ^ ⌈log_b n⌉`, which is at most `(b ^ ⌈log_b m⌉) ^ ⌈log_b n⌉ = (b ^ ⌈log_b n⌉) ^ ⌈log_b m⌉`, is
at most `b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉` (`Nat.pow_clog_le_pow_clog_mul_pow_clog`): a factor `m`
applied `⌈log_b n⌉` times is polynomial in `n`. This is how the size of an iterated construction
stays polynomial after logarithmically many rounds. Similarly `2 ^ (⌊log₂ n⌋ + 1)` and
`2 ^ ⌈log₂ n⌉` are at most `2 (n + 1)` (`Nat.two_pow_log2_succ_le`, `Nat.two_pow_clog_two_le`).

## Main results

* `Nat.pow_clog_le_mul`: `b ^ ⌈log_b n⌉ ≤ b * n` for `n ≠ 0`.
* `Nat.pow_clog_le_pow_clog_mul_pow_clog`: `m ^ ⌈log_b n⌉ ≤ b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉` for
  `n ≠ 0`.
* `Nat.two_pow_log2_succ_le`: `2 ^ (⌊log₂ n⌋ + 1) ≤ 2 (n + 1)`.
* `Nat.two_pow_clog_two_le`: `2 ^ ⌈log₂ n⌉ ≤ 2 (n + 1)`, also for `n = 0`.
* `Nat.log_add_one_le`: `⌊log_b (n + 1)⌋ ≤ ⌊log_b n⌋ + 1`.
* `Nat.mul_log_le_add_sq`: `m * ⌊log_b n⌋ ≤ n + m * m` for `1 < b`.
* `Nat.clog_two_le_two_mul_of_le_two_mul`: `⌈log₂ n⌉ ≤ 2 * ⌈log₂ n'⌉` when `n ≤ 2 * n'` and
  `2 ≤ n'`.
* `Nat.clog_two_add_two_le_three_mul_log_two`: `⌈log₂ (n + 2)⌉ ≤ 3 ⌊log₂ n⌋` for `n ≥ 2`.
-/

@[expose] public section

namespace Nat

variable {b n : ℕ}

/-- The power `b ^ ⌈log_b n⌉` overshoots `n ≠ 0` by less than a factor `b`. -/
theorem pow_clog_le_mul (hb : 1 < b) (hn : n ≠ 0) : b ^ clog b n ≤ b * n := by
  rcases (one_le_iff_ne_zero.2 hn).eq_or_lt with rfl | hn
  · simpa using hb.le
  · have := pow_pred_clog_lt_self hb hn
    rw [← succ_pred_eq_of_pos (clog_pos hb hn), pow_succ']
    exact Nat.mul_le_mul_left _ this.le

/-- A factor `m` applied `⌈log_b n⌉` times is polynomial in `n ≠ 0`:
`m ^ ⌈log_b n⌉ ≤ b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉`. -/
theorem pow_clog_le_pow_clog_mul_pow_clog (hb : 1 < b) (m : ℕ) (hn : n ≠ 0) :
    m ^ clog b n ≤ b ^ clog b m * n ^ clog b m :=
  calc m ^ clog b n ≤ (b ^ clog b m) ^ clog b n := Nat.pow_le_pow_left (le_pow_clog hb m) _
    _ = (b ^ clog b n) ^ clog b m := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (b * n) ^ clog b m := Nat.pow_le_pow_left (pow_clog_le_mul hb hn) _
    _ = b ^ clog b m * n ^ clog b m := Nat.mul_pow _ _ _

/-- `2 ^ (log₂ n + 1)` is at most `2 (n + 1)`. -/
theorem two_pow_log2_succ_le (n : ℕ) : 2 ^ (Nat.log2 n + 1) ≤ 2 * (n + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.mul_le_mul_left 2 ((Nat.log2_self_le hn.ne').trans (Nat.le_succ n))

/-- `2 ^ ⌈log₂ n⌉` is at most `2 (n + 1)`, also for `n = 0`. -/
theorem two_pow_clog_two_le (n : ℕ) : 2 ^ clog 2 n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (pow_clog_le_mul Nat.one_lt_two hn.ne').trans (by omega)

/-- Adding one increases the base-`b` logarithm by at most one:
`⌊log_b (n + 1)⌋ ≤ ⌊log_b n⌋ + 1`. -/
theorem log_add_one_le (b n : ℕ) : log b (n + 1) ≤ log b n + 1 := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
  · have hlt : n < b ^ (log b n + 1) := lt_pow_succ_log_self hb n
    have hpow : 1 * b ^ (log b n + 1) < b * b ^ (log b n + 1) :=
      Nat.mul_lt_mul_of_pos_right hb (Nat.pow_pos (by omega))
    have hlt' : n + 1 < b ^ (log b n + 2) := by
      rw [pow_succ']
      omega
    exact le_of_lt_succ (log_lt_of_lt_pow (Nat.succ_ne_zero n) hlt')

/-- For any base `b > 1` and multiplier `m`, `m * ⌊log_b n⌋ ≤ n + m * m`. -/
theorem mul_log_le_add_sq (hb : 1 < b) (m n : ℕ) : m * log b n ≤ n + m * m := by
  rcases le_or_gt (log b n) m with h | h
  · exact (Nat.mul_le_mul_left m h).trans (Nat.le_add_left _ n)
  · have hpow (k : ℕ) : k ≤ b ^ k :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hb k)
    have hsub : m * (log b n - m) ≤ n :=
      calc m * (log b n - m) ≤ b ^ m * b ^ (log b n - m) :=
            Nat.mul_le_mul (hpow m) (hpow (log b n - m))
        _ = b ^ log b n := by rw [← Nat.pow_add, Nat.add_sub_cancel' h.le]
        _ ≤ n := pow_log_le_self b (by rintro rfl; simp at h)
    have hmul : m * log b n = m * (log b n - m) + m * m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel h.le]
    omega

/-- When `n ≤ 2 * n'` and `2 ≤ n'`, `⌈log₂ n⌉ ≤ 2 * ⌈log₂ n'⌉`. -/
theorem clog_two_le_two_mul_of_le_two_mul {n n' : ℕ} (hn : n ≤ 2 * n') (hn' : 2 ≤ n') :
    clog 2 n ≤ 2 * clog 2 n' := by
  have h1 : 1 ≤ clog 2 n' := (lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega : 2 ^ 0 < n')
  have h2 : n ≤ 2 ^ (clog 2 n' + 1) :=
    calc n ≤ 2 * n' := hn
      _ ≤ 2 * 2 ^ clog 2 n' := Nat.mul_le_mul_left 2 (le_pow_clog Nat.one_lt_two n')
      _ = 2 ^ (clog 2 n' + 1) := Nat.pow_succ'.symm
  have h3 : clog 2 n ≤ clog 2 n' + 1 := (clog_le_iff_le_pow Nat.one_lt_two).mpr h2
  omega

/-- From `n = 2` on, `⌈log₂ (n + 2)⌉ ≤ 3 ⌊log₂ n⌋`: the left side is at most `⌊log₂ n⌋ + 2`, and
`⌊log₂ n⌋ ≥ 1`. -/
theorem clog_two_add_two_le_three_mul_log_two {n : ℕ} (hn : 2 ≤ n) :
    clog 2 (n + 2) ≤ 3 * log 2 n := by
  have hL : 1 ≤ log 2 n := le_log_of_pow_le Nat.one_lt_two (by simpa using hn)
  have hlt : n < 2 ^ (log 2 n + 1) := lt_pow_succ_log_self Nat.one_lt_two n
  refine (clog_le_iff_le_pow Nat.one_lt_two).mpr ?_
  calc n + 2 ≤ 2 ^ (log 2 n + 2) := by rw [Nat.pow_succ]; omega
    _ ≤ 2 ^ (3 * log 2 n) := Nat.pow_le_pow_right Nat.two_pos (by omega)

end Nat


