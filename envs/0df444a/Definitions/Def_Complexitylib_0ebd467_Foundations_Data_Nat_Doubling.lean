-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Doubling
-- name    : Complexitylib_0ebd467_Foundations_Data_Nat_Doubling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:59.627552+00:00
-- url     : https://prove2.me/theorems/c8deb5ab-1fc9-4c91-935e-46b52be0bfc5
-- title:
--   Complexity.Foundations.Data.Nat.Doubling — Powers of two by doubling
-- statement:
--   This is module `Complexity.Foundations.Data.Nat.Doubling` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Doubling a counter once per element of a list multiplies it by `2 ^ length`
--   (`List.foldl_add_self_eq_mul_two_pow`), and the least power of two above `n`, `2 ^ Nat.size n`,
--   is at most `2 * n + 1` (`Nat.two_pow_size_le`). Together they bound unary counters built by
--   doubling once per binary digit.
--
--   ### Main results
--
--   * `List.foldl_add_self_eq_mul_two_pow`: `l.foldl (fun m _ => m + m) m = m * 2 ^ l.length`.
--   * `Nat.two_pow_size_le`: `2 ^ Nat.size n ≤ 2 * n + 1`.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Doubling`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/Nat/Doubling.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Foundations.Data.Nat.Doubling` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Powers of two by doubling

Doubling a counter once per element of a list multiplies it by `2 ^ length`
(`List.foldl_add_self_eq_mul_two_pow`), and the least power of two above `n`, `2 ^ Nat.size n`,
is at most `2 * n + 1` (`Nat.two_pow_size_le`). Together they bound unary counters built by
doubling once per binary digit.

## Main results

* `List.foldl_add_self_eq_mul_two_pow`: `l.foldl (fun m _ => m + m) m = m * 2 ^ l.length`.
* `Nat.two_pow_size_le`: `2 ^ Nat.size n ≤ 2 * n + 1`.
-/

public section

namespace List

/-- Doubling a counter once per element of a list multiplies it by `2 ^ length`. -/
theorem foldl_add_self_eq_mul_two_pow {α : Type*} (l : List α) (m : ℕ) :
    l.foldl (fun m _ => m + m) m = m * 2 ^ l.length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.length_cons, pow_succ]
    ring

end List

namespace Nat

/-- `2 ^ Nat.size n` is the least power of two above `n`, so it is at most `2 * n + 1`. -/
theorem two_pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨s, hs⟩ : ∃ s, n.size = s + 1 := ⟨n.size - 1, by have := Nat.size_pos.mpr hn; omega⟩
    have : 2 ^ s ≤ n := Nat.lt_size.mp (by omega)
    rw [hs, pow_succ]
    omega

end Nat


