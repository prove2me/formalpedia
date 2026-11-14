-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_BinarySize
-- name    : Complexitylib_0ebd467_Foundations_Data_Nat_BinarySize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:56.289953+00:00
-- url     : https://prove2.me/theorems/cf2f452c-91aa-4087-bda5-8103b645d318
-- title:
--   Complexity.Foundations.Data.Nat.BinarySize — Binary sizes of products, powers, and factorials
-- statement:
--   This is module `Complexity.Foundations.Data.Nat.BinarySize` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These pure facts are moved unchanged from the binary arithmetic facade. They retain their
--   qualified names without depending on a machine calculus.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_BinarySize`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/Nat/BinarySize.lean

/-
Copyright (c) 2026 Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth, Anton Kovsharov
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Foundations.Data.Nat.BinarySize` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Binary sizes of products, powers, and factorials

These pure facts are moved unchanged from the binary arithmetic facade. They retain their
qualified names without depending on a machine calculus.
-/

@[expose] public section
namespace Nat

/-- The binary length of a product is at most the binary lengths of the factors together. -/
theorem size_mul_le (m n : ℕ) : (m * n).size ≤ m.size + n.size := by
  refine Nat.size_le.2 ?_
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self m) (Nat.lt_size_self n)

/-- The binary length of a power is at most the exponent times the binary length of the base,
plus one for the zeroth power. -/
theorem size_pow_le (m k : ℕ) : (m ^ k).size ≤ k * m.size + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := size_mul_le (m ^ k) m
    rw [Nat.pow_succ, Nat.succ_mul]
    lia

/-- The binary length of `n!` is at most `n * n.size + 1`. -/
theorem size_factorial_le (n : ℕ) : n.factorial.size ≤ n * n.size + 1 :=
  (Nat.size_le_size n.factorial_le_pow).trans (size_pow_le n n)

end Nat


