-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Counter
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_Counter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:44.658574+00:00
-- url     : https://prove2.me/theorems/0014c41c-e1a0-4bfb-9bf9-79141bd4d5bb
-- title:
--   Complexity.Foundations.Data.BitString.Counter — A binary counter
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.Counter` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A word of fixed length is a counter, read least significant bit first (`Cslib.BitString.lsbValue`).
--   Increment (`Cslib.BitString.increment`) flips the trailing ones of the least significant end and
--   the first zero, discarding the final carry, so it keeps the length and wraps around from the word
--   of ones to the word of zeros. Counting from the word of `m` zeros enumerates the words of length
--   `m` in order of value (`Cslib.BitString.iterate_increment`), each reached at its value
--   (`Cslib.BitString.iterate_increment_lsbValue`). Exhaustive searches in polynomial space enumerate
--   their candidates in this way, storing only the current one.
--
--   ### Main definitions
--
--   * `Cslib.BitString.increment`: binary increment, least significant bit first.
--   * `Cslib.BitString.lsbValue`: the value of a word, least significant bit first.
--
--   ### Main results
--
--   * `Cslib.BitString.lsbValue_increment`: increment adds one below the largest value.
--   * `Cslib.BitString.lsbValue_injective`: words of the same length are determined by their values.
--   * `Cslib.BitString.iterate_increment`, `Cslib.BitString.iterate_increment_lsbValue`: counting from
--     zero enumerates the words of a length.
--   * `Cslib.BitString.lsbValue_append`, `Cslib.BitString.lsbValue_singleton`,
--     `Cslib.BitString.lsbValue_bits`: the value of a concatenation, of one bit, and of the binary
--     digits `Nat.bits n` of a number.
--   * `Cslib.BitString.lsbValue_eq_foldr_bit`: `lsbValue` is a right fold of `Nat.bit`.
--   * `Cslib.BitString.testBit_lsbValue`: binary digit `i` of `lsbValue w` is the bit `w[i]`.
--
--   **Contents.** The module is published as a whole: 18 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Counter`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/Counter.lean

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
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Bits

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.Counter` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A binary counter

A word of fixed length is a counter, read least significant bit first (`Cslib.BitString.lsbValue`).
Increment (`Cslib.BitString.increment`) flips the trailing ones of the least significant end and
the first zero, discarding the final carry, so it keeps the length and wraps around from the word
of ones to the word of zeros. Counting from the word of `m` zeros enumerates the words of length
`m` in order of value (`Cslib.BitString.iterate_increment`), each reached at its value
(`Cslib.BitString.iterate_increment_lsbValue`). Exhaustive searches in polynomial space enumerate
their candidates in this way, storing only the current one.

## Main definitions

* `Cslib.BitString.increment`: binary increment, least significant bit first.
* `Cslib.BitString.lsbValue`: the value of a word, least significant bit first.

## Main results

* `Cslib.BitString.lsbValue_increment`: increment adds one below the largest value.
* `Cslib.BitString.lsbValue_injective`: words of the same length are determined by their values.
* `Cslib.BitString.iterate_increment`, `Cslib.BitString.iterate_increment_lsbValue`: counting from
  zero enumerates the words of a length.
* `Cslib.BitString.lsbValue_append`, `Cslib.BitString.lsbValue_singleton`,
  `Cslib.BitString.lsbValue_bits`: the value of a concatenation, of one bit, and of the binary
  digits `Nat.bits n` of a number.
* `Cslib.BitString.lsbValue_eq_foldr_bit`: `lsbValue` is a right fold of `Nat.bit`.
* `Cslib.BitString.testBit_lsbValue`: binary digit `i` of `lsbValue w` is the bit `w[i]`.
-/

@[expose] public section

namespace Cslib.BitString

/-- Binary increment, least significant bit first, discarding the final carry. -/
def increment : List Bool → List Bool
  | [] => []
  | false :: w => true :: w
  | true :: w => false :: increment w

/-- The value of a word in binary, least significant bit first. -/
def lsbValue : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * lsbValue w

/-- Increment keeps the length. -/
@[simp] theorem length_increment : ∀ w, (increment w).length = w.length
  | [] => rfl
  | false :: _ => rfl
  | true :: w => by simp [increment, length_increment w]

/-- Iterated increment keeps the length. -/
@[simp] theorem length_iterate_increment (j : ℕ) (w : List Bool) :
    (increment^[j] w).length = w.length := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, length_increment]

/-- A word of length `m` has value below `2 ^ m`. -/
theorem lsbValue_lt : ∀ w, lsbValue w < 2 ^ w.length
  | [] => by simp [lsbValue]
  | b :: w => by
    have := lsbValue_lt w
    have := Bool.toNat_le b
    simp only [lsbValue, List.length_cons]
    lia

/-- Below the largest value, increment adds one. -/
theorem lsbValue_increment : ∀ w, lsbValue w + 1 < 2 ^ w.length →
    lsbValue (increment w) = lsbValue w + 1
  | [] => by simp [lsbValue]
  | false :: w => fun _ => by
    simp only [increment, lsbValue, Bool.toNat_true, Bool.toNat_false]
    lia
  | true :: w => fun h => by
    simp only [lsbValue, List.length_cons, Bool.toNat_true, increment, Bool.toNat_false] at h ⊢
    rw [lsbValue_increment w (by lia)]
    lia

/-- Words of the same length are determined by their values. -/
theorem lsbValue_injective : ∀ {w w' : List Bool}, w.length = w'.length →
    lsbValue w = lsbValue w' → w = w'
  | [], [], _, _ => rfl
  | b :: w, b' :: w', hl, hv => by
    simp only [lsbValue] at hv
    have hb : b = b' := by
      cases b <;> cases b' <;>
        first | rfl | (simp only [Bool.toNat_false, Bool.toNat_true] at hv; lia)
    subst hb
    exact congrArg _ (lsbValue_injective (by simpa using hl) (by lia))

/-- The word of zeros has value `0`. -/
@[simp] theorem lsbValue_replicate_false : ∀ m, lsbValue (List.replicate m false) = 0
  | 0 => rfl
  | m + 1 => by simp [List.replicate_succ, lsbValue, lsbValue_replicate_false m]

/-- The word of ones has the largest value. -/
theorem lsbValue_replicate_true : ∀ m, lsbValue (List.replicate m true) + 1 = 2 ^ m
  | 0 => rfl
  | m + 1 => by
    have := lsbValue_replicate_true m
    simp only [List.replicate_succ, lsbValue, Bool.toNat_true]
    lia

/-- A word with a `true` has a positive value. -/
theorem lsbValue_pos_of_true_mem : ∀ {u : List Bool}, true ∈ u → 0 < lsbValue u
  | b :: u, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [lsbValue, Bool.toNat_true]
      lia
    · have := lsbValue_pos_of_true_mem h
      simp only [lsbValue]
      lia

/-- A word without `true` has value `0`. -/
theorem lsbValue_eq_zero_of_true_not_mem : ∀ {u : List Bool}, true ∉ u → lsbValue u = 0
  | [], _ => rfl
  | b :: u, h => by
    simp only [List.mem_cons, not_or] at h
    have hb : b = false := by simpa using h.1
    subst hb
    simp [lsbValue, lsbValue_eq_zero_of_true_not_mem h.2]

/-- **The counter counts**: the `j`-th iterate from the word of `m` zeros has value `j`, for
`j < 2 ^ m`. -/
theorem iterate_increment (m : ℕ) : ∀ j < 2 ^ m,
    lsbValue (increment^[j] (List.replicate m false)) = j ∧
      (increment^[j] (List.replicate m false)).length = m
  | 0, _ => ⟨lsbValue_replicate_false m, List.length_replicate⟩
  | j + 1, hj => by
    obtain ⟨hv, hl⟩ := iterate_increment m j (by lia)
    rw [Function.iterate_succ_apply', length_increment,
      lsbValue_increment _ (by rw [hv, hl]; lia), hv]
    exact ⟨rfl, hl⟩

/-- **Every word is reached by counting up to its value.** -/
theorem iterate_increment_lsbValue (u : List Bool) :
    increment^[lsbValue u] (List.replicate u.length false) = u :=
  let h := iterate_increment u.length (lsbValue u) (lsbValue_lt u)
  lsbValue_injective h.2 h.1

/-- The value of a concatenation: the second word is shifted past the first. -/
theorem lsbValue_append : ∀ u v : List Bool,
    lsbValue (u ++ v) = lsbValue u + 2 ^ u.length * lsbValue v
  | [], v => by simp [lsbValue]
  | b :: u, v => by
    simp only [List.cons_append, lsbValue, List.length_cons, lsbValue_append u v, Nat.pow_succ',
      Nat.mul_assoc]
    lia

/-- A one-bit word has the value of its bit. -/
@[simp] theorem lsbValue_singleton (b : Bool) : lsbValue [b] = b.toNat := by simp [lsbValue]

/-- The binary digits of a number, least significant first, have the number as value. -/
@[simp] theorem lsbValue_bits (n : ℕ) : lsbValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rw [Nat.zero_bits]; rfl
  | bit b n h ih => rw [Nat.bits_append_bit n b h, lsbValue, ih, Nat.bit_val]; lia

/-- `lsbValue` is a right fold of `Nat.bit`. -/
theorem lsbValue_eq_foldr_bit (w : List Bool) : lsbValue w = w.foldr Nat.bit 0 := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [lsbValue, List.foldr_cons, ← ih, Nat.bit_val, Nat.add_comm]

/-- Binary digit `i` of the value of a word is its bit `i`, or `false` past its end. -/
@[simp] theorem testBit_lsbValue : ∀ (w : List Bool) (i : ℕ),
    (lsbValue w).testBit i = w.getD i false
  | [], _ => by simp [lsbValue]
  | b :: w, i => by
    rw [lsbValue_eq_foldr_bit, List.foldr_cons, ← lsbValue_eq_foldr_bit]
    cases i with
    | zero => simp
    | succ i => simp [Nat.testBit_bit_succ, testBit_lsbValue w i]

end Cslib.BitString


