-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:14.627913+00:00
-- url     : https://prove2.me/theorems/1216d958-b95d-468f-b7c0-26c10b3eee0c
-- title:
--   Complexity.Foundations.Data.BitString.List.Binary — Saturating binary decoding
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.List.Binary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Words are read most significant bit first. Saturating at every step keeps a unary accumulator
--   bounded on arbitrary input words; it agrees with capping the full mathematical binary value.
--
--   ### Main definitions
--
--   * `binaryValue`: the natural represented by a binary word, without a size bound.
--   * `boundedBinaryValue`: the same fold with a cap at every step.
--   * `binaryWord`: the word of a given width representing a number.
--   * `lowBits`: a fixed-width word in the opposite, least-significant-first order.
--
--   ### Main results
--
--   * `binaryValue_injective_of_length_eq`: fixed-width words have distinct binary values.
--   * `boundedBinaryValue_eq`: incremental saturation equals a single final cap.
--   * `boundedBinaryValue_le`: every output is at most the cap.
--   * `binaryValue_lt_two_pow`, `exists_binaryValue_eq`: the words of `t` bits represent exactly the
--     numbers below `2 ^ t`.
--   * `length_binaryWord`, `binaryValue_binaryWord`: the word of width `t` of a number below `2 ^ t`.
--   * `lowBits_two_pow`: `2 ^ width` has the same `width` low-order bits as `0`.
--
--   ### References
--
--   Adapted from Probability/UniformNat.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
--
--   **Contents.** The module is published as a whole: 19 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/List/Binary.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.Nat.Bits
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Bits
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.List.Binary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Saturating binary decoding

Words are read most significant bit first. Saturating at every step keeps a unary accumulator
bounded on arbitrary input words; it agrees with capping the full mathematical binary value.

## Main definitions

* `binaryValue`: the natural represented by a binary word, without a size bound.
* `boundedBinaryValue`: the same fold with a cap at every step.
* `binaryWord`: the word of a given width representing a number.
* `lowBits`: a fixed-width word in the opposite, least-significant-first order.

## Main results

* `binaryValue_injective_of_length_eq`: fixed-width words have distinct binary values.
* `boundedBinaryValue_eq`: incremental saturation equals a single final cap.
* `boundedBinaryValue_le`: every output is at most the cap.
* `binaryValue_lt_two_pow`, `exists_binaryValue_eq`: the words of `t` bits represent exactly the
  numbers below `2 ^ t`.
* `length_binaryWord`, `binaryValue_binaryWord`: the word of width `t` of a number below `2 ^ t`.
* `lowBits_two_pow`: `2 ^ width` has the same `width` low-order bits as `0`.

## References

Adapted from Probability/UniformNat.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.BitString

/-- The first `width` digits of a natural, least significant first. Unlike `binaryWord`, this
always has the declared width: high digits are truncated and absent digits are `false`. -/
def lowBits (width value : ℕ) : List Bool := (List.range width).map value.testBit

/-- `lowBits width value` has `width` digits. -/
@[simp] theorem length_lowBits (width value : ℕ) : (lowBits width value).length = width := by
  simp [lowBits]

/-- The executable digit loop agrees with the finite coordinate view. -/
theorem lowBits_eq_ofFn (width value : ℕ) :
    lowBits width value = List.ofFn (fun i : Fin width => value.testBit i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [lowBits]

/-- All `width` low-order bits of `2 ^ width` are `false`, matching `lowBits width 0`. -/
theorem lowBits_two_pow (width : ℕ) : lowBits width (2 ^ width) = lowBits width 0 := by
  simp only [lowBits]; refine List.map_congr_left fun i hi => ?_
  rw [Nat.testBit_two_pow_of_ne (ne_of_gt (List.mem_range.mp hi)), Nat.zero_testBit]

/-- The natural number represented by a word, most significant bit first. -/
def binaryValue (word : List Bool) : ℕ :=
  word.foldl (fun value bit => 2 * value + bit.toNat) 0

/-- Decode binary digits with a saturating accumulator. -/
def boundedBinaryValue (bound : ℕ) (word : List Bool) : ℕ :=
  word.foldl (fun value bit => min bound (2 * value + bit.toNat)) 0

private theorem min_binary_step (bound value : ℕ) (bit : Bool) :
    min bound (2 * min bound value + bit.toNat) = min bound (2 * value + bit.toNat) := by
  by_cases h : value ≤ bound
  · rw [Nat.min_eq_right h]
  · rw [Nat.min_eq_left (by lia), Nat.min_eq_left (by lia)]

/-- Saturating at each step agrees with capping the final mathematical value. -/
theorem boundedBinaryValue_eq (bound : ℕ) (word : List Bool) :
    boundedBinaryValue bound word = min bound (binaryValue word) := by
  simpa only [boundedBinaryValue, binaryValue, Nat.min_zero] using
    (List.foldl_hom (min bound) (l := word) (init := 0)
      (min_binary_step bound))

/-- The unary result never exceeds the declared bound. -/
theorem boundedBinaryValue_le (bound : ℕ) (word : List Bool) :
    boundedBinaryValue bound word ≤ bound := by
  rw [boundedBinaryValue_eq]
  exact Nat.min_le_left _ _

/-- Append a low-order bit to a most-significant-first binary word. -/
theorem binaryValue_snoc (word : List Bool) (bit : Bool) :
    binaryValue (word ++ [bit]) = 2 * binaryValue word + bit.toNat := by
  simp [binaryValue, List.foldl_append]

/-- Reversing the little-endian digits gives the corresponding most-significant-first value. -/
theorem binaryValue_reverse_bits (n : ℕ) : binaryValue n.bits.reverse = n := by
  simpa only [binaryValue, List.foldl_reverse, ← Nat.bit_val] using Nat.foldr_bit_bits n

/-- An all-one binary word represents one less than the corresponding power of two. -/
theorem binaryValue_replicate_true (k : ℕ) :
    binaryValue (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => simp [binaryValue]
  | succ k ih =>
    rw [List.replicate_succ']
    simp only [binaryValue, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Bool.toNat_true] at *
    rw [Nat.pow_succ]
    lia

/-- A word of `n` bits represents a number below `2 ^ n`. -/
theorem binaryValue_lt_two_pow (word : List Bool) : binaryValue word < 2 ^ word.length := by
  induction word using List.reverseRecOn with
  | nil => simp [binaryValue]
  | append_singleton word bit ih =>
    rw [binaryValue_snoc, List.length_append, List.length_singleton, Nat.pow_succ]
    cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Leading zeros do not change the represented number. -/
theorem binaryValue_replicate_false_append (n : ℕ) (word : List Bool) :
    binaryValue (List.replicate n false ++ word) = binaryValue word := by
  have h : (List.replicate n false).foldl (fun value bit => 2 * value + bit.toNat) 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ', List.foldl_append, ih]; rfl
  rw [binaryValue, List.foldl_append, h, ← binaryValue]

/-- The word of width `w` representing `a` in binary, most significant bit first, padded with
leading zeros; it has width `w` when `a < 2 ^ w` (`length_binaryWord`). -/
def binaryWord (w a : ℕ) : List Bool := List.replicate (w - a.bits.length) false ++ a.bits.reverse

/-- The word of width `w` representing `a` has `w` bits when `a < 2 ^ w`. -/
theorem length_binaryWord {w a : ℕ} (ha : a < 2 ^ w) : (binaryWord w a).length = w := by
  have : a.bits.length ≤ w := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.2 ha
  simp only [binaryWord, List.length_append, List.length_replicate, List.length_reverse]
  omega

/-- The word `binaryWord w a` represents `a`, whatever the width `w`. -/
@[simp] theorem binaryValue_binaryWord (w a : ℕ) : binaryValue (binaryWord w a) = a := by
  rw [binaryWord, binaryValue_replicate_false_append, binaryValue_reverse_bits]

/-- Every number below `2 ^ t` is represented by a word of `t` bits. -/
theorem exists_binaryValue_eq {t k : ℕ} (hk : k < 2 ^ t) :
    ∃ u : Fin t → Bool, binaryValue (List.ofFn u) = k := by
  have hwlen := length_binaryWord hk
  refine ⟨fun i => (binaryWord t k)[i.val]'(by omega), ?_⟩
  rw [show (List.ofFn fun i : Fin t => (binaryWord t k)[i.val]'(by omega)) = binaryWord t k from
    List.ext_getElem (by simp [hwlen]) fun i _ _ => by simp, binaryValue_binaryWord]

/-- Fixed-width binary words represent their values injectively. -/
theorem binaryValue_injective_of_length_eq {u v : List Bool} (hlen : u.length = v.length)
    (h : binaryValue u = binaryValue v) : u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil => exact (List.length_eq_zero_iff.1 hlen.symm).symm
  | append_singleton u b ih =>
    obtain ⟨v, c, rfl⟩ : ∃ w b, v = w ++ [b] := by
      rcases List.eq_nil_or_concat v with h' | ⟨w, b, h'⟩
      · simp [h'] at hlen
      · exact ⟨w, b, by simpa using h'⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
    rw [binaryValue_snoc, binaryValue_snoc] at h
    have hb : b = c := by
      cases b <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;>
        first | rfl | lia
    subst hb
    rw [ih hlen (by lia)]

end Cslib.BitString


