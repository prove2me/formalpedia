-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:04.028454+00:00
-- url     : https://prove2.me/theorems/49b4cf43-2328-48db-bb1f-9b03cc06d059
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words — Reading arbitrary little-endian natural-number words
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The existing word interpretation and normalization identity are independent of machine or
--   complexity certificates. Trailing false symbols are ignored, and the empty word represents zero.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.ofBits`: read little-endian digits as a natural number.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.bits_ofBits`: normalize a word by removing its trailing false symbols.
--   * `Turing.MultiTapeTM.bits_add_two_pow`: the binary digits of `x + 2 ^ W`, for `x < 2 ^ W`, are
--     the `W` low-order digits of `x` (`Cslib.BitString.lowBits`) followed by a one.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Nat/Words.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
public import Mathlib.Data.List.DropRight
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Binary
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Counter
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Append
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Bits
import Mathlib.Data.Nat.Size

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Reading arbitrary little-endian natural-number words

The existing word interpretation and normalization identity are independent of machine or
complexity certificates. Trailing false symbols are ignored, and the empty word represents zero.

## Main definitions

* `Turing.MultiTapeTM.ofBits`: read little-endian digits as a natural number.

## Main results

* `Turing.MultiTapeTM.bits_ofBits`: normalize a word by removing its trailing false symbols.
* `Turing.MultiTapeTM.bits_add_two_pow`: the binary digits of `x + 2 ^ W`, for `x < 2 ^ W`, are
  the `W` low-order digits of `x` (`Cslib.BitString.lowBits`) followed by a one.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-- Binary digits, least significant first, read as a number. -/
def ofBits (w : List Bool) : ℕ := w.foldr Nat.bit 0

/-- The binary digits of a word read as a number are the word up to its last `true`. -/
theorem bits_ofBits (w : List Bool) : (ofBits w).bits = w.rdropWhile (!·) := by
  induction w with
  | nil => simp [ofBits]
  | cons b w ih =>
    rw [ofBits, List.foldr_cons, ← ofBits, ← List.singleton_append, List.rdropWhile_append, ← ih]
    by_cases h : ofBits w = 0 ∧ b = false
    · obtain ⟨h₀, rfl⟩ := h
      simp [h₀]
    · rw [Nat.bits_append_bit _ _ fun h₀ => by simpa [h₀] using h]
      by_cases h₀ : ofBits w = 0
      · obtain rfl : b = true := by simpa [h₀] using h
        simp [h₀, List.rdropWhile_singleton]
      · simp only [Nat.bits_eq_nil_iff, h₀, ↓reduceIte]
        rfl

/-- A trailing one adds `2 ^ |w|` to the value of a word. -/
private theorem foldr_bit_one_eq (w : List Bool) :
    w.foldr Nat.bit 1 = w.foldr Nat.bit 0 + 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, Nat.bit_val, Nat.bit_val, List.length_cons, pow_succ]
    omega

/-- The binary digits of `x + 2 ^ W`, for `x < 2 ^ W`, are the `W` low-order digits of `x`,
followed by a one. -/
theorem bits_add_two_pow {W x : ℕ} (hx : x < 2 ^ W) :
    (x + 2 ^ W).bits = Cslib.BitString.lowBits W x ++ [true] := by
  have h := foldr_bit_one_eq (Cslib.BitString.lowBits W x)
  rw [← Cslib.BitString.lsbValue_eq_foldr_bit, Cslib.BitString.lsbValue_lowBits hx,
    Cslib.BitString.length_lowBits] at h
  rw [← h, Nat.bits_foldr_bit_one]

/-- The `W` low-order digits of `x < 2 ^ W` are `(x + 2 ^ W).bits` without its last digit. -/
theorem dropLast_bits_add_two_pow {W x : ℕ} (hx : x < 2 ^ W) :
    (x + 2 ^ W).bits.dropLast = Cslib.BitString.lowBits W x := by
  rw [bits_add_two_pow hx, List.dropLast_concat]

end Turing.MultiTapeTM


