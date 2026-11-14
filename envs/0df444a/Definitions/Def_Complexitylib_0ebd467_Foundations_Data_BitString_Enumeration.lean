-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Enumeration
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_Enumeration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:34.608559+00:00
-- url     : https://prove2.me/theorems/f794f15d-eb06-4d5d-b9da-8f5746d27cf5
-- title:
--   Complexity.Foundations.Data.BitString.Enumeration — Enumerating bit strings
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.Enumeration` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The list `BitString.enum n` enumerates all `n`-bit strings once in binary order, least significant
--   bit first. This is an executable enumeration; generating its `2 ^ n` entries is not asserted to
--   be polynomial in `n`.
--
--   ### Main definitions
--
--   * `Cslib.BitString.enum`: enumerate bit strings by prepending both bits to every shorter string.
--   * `Cslib.BitString.enumList`: the same enumeration as ordinary lists of bits.
--
--   ### Main results
--
--   * `Cslib.BitString.mem_enum`, `Cslib.BitString.length_enum`, `Cslib.BitString.nodup_enum`:
--     the enumeration contains each bit string exactly once and has `2 ^ n` entries.
--   * `Cslib.BitString.enum_eq_ofFn`, `Cslib.BitString.enumList_eq_ofFn`: the enumeration lists the
--     bit strings in the order of their numbers `Cslib.BitString.equivFin`.
--
--   ### References
--
--   Adapted from Crypto/Computational/GoldreichLevin/{Reduction,WordDecoder}.lean on the cslib
--   `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
--
--   **Contents.** The module is published as a whole: 13 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Enumeration`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/Enumeration.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Basic
public import Mathlib.Data.List.OfFn

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.Enumeration` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Enumerating bit strings

The list `BitString.enum n` enumerates all `n`-bit strings once in binary order, least significant
bit first. This is an executable enumeration; generating its `2 ^ n` entries is not asserted to
be polynomial in `n`.

## Main definitions

* `Cslib.BitString.enum`: enumerate bit strings by prepending both bits to every shorter string.
* `Cslib.BitString.enumList`: the same enumeration as ordinary lists of bits.

## Main results

* `Cslib.BitString.mem_enum`, `Cslib.BitString.length_enum`, `Cslib.BitString.nodup_enum`:
  the enumeration contains each bit string exactly once and has `2 ^ n` entries.
* `Cslib.BitString.enum_eq_ofFn`, `Cslib.BitString.enumList_eq_ofFn`: the enumeration lists the
  bit strings in the order of their numbers `Cslib.BitString.equivFin`.

## References

Adapted from Crypto/Computational/GoldreichLevin/{Reduction,WordDecoder}.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.BitString

/-- Enumerate bitstrings by prepending each possible bit. This fixes an executable order. -/
def enum : (k : ℕ) → List (BitString k)
  | 0 => [Fin.elim0]
  | k + 1 => (enum k).flatMap (fun guess => [Fin.cons false guess, Fin.cons true guess])

/-- Every bit string is enumerated. -/
@[simp] theorem mem_enum (k : ℕ) (guess : BitString k) : guess ∈ enum k := by
  induction k with
  | zero => simp [enum, Subsingleton.elim guess Fin.elim0]
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨Fin.tail guess, ih _, ?_⟩
    have hg := Fin.cons_self_tail guess
    cases hbit : guess 0 <;> simp_all

/-- There are exactly `2 ^ k` strings of `k` bits. -/
@[simp] theorem length_enum (k : ℕ) : (enum k).length = 2 ^ k := by
  induction k with
  | zero => simp [enum]
  | succ k ih =>
    simp [enum, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

/-- Each bit string occurs exactly once. -/
theorem nodup_enum (k : ℕ) : (enum k).Nodup := by
  have key : ∀ l : List (BitString k), l.Nodup ↔ l.dedup.length = l.length := fun l =>
    ⟨fun h => by rw [h.dedup], fun h => by
      have := (List.dedup_sublist l).eq_of_length h
      rw [← this]; exact List.nodup_dedup l⟩
  rw [key, ← List.card_toFinset]
  have hall : (enum k).toFinset = Finset.univ := by ext; simp
  rw [hall]
  simp [BitString]

/-- The binary enumeration represented by ordinary lists, in the same order. -/
def enumList (count : ℕ) : List (List Bool) := (enum count).map List.ofFn

/-- The only word of length `0` is the empty list. -/
@[simp] theorem enumList_zero : enumList 0 = [[]] := rfl

/-- Extend every shorter string by both possible first bits. -/
theorem enumList_succ (count : ℕ) :
    enumList (count + 1) =
      (enumList count).flatMap (fun word => [false :: word, true :: word]) := by
  simp [enumList, enum, List.map_flatMap, List.flatMap_map]

/-- The word enumeration has the same size as the finite-string enumeration. -/
@[simp] theorem length_enumList (count : ℕ) : (enumList count).length = 2 ^ count := by
  simp [enumList]

/-- Counting an output predicate over the enumeration equals its finite witness cardinality. -/
theorem countP_enumList (n : ℕ) (verdict : List Bool → Bool) :
    (enumList n).countP verdict =
      (Finset.univ.filter fun word : BitString n => verdict (List.ofFn word)).card := by
  have hall : (enum n).toFinset = Finset.univ := by ext; simp
  simpa [enumList, List.countP_map, Function.comp_def, hall] using
    ((nodup_enum n).card_eq_countP (P := fun word => verdict (List.ofFn word))).symm

/-- Every enumerated word has the requested width. -/
theorem length_of_mem_enumList {count : ℕ} {word : List Bool}
    (hword : word ∈ enumList count) : word.length = count := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hword
  simp

/-- The ordinary-list enumeration contains exactly the words of the specified length. -/
@[simp] theorem mem_enumList {count : ℕ} {word : List Bool} :
    word ∈ enumList count ↔ word.length = count := by
  refine ⟨length_of_mem_enumList, ?_⟩
  intro h
  subst count
  exact List.mem_map.mpr ⟨word.get, mem_enum _ _, List.ofFn_get word⟩

/-- **The enumeration is in the order of `equivFin`**: binary order, least significant bit
first. -/
theorem enum_eq_ofFn (k : ℕ) : enum k = List.ofFn (equivFin k).symm := by
  induction k with
  | zero => exact List.ext_getElem (by simp) fun _ _ _ => Subsingleton.elim _ _
  | succ k ih =>
    rw [enum, ih, List.flatMap, List.map_ofFn, List.ofFn_congr (pow_succ 2 k), List.ofFn_mul]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    have hcons (b : Bool) (j : ℕ) (hj : b.toNat = j) (h : (i : ℕ) * 2 + j < 2 ^ k * 2) :
        Fin.cons b ((equivFin k).symm i) =
          (equivFin (k + 1)).symm (Fin.cast (pow_succ 2 k).symm ⟨i * 2 + j, h⟩) := by
      refine (Equiv.eq_symm_apply _).2 (Fin.ext ?_)
      rw [val_equivFin_cons, Equiv.apply_symm_apply, Fin.val_cast]
      change _ = (i : ℕ) * 2 + j
      omega
    simp only [Function.comp_apply, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ]
    rw [hcons false 0 rfl, hcons true 1 rfl]

/-- The word enumeration lists the bits of the strings in the order of `equivFin`. -/
theorem enumList_eq_ofFn (k : ℕ) :
    enumList k = List.ofFn fun i => List.ofFn ((equivFin k).symm i) := by
  rw [enumList, enum_eq_ofFn, List.map_ofFn]
  rfl

end Cslib.BitString


