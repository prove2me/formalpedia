-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:55.670847+00:00
-- url     : https://prove2.me/theorems/382c0c8c-bc85-4540-8b3c-68cc5f223544
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString — Polynomial-time bit-list operations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Raw bit strings and framed lists share the list and iteration calculus. Captured traversals,
--   Boolean folds, pointwise operations, majority and selected mask sums have compositional
--   certificates. Runtime dimensions are computed in unary. Enumeration additionally requires a
--   polynomial bound on the complete encoded output. The operations are total on empty and short lists.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ofBits_reverse`: agreement of the two binary-word conventions.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBinaryValue`: binary-valued word decoding.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsLow`: fixed-width low-order binary digits.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsToList`, `.listToBits`: encoding conversion.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFlatten`: concatenate computed raw words.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapToBitsWithInput`: concatenate captured
--     words over a framed list.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFrame`, `.bitsPadWord`: self-delimiting
--     framing and bounded padding, including arbitrary encoded inputs and overlong words.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsGetElem?`: optional lookup in raw bits.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapToBitsWithInput`, `.bitsFilterWithInput`,
--     `.bitsAnyWithInput`, `.bitsFoldlWithInput`, `.bitsZipWithInput`, and
--     `Turing.MultiTapeTM.ComputableInPolyTime.bitsAllWithInput`: compositional bit operations.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsStrictMajority`, `.bitsSingle`, `.bitsSingles`,
--     `.bitsXorSelected`, `.bitsXorWithInput`: finite-mask algorithms.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.bitsCountPWithInput`,
--     `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCountWithInput`: unary counts under captured
--     predicates or computed labels.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.bitsNonpositiveMarginWithInput`: compare the
--     correct-vote count with the word length.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsEnumList`: output-bounded enumeration.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBoundedBinaryValue`: capped binary decoding
--     to unary, with every intermediate accumulator bounded by the supplied cap.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsReplicate`: repeat a fixed bit.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsWordLt`: lexicographic word comparison.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowWithInput`: read one fixed-width row.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowsWithInput`: read a runtime number of rows.
--
--   ### References
--
--   Adapted from Computability/Probabilistic/BitString.lean and
--   Computability/Probabilistic/UniformNat.lean and
--   Crypto/Computational/GoldreichLevin/WordDecoder.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy machine calculus.
--
--   **Contents.** The module is published as a whole: 66 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/BitString.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListToBits
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Operations
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Enumeration
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_WordCount
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Padding
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time bit-list operations

Raw bit strings and framed lists share the list and iteration calculus. Captured traversals,
Boolean folds, pointwise operations, majority and selected mask sums have compositional
certificates. Runtime dimensions are computed in unary. Enumeration additionally requires a
polynomial bound on the complete encoded output. The operations are total on empty and short lists.

## Main results

* `Turing.MultiTapeTM.ofBits_reverse`: agreement of the two binary-word conventions.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBinaryValue`: binary-valued word decoding.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsLow`: fixed-width low-order binary digits.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsToList`, `.listToBits`: encoding conversion.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFlatten`: concatenate computed raw words.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapToBitsWithInput`: concatenate captured
  words over a framed list.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFrame`, `.bitsPadWord`: self-delimiting
  framing and bounded padding, including arbitrary encoded inputs and overlong words.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsGetElem?`: optional lookup in raw bits.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapToBitsWithInput`, `.bitsFilterWithInput`,
  `.bitsAnyWithInput`, `.bitsFoldlWithInput`, `.bitsZipWithInput`, and
  `Turing.MultiTapeTM.ComputableInPolyTime.bitsAllWithInput`: compositional bit operations.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsStrictMajority`, `.bitsSingle`, `.bitsSingles`,
  `.bitsXorSelected`, `.bitsXorWithInput`: finite-mask algorithms.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsCountPWithInput`,
  `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCountWithInput`: unary counts under captured
  predicates or computed labels.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsNonpositiveMarginWithInput`: compare the
  correct-vote count with the word length.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsEnumList`: output-bounded enumeration.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBoundedBinaryValue`: capped binary decoding
  to unary, with every intermediate accumulator bounded by the supplied cap.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsReplicate`: repeat a fixed bit.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsWordLt`: lexicographic word comparison.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowWithInput`: read one fixed-width row.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowsWithInput`: read a runtime number of rows.

## References

Adapted from Computability/Probabilistic/BitString.lean and
Computability/Probabilistic/UniformNat.lean and
Crypto/Computational/GoldreichLevin/WordDecoder.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy machine calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Reversing a most-significant-first word gives its little-endian binary decoding. -/
theorem ofBits_reverse (w : List Bool) : ofBits w.reverse = Cslib.BitString.binaryValue w := by
  rw [ofBits, List.foldr_reverse, Cslib.BitString.binaryValue]
  congr 1
  funext v b
  rw [Nat.bit_val]

/-- The encoding charges every bit and every delimiter in the enumerated words. -/
theorem length_encList_enumList (count : ℕ) :
    (encList encBits (Cslib.BitString.enumList count)).length =
      2 ^ count * (2 * count + 1) := by
  simp [encList, Cslib.BitString.enumList, List.length_flatMap, List.map_map,
    Function.comp_def]

namespace ComputableTidilyInPolyTime

/-- Frame the existing input encoding, charging every delimiter. -/
@[fun_prop]
theorem bitsFrame {α : Type} (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun a => frame (enc a)) enc encBits :=
  .of_linear (.of_frame fun _ => rfl)

/-- Saturating binary decoding to unary is polynomial time on arbitrary input words. -/
@[fun_prop]
theorem bitsBoundedBinaryValue : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => Cslib.BitString.boundedBinaryValue p.1 p.2)
    (encPair encUnary encBits) encUnary := by
  apply foldlWith (encA := encBool) (encL := encBits) (encP := encUnary)
    (par := Prod.fst) (list := Prod.snd)
    (step := fun cap value bit => min cap (2 * value + bit.toNat))
    (fst encUnary encBits) (snd encUnary encBits) (const 0) (by fun_prop)
    (B := fun p => p.1)
  · simpa only [encUnary_apply, List.length_replicate] using
      (fst encUnary encBits).polyBounded_length
  · intro p i _
    simpa only [encUnary_apply, List.length_replicate, Cslib.BitString.boundedBinaryValue] using
      Cslib.BitString.boundedBinaryValue_le p.1 (p.2.take i)

/-- Decode computed bits under a computed unary cap, fixing both intermediate encodings. -/
@[fun_prop]
theorem bitsBoundedBinaryValueWithInput {α : Type} {input : α ↪ List Bool}
    {cap : α → ℕ} {word : α → List Bool}
    (hcap : ComputableTidilyInPolyTime cap input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.boundedBinaryValue (cap a) (word a))
      input encUnary := bitsBoundedBinaryValue.comp (hcap.prod hword)

/-- Convert a binary value to unary under a computed unary bound. -/
theorem binary_to_unary_bounded {α : Type} {input : α ↪ List Bool} {value bound : α → ℕ}
    (hvalue : ComputableTidilyInPolyTime value input encNat)
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hle : ∀ a, value a ≤ bound a) :
    ComputableTidilyInPolyTime value input encUnary := by
  have h := bitsBoundedBinaryValueWithInput hbound (bitsReverse.comp hvalue.encoded)
  convert h using 1
  funext a
  simp only [Function.comp_apply, encNat_apply, Cslib.BitString.boundedBinaryValue_eq,
    Cslib.BitString.binaryValue_reverse_bits, Nat.min_eq_right (hle a)]

/-- Convert a raw bit string to the framed list encoding. -/
@[fun_prop]
theorem bitsToList : ComputableTidilyInPolyTime (fun l => l) encBits (encList encBool) := by
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits)
    (step := fun acc bit => acc ++ [bit]) (init := fun _ => [])
    (id' (encIn := encBits)) (const [])
    (show ComputableTidilyInPolyTime (fun p : List Bool × Bool => p.1 ++ [p.2])
      (encPair (encList encBool) encBool) (encList encBool) by fun_prop)
    (growth := 3) (fun _ _ => by simp)
  simpa only [List.foldl_append_eq_append, List.nil_append, List.flatten_eq_flatMap,
    List.flatMap_map, id_eq, List.flatMap_singleton'] using h

/-- Optional lookup in a raw bit string, fixing the representation of the returned bit. -/
@[fun_prop]
theorem bitsGetElem? {α : Type} {input : α ↪ List Bool}
    {list : α → List Bool} {index : α → ℕ}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hindex : ComputableTidilyInPolyTime index input encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x)[index x]?) input (encOption encBool) :=
  getElem? hlist hindex

/-- Remove the framing from a list of bits. -/
@[fun_prop]
theorem listToBits : ComputableTidilyInPolyTime (fun l => l) (encList encBool) encBits := by
  have h := foldl_of_bounded_growth (encA := encBool)
    (step := fun acc bit => acc ++ [bit]) (init := fun _ => [])
    (id' (encIn := encList encBool)) (const [])
    (show ComputableTidilyInPolyTime (fun p : List Bool × Bool => p.1 ++ [p.2])
      (encPair encBits encBool) encBits by fun_prop)
    (growth := 1) (fun _ _ => by simp)
  simpa only [List.foldl_append_eq_append, List.nil_append, List.flatten_eq_flatMap,
    List.flatMap_map, id_eq, List.flatMap_singleton'] using h

/-- Repeat a fixed bit a unary number of times. -/
@[fun_prop]
theorem bitsReplicate (bit : Bool) :
    ComputableTidilyInPolyTime (fun n => List.replicate n bit) encUnary encBits := by
  have h (n : ℕ) : (List.cons bit)^[n] [] = List.replicate n bit := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, List.replicate_succ]
  simpa only [h, id_eq] using iterate_of_bounded_growth (count := id) (init := fun _ : ℕ => [])
    (step := List.cons bit) id' (const []) (by fun_prop) (growth := 1) (fun _ => by simp)

variable {α : Type} {input : α ↪ List Bool}

/-- Concatenate computed raw words, fixing the intermediate list encoding before proof search. -/
@[fun_prop]
theorem bitsFlatten {words : α → List (List Bool)}
    (hwords : ComputableTidilyInPolyTime words input (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => (words a).flatten) input encBits := by
  simpa only [Function.comp_def, List.map_id_fun', id_eq] using
    listToBits.comp ((flatten encBool).comp ((map bitsToList).comp hwords))

/-- Self-delimiting padding uses ordinary framing and unary arithmetic. -/
@[fun_prop]
theorem bitsPadWord {bound : α → ℕ} {word : α → List Bool}
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.padWord (bound a) (word a))
      input encBits := by
  unfold Cslib.BitString.padWord
  fun_prop

/-- Map a captured Boolean-valued function over a framed list, emitting a raw bit string. -/
@[fun_prop]
theorem mapToBitsWithInput {β : Type} {enc : β ↪ List Bool} {list : α → List β}
    {f : α → β → Bool}
    (hlist : ComputableTidilyInPolyTime list input (encList enc))
    (hf : ComputableTidilyInPolyTime (fun p : α × β => f p.1 p.2)
      (encPair input enc) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).map (f a)) input encBits :=
  listToBits.comp (mapWithInput hlist hf)

/-- Concatenate captured raw bit strings over a framed list. The complete intermediate words
and their framing are charged before concatenation. Apply this rule explicitly: registering both
raw and framed `flatMap` outputs makes existing enumeration proof search exceed its limit. -/
theorem flatMapToBitsWithInput {β : Type} {enc : β ↪ List Bool} {list : α → List β}
    {f : α → β → List Bool}
    (hlist : ComputableTidilyInPolyTime list input (encList enc))
    (hf : ComputableTidilyInPolyTime (fun p : α × β => f p.1 p.2)
      (encPair input enc) encBits) :
    ComputableTidilyInPolyTime (fun a => (list a).flatMap (f a)) input encBits := by
  simpa only [List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    bitsFlatten (mapWithInput hlist hf)

/-- Emit a computed unary number of low-order digits of a computed binary natural. The width
charges every output bit, including leading zero digits. -/
@[fun_prop]
theorem bitsLow {width value : α → ℕ}
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hvalue : ComputableTidilyInPolyTime value input encNat) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.lowBits (width a) (value a))
      input encBits := by
  unfold Cslib.BitString.lowBits
  exact mapToBitsWithInput (range.comp hwidth) (by fun_prop)

/-- Map a captured Boolean operation over a raw bit string. -/
@[fun_prop]
theorem bitsMapWithInput {list : α → List Bool} {f : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hf : ComputableTidilyInPolyTime (fun p : α × Bool => f p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).map (f a)) input encBits :=
  mapToBitsWithInput (bitsToList.comp hlist) hf

/-- Filter a raw bit string with a predicate that may capture its original input. -/
@[fun_prop]
theorem bitsFilterWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).filter (test a)) input encBits :=
  listToBits.comp (filterWithInput (bitsToList.comp hlist) htest)

/-- Count occurrences of a computed bit in a raw bit string. -/
@[fun_prop]
theorem bitsCountWithInput {list : α → List Bool} {value : α → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hvalue : ComputableTidilyInPolyTime value input encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).count (value x)) input encUnary := by
  simp only [List.count_eq_countP]
  apply countPWith (encA := encBool) (test := fun p : α × Bool => p.2 == value p.1)
    (hpar := id') (hlist := hlist)
  fun_prop

/-- Test whether any bit satisfies a captured predicate. -/
@[fun_prop]
theorem bitsAnyWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).any (test a)) input encBool :=
  anyWithEncoding htest id' hlist

/-- A Boolean fold has constant-sized state, so no separate state bound is needed. -/
@[fun_prop]
theorem bitsFoldlWithInput (op : Bool → Bool → Bool) {list : α → List Bool} {init : α → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hinit : ComputableTidilyInPolyTime init input encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).foldl op (init a)) input encBool :=
  foldl' (encA := encBool) hlist hinit (of_finite (fun p : Bool × Bool => op p.1 p.2))
    (.const 1) (fun _ _ _ => by simp)

/-- Apply a fixed Boolean operation pointwise, stopping at the shorter word. -/
@[fun_prop]
theorem bitsZipWith (op : Bool → Bool → Bool) :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => p.1.zipWith op p.2)
      (encPair encBits encBits) encBits := by
  have hop : ComputableTidilyInPolyTime (fun p : Bool × Bool => op p.1 p.2)
      (encPair encBool encBool) encBool := of_finite _
  have h : ComputableTidilyInPolyTime (fun p : List Bool × List Bool =>
      (List.range (min p.1.length p.2.length)).map
        (fun i => op (p.1.getD i false) (p.2.getD i false)))
      (encPair encBits encBits) encBits := by fun_prop
  convert h using 1
  funext p
  apply List.ext_getElem (by simp)
  intro i hleft hright
  simp only [List.length_zipWith, Nat.lt_min] at hleft
  simp [List.getD, List.getElem?_eq_getElem hleft.1, List.getElem?_eq_getElem hleft.2]

/-- Pointwise operations on computed words, with both intermediate encodings fixed. -/
@[fun_prop]
theorem bitsZipWithInput (op : Bool → Bool → Bool) {left right : α → List Bool}
    (hleft : ComputableTidilyInPolyTime left input encBits)
    (hright : ComputableTidilyInPolyTime right input encBits) :
    ComputableTidilyInPolyTime (fun a => (left a).zipWith op (right a)) input encBits :=
  (bitsZipWith op).comp (hleft.prod hright)

/-- Strict majority uses filtering, length, unary multiplication and comparison. -/
@[fun_prop]
theorem bitsStrictMajority : ComputableTidilyInPolyTime Cslib.BitString.listStrictMajority
    encBits encBool := by
  unfold Cslib.BitString.listStrictMajority
  fun_prop

/-- Strict majority of computed votes fixes the intermediate raw-word encoding. -/
@[fun_prop]
theorem bitsStrictMajorityWithInput {votes : α → List Bool}
    (hvotes : ComputableTidilyInPolyTime votes input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listStrictMajority (votes a))
      input encBool :=
  bitsStrictMajority.comp hvotes

/-- Generate one coordinate mask from its unary width and index. -/
@[fun_prop]
theorem bitsSingle : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => Cslib.BitString.listSingle p.1 p.2)
    (encPair encUnary encUnary) encBits := by
  unfold Cslib.BitString.listSingle
  fun_prop

/-- Generate all coordinate masks, charging for their quadratic total size. -/
@[fun_prop]
theorem bitsSingles : ComputableTidilyInPolyTime Cslib.BitString.listSingles
    encUnary (encList encBits) := by
  unfold Cslib.BitString.listSingles
  fun_prop

/-- Sum selected rows with a shrinking selector and an accumulator that never grows. -/
@[fun_prop]
theorem bitsXorSelected : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool × List (List Bool) =>
      Cslib.BitString.listXorSelected p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits (encList encBits))) encBits := by
  let advance (state : List Bool × List Bool) (row : List Bool) :=
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2)
  have hfold : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List (List Bool) =>
        p.2.2.foldl advance (p.2.1, List.replicate p.1 false))
      (encPair encUnary (encPair encBits (encList encBits))) (encPair encBits encBits) := by
    apply foldl_of_bounded_growth (encA := encBits) (encL := encList encBits) (growth := 0)
    · fun_prop
    · fun_prop
    · unfold advance; fun_prop
    · rintro ⟨selector, value⟩ row
      simp only [advance, length_encPair, encBits_apply, List.length_tail]
      split
      · rw [List.length_zipWith]; lia
      · lia
  exact hfold.snd'

/-- Enumerate words only when their complete encoded size is polynomially bounded.
This does not claim polynomial time in the number of enumerated bits. -/
theorem bitsEnumList {count : α → ℕ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    {size : ℕ → ℕ} (hsize : Cslib.PolynomiallyBounded size)
    (hbudget : ∀ a, 2 ^ count a * (2 * count a + 1) ≤ size (input a).length) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.enumList (count a))
      input (encList encBits) := by
  let extend (values : List (List Bool)) :=
    values.flatMap (fun word => [false :: word, true :: word])
  have hstep : ComputableTidilyInPolyTime extend (encList encBits) (encList encBits) := by
    unfold extend
    fun_prop
  have hiterate (n : ℕ) : extend^[n] [[]] = Cslib.BitString.enumList n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, Cslib.BitString.enumList_succ]
  have h := iterate (init := fun _ => [[]]) hcount (const [[]]) hstep
    (.of_polynomiallyBounded _ hsize) (fun a index hi => by
      rw [hiterate, length_encList_enumList]
      exact (Nat.mul_le_mul (Nat.pow_le_pow_right two_pos hi)
        (by lia : 2 * index + 1 ≤ 2 * count a + 1)).trans (hbudget a))
  simpa only [hiterate] using h

/-- Read a row of a computed word, including the cost of padding a short word. -/
@[fun_prop]
theorem bitsRowWithInput {width row : α → ℕ} {word : α → List Bool}
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hrow : ComputableTidilyInPolyTime row input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listRow (width a) (row a) (word a))
      input encBits := by
  unfold Cslib.BitString.listRow
  fun_prop

/-- Extract rows from a word with polynomial-time unary dimensions. -/
@[fun_prop]
theorem bitsRowsWithInput {count width : α → ℕ} {word : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listRows (count a) (width a) (word a))
      input (encList encBits) := by
  unfold Cslib.BitString.listRows
  fun_prop

/-- Variable-width XOR uses runtime lookup and ordinary Boolean folds. -/
@[fun_prop]
theorem bitsXorWithInput {α : Type} {input : α ↪ List Bool}
    {width : α → ℕ} {words : α → List (List Bool)}
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hwords : ComputableTidilyInPolyTime words input (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listXor (width a) (words a))
      input encBits := by
  unfold Cslib.BitString.listXor
  fun_prop

/-- Lexicographic comparison of equal-length words is polynomial-time. -/
@[fun_prop]
theorem bitsWordLt {α : Type} {input : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableTidilyInPolyTime x input encBits)
    (hy : ComputableTidilyInPolyTime y input encBits) :
    ComputableTidilyInPolyTime (fun c => Cslib.BitString.wordLt (x c) (y c)) input encBool := by
  unfold Cslib.BitString.wordLt
  fun_prop

/-- Decode arbitrary most-significant-first bit words to binary naturals. -/
@[fun_prop]
theorem bitsBinaryValue :
    ComputableTidilyInPolyTime Cslib.BitString.binaryValue encBits encNat := by
  simpa only [Function.comp_def, ofBits_reverse] using bitsToNat.comp bitsReverse

end ComputableTidilyInPolyTime

end Turing.MultiTapeTM

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Test whether any bit satisfies a captured predicate. -/
@[fun_prop]
theorem bitsAnyWithInput {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun (p : α × Bool) => test p.1 p.2)
  (encPair input encBool)
  encBool) :
    ComputableInPolyTime (fun (a : α) => (list a).any (test a)) input
  encBool :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsAnyWithInput α input list test
      hlist.tidy htest.tidy)

/-- Self-delimiting padding uses ordinary framing and unary arithmetic. -/
@[fun_prop]
theorem bitsPadWord {α : Type}
    {input : α ↪ List Bool}
    {bound : α → ℕ}
    {word : α → List Bool}
    (hbound : ComputableInPolyTime bound input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime
  (fun (a : α) => Cslib.BitString.padWord (bound a) (word a)) input
  encBits :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsPadWord α input bound word
      hbound.tidy hword.tidy)

/-- Repeat a fixed bit a unary number of times, including zero repetitions. -/
@[fun_prop]
theorem bitsReplicate (bit : Bool) :
    ComputableInPolyTime (fun n => List.replicate n bit) encUnary encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsReplicate bit)

/-- Apply a fixed Boolean operation pointwise to two computed raw words. The result stops at
whichever word ends first; the two certificates retain their raw bit-string encoding. -/
@[fun_prop]
theorem bitsZipWithInput (op : Bool → Bool → Bool) {α : Type} {input : α ↪ List Bool}
    {left right : α → List Bool}
    (hleft : ComputableInPolyTime left input encBits)
    (hright : ComputableInPolyTime right input encBits) :
    ComputableInPolyTime (fun a => (left a).zipWith op (right a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsZipWithInput op hleft.tidy hright.tidy)

/-- Read a row of a computed word, charging padding and both computed unary indices. -/
@[fun_prop]
theorem bitsRowWithInput {α : Type} {input : α ↪ List Bool}
    {width row : α → ℕ} {word : α → List Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hrow : ComputableInPolyTime row input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.listRow (width a) (row a) (word a))
      input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsRowWithInput hwidth.tidy hrow.tidy hword.tidy)

/-- Frame the existing input encoding, charging every delimiter. -/
@[fun_prop]
theorem bitsFrame {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun a => Turing.MultiTapeTM.frame (enc a)) enc encBits := by
  have henc : ComputableInPolyTime (fun a => enc a) enc encBits := of_eq fun _ => rfl
  exact frame.comp henc

/-- Saturating binary decoding to unary is polynomial time on arbitrary input words. -/
@[fun_prop]
theorem bitsBoundedBinaryValue : ComputableInPolyTime
    (fun p : ℕ × List Bool => Cslib.BitString.boundedBinaryValue p.1 p.2)
    (encPair encUnary encBits) encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.bitsBoundedBinaryValue)

/-- Decode computed bits under a computed unary cap, fixing both intermediate encodings. -/
@[fun_prop]
theorem bitsBoundedBinaryValueWithInput {α : Type} {input : α ↪ List Bool}
    {cap : α → ℕ} {word : α → List Bool}
    (hcap : ComputableInPolyTime cap input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.boundedBinaryValue (cap a) (word a))
      input encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput (α := α)
    (input := input)
    (cap := cap)
    (word := word)
    (hcap := hcap.tidy)
    (hword := hword.tidy))

/-- Convert a binary value to unary under a computed unary bound. -/
theorem binary_to_unary_bounded {α : Type} {input : α ↪ List Bool} {value bound : α → ℕ}
    (hvalue : ComputableInPolyTime value input encNat)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hle : ∀ a, value a ≤ bound a) :
    ComputableInPolyTime value input encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.binary_to_unary_bounded (α := α)
    (input := input)
    (value := value)
    (bound := bound)
    (hvalue := hvalue.tidy)
    (hbound := hbound.tidy)
    (hle := hle))

/-- Convert a raw bit string to the framed list encoding. -/
@[fun_prop]
theorem bitsToList : ComputableInPolyTime (fun l => l) encBits (encList encBool) :=
  .of_tidy (ComputableTidilyInPolyTime.bitsToList)

/-- Optional lookup in a raw bit string, fixing the representation of the returned bit. -/
@[fun_prop]
theorem bitsGetElem? {α : Type} {input : α ↪ List Bool}
    {list : α → List Bool} {index : α → ℕ}
    (hlist : ComputableInPolyTime list input encBits)
    (hindex : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime (fun x => (list x)[index x]?) input (encOption encBool) :=
  .of_tidy (ComputableTidilyInPolyTime.bitsGetElem? (α := α)
    (input := input)
    (list := list)
    (index := index)
    (hlist := hlist.tidy)
    (hindex := hindex.tidy))

/-- Concatenate computed raw words, fixing the intermediate list encoding before proof search. -/
@[fun_prop]
theorem bitsFlatten {words : α → List (List Bool)}
    (hwords : ComputableInPolyTime words input (encList encBits)) :
    ComputableInPolyTime (fun a => (words a).flatten) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsFlatten (words := words) (hwords := hwords.tidy))

/-- Map a captured Boolean-valued function over a framed list, emitting a raw bit string. -/
@[fun_prop]
theorem mapToBitsWithInput {β : Type} {enc : β ↪ List Bool} {list : α → List β}
    {f : α → β → Bool}
    (hlist : ComputableInPolyTime list input (encList enc))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2)
      (encPair input enc) encBool) :
    ComputableInPolyTime (fun a => (list a).map (f a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.mapToBitsWithInput (β := β)
    (enc := enc)
    (list := list)
    (f := f)
    (hlist := hlist.tidy)
    (hf := hf.tidy))

/-- Concatenate captured raw bit strings over a framed list. The complete intermediate words
and their framing are charged before concatenation. Apply this rule explicitly: registering both
raw and framed `flatMap` outputs makes existing enumeration proof search exceed its limit. -/
theorem flatMapToBitsWithInput {β : Type} {enc : β ↪ List Bool} {list : α → List β}
    {f : α → β → List Bool}
    (hlist : ComputableInPolyTime list input (encList enc))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2)
      (encPair input enc) encBits) :
    ComputableInPolyTime (fun a => (list a).flatMap (f a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.flatMapToBitsWithInput (β := β)
    (enc := enc)
    (list := list)
    (f := f)
    (hlist := hlist.tidy)
    (hf := hf.tidy))

/-- Emit a computed unary number of low-order digits of a computed binary natural. The width
charges every output bit, including leading zero digits. -/
@[fun_prop]
theorem bitsLow {width value : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hvalue : ComputableInPolyTime value input encNat) :
    ComputableInPolyTime (fun a => Cslib.BitString.lowBits (width a) (value a))
      input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsLow (width := width)
    (value := value)
    (hwidth := hwidth.tidy)
    (hvalue := hvalue.tidy))

/-- Map a captured Boolean operation over a raw bit string. -/
@[fun_prop]
theorem bitsMapWithInput {list : α → List Bool} {f : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (hf : ComputableInPolyTime (fun p : α × Bool => f p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableInPolyTime (fun a => (list a).map (f a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsMapWithInput (list := list)
    (f := f)
    (hlist := hlist.tidy)
    (hf := hf.tidy))

/-- Filter a raw bit string with a predicate that may capture its original input. -/
@[fun_prop]
theorem bitsFilterWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableInPolyTime (fun a => (list a).filter (test a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsFilterWithInput (list := list)
    (test := test)
    (hlist := hlist.tidy)
    (htest := htest.tidy))

/-- Count predicate matches in a raw bit string, including a captured input. -/
@[fun_prop]
theorem bitsCountPWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableInPolyTime (fun x => (list x).countP (test x)) input encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.countPWith htest.tidy .id' hlist.tidy)

/-- Count occurrences of a computed bit in a raw bit string. -/
@[fun_prop]
theorem bitsCountWithInput {list : α → List Bool} {value : α → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (hvalue : ComputableInPolyTime value input encBool) :
    ComputableInPolyTime (fun x => (list x).count (value x)) input encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.bitsCountWithInput (list := list)
    (value := value)
    (hlist := hlist.tidy)
    (hvalue := hvalue.tidy))

/-- Test whether every bit satisfies a captured predicate. -/
@[fun_prop]
theorem bitsAllWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableInPolyTime (fun a => (list a).all (test a)) input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.allWithEncoding htest.tidy .id' hlist.tidy)

/-- A Boolean fold has constant-sized state, so no separate state bound is needed. -/
@[fun_prop]
theorem bitsFoldlWithInput (op : Bool → Bool → Bool) {list : α → List Bool} {init : α → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (hinit : ComputableInPolyTime init input encBool) :
    ComputableInPolyTime (fun a => (list a).foldl op (init a)) input encBool :=
  foldl' (encA := encBool) hlist hinit (of_finite (fun p : Bool × Bool => op p.1 p.2))
    (.const 1) (fun _ _ _ => by simp)

/-- Apply a fixed Boolean operation pointwise, stopping at the shorter word. -/
@[fun_prop]
theorem bitsZipWith (op : Bool → Bool → Bool) :
    ComputableInPolyTime (fun p : List Bool × List Bool => p.1.zipWith op p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsZipWith (op := op))

/-- Strict majority uses filtering, length, unary multiplication and comparison. -/
@[fun_prop]
theorem bitsStrictMajority : ComputableInPolyTime Cslib.BitString.listStrictMajority
    encBits encBool :=
  .of_tidy (ComputableTidilyInPolyTime.bitsStrictMajority)

/-- Strict majority of computed votes fixes the intermediate raw-word encoding. -/
@[fun_prop]
theorem bitsStrictMajorityWithInput {votes : α → List Bool}
    (hvotes : ComputableInPolyTime votes input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.listStrictMajority (votes a))
      input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.bitsStrictMajorityWithInput (votes := votes)
    (hvotes := hvotes.tidy))

/-- The training test is polynomial time in the vote list and its supplied label. -/
@[fun_prop]
theorem bitsNonpositiveMarginWithInput
    {votes : α → List Bool} {truth : α → Bool}
    (hvotes : ComputableInPolyTime votes input encBits)
    (htruth : ComputableInPolyTime truth input encBool) :
    ComputableInPolyTime (fun a => Cslib.BitString.listNonpositiveMargin (votes a) (truth a))
      input encBool := by
  unfold Cslib.BitString.listNonpositiveMargin
  fun_prop

/-- Generate one coordinate mask from its unary width and index. -/
@[fun_prop]
theorem bitsSingle : ComputableInPolyTime
    (fun p : ℕ × ℕ => Cslib.BitString.listSingle p.1 p.2)
    (encPair encUnary encUnary) encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsSingle)

/-- Generate all coordinate masks, charging for their quadratic total size. -/
@[fun_prop]
theorem bitsSingles : ComputableInPolyTime Cslib.BitString.listSingles
    encUnary (encList encBits) :=
  .of_tidy (ComputableTidilyInPolyTime.bitsSingles)

/-- Sum selected rows with a shrinking selector and an accumulator that never grows. -/
@[fun_prop]
theorem bitsXorSelected : ComputableInPolyTime
    (fun p : ℕ × List Bool × List (List Bool) =>
      Cslib.BitString.listXorSelected p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits (encList encBits))) encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsXorSelected)

/-- Enumerate words only when their complete encoded size is polynomially bounded.
This does not claim polynomial time in the number of enumerated bits. -/
theorem bitsEnumList {count : α → ℕ}
    (hcount : ComputableInPolyTime count input encUnary)
    {size : ℕ → ℕ} (hsize : Cslib.PolynomiallyBounded size)
    (hbudget : ∀ a, 2 ^ count a * (2 * count a + 1) ≤ size (input a).length) :
    ComputableInPolyTime (fun a => Cslib.BitString.enumList (count a))
      input (encList encBits) :=
  .of_tidy (ComputableTidilyInPolyTime.bitsEnumList (count := count)
    (hcount := hcount.tidy)
    (size := size)
    (hsize := hsize)
    (hbudget := hbudget))

/-- Extract rows from a word with polynomial-time unary dimensions. -/
@[fun_prop]
theorem bitsRowsWithInput {count width : α → ℕ} {word : α → List Bool}
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.listRows (count a) (width a) (word a))
      input (encList encBits) :=
  .of_tidy (ComputableTidilyInPolyTime.bitsRowsWithInput (count := count)
    (width := width)
    (word := word)
    (hcount := hcount.tidy)
    (hwidth := hwidth.tidy)
    (hword := hword.tidy))

/-- Variable-width XOR uses runtime lookup and ordinary Boolean folds. -/
@[fun_prop]
theorem bitsXorWithInput {α : Type} {input : α ↪ List Bool}
    {width : α → ℕ} {words : α → List (List Bool)}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hwords : ComputableInPolyTime words input (encList encBits)) :
    ComputableInPolyTime (fun a => Cslib.BitString.listXor (width a) (words a))
      input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsXorWithInput (α := α)
    (input := input)
    (width := width)
    (words := words)
    (hwidth := hwidth.tidy)
    (hwords := hwords.tidy))

/-- Lexicographic comparison of equal-length words is polynomial-time. -/
@[fun_prop]
theorem bitsWordLt {α : Type} {input : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun c => Cslib.BitString.wordLt (x c) (y c)) input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.bitsWordLt (α := α)
    (input := input)
    (x := x)
    (y := y)
    (hx := hx.tidy)
    (hy := hy.tidy))

/-- Decode arbitrary most-significant-first bit words to binary naturals. -/
@[fun_prop]
theorem bitsBinaryValue :
    ComputableInPolyTime Cslib.BitString.binaryValue encBits encNat :=
  .of_tidy (ComputableTidilyInPolyTime.bitsBinaryValue)

end Turing.MultiTapeTM.ComputableInPolyTime


