-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Padding
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Padding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:42.100511+00:00
-- url     : https://prove2.me/theorems/71b545eb-2212-4673-ad56-16460a90e2c7
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Padding — Self-delimiting padding of bounded words
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Padding` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The machine calculus's existing frame encoding makes bounded words equally long without
--   identifying distinct words. Words longer than the bound retain their complete frame. This
--   representation bridge is separate from the pure bit-string foundations and from its
--   polynomial-time certificate in
--   `Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/BitString.lean`.
--
--   ### Main definitions
--
--   * `Cslib.BitString.padWord`: frame a word and pad it to a supplied width bound.
--
--   ### Main results
--
--   * `Cslib.BitString.word_eq_of_padWord_eq`: injectivity even across different bounds.
--   * `Cslib.BitString.length_padWord`: bounded words have length `2 * bound + 1`.
--   * `Cslib.BitString.word_eq_of_paddedBits_eq`: bounded words embed into a fixed finite cube.
--
--   ### References
--
--   Adapted from Computability/Probabilistic/BitString.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy machine frame encoding.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Padding`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Padding.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Padding` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Self-delimiting padding of bounded words

The machine calculus's existing frame encoding makes bounded words equally long without
identifying distinct words. Words longer than the bound retain their complete frame. This
representation bridge is separate from the pure bit-string foundations and from its
polynomial-time certificate in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/BitString.lean`.

## Main definitions

* `Cslib.BitString.padWord`: frame a word and pad it to a supplied width bound.

## Main results

* `Cslib.BitString.word_eq_of_padWord_eq`: injectivity even across different bounds.
* `Cslib.BitString.length_padWord`: bounded words have length `2 * bound + 1`.
* `Cslib.BitString.word_eq_of_paddedBits_eq`: bounded words embed into a fixed finite cube.

## References

Adapted from Computability/Probabilistic/BitString.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy machine frame encoding.
-/

@[expose] public section

namespace Cslib.BitString

open Turing.MultiTapeTM

/-- Pad a framed word to `2 * bound + 1` bits when it fits. Longer words are not truncated. -/
def padWord (bound : ℕ) (word : List Bool) : List Bool :=
  frame word ++ List.replicate (2 * (bound - word.length)) false

/-- Padding never identifies distinct words, even when their bounds differ. -/
theorem word_eq_of_padWord_eq {bound bound' : ℕ} {word word' : List Bool}
    (h : padWord bound word = padWord bound' word') : word = word' :=
  (frame_append_inj h).1

/-- Every word within the supplied bound has the same padded length. -/
theorem length_padWord {bound : ℕ} {word : List Bool} (h : word.length ≤ bound) :
    (padWord bound word).length = 2 * bound + 1 := by
  simp only [padWord, List.length_append, length_frame, List.length_replicate]
  lia

/-- Concatenating bounded, padded words has a length determined solely by their count. -/
theorem length_flatten_padWord (bound : ℕ) (words : List (List Bool))
    (hbound : ∀ word ∈ words, word.length ≤ bound) :
    ((words.map (padWord bound)).flatten).length = words.length * (2 * bound + 1) := by
  induction words with
  | nil => simp
  | cons word rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hbound
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      length_padWord hbound.1, ih hbound.2, List.length_cons]
    lia

/-- Padding embeds bounded words into a fixed finite bit-string space. -/
theorem word_eq_of_paddedBits_eq {bound : ℕ} {left right : List Bool}
    (hleft : left.length ≤ bound) (hright : right.length ≤ bound)
    (h : ofList (2 * bound + 1) (padWord bound left) =
      ofList (2 * bound + 1) (padWord bound right)) : left = right := by
  apply word_eq_of_padWord_eq
  simpa only [ofFn_ofList (length_padWord hleft), ofFn_ofList (length_padWord hright)] using
    congrArg List.ofFn h

end Cslib.BitString


