-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:52:48.643892+00:00
-- url     : https://prove2.me/theorems/febd66d8-7a60-4336-a402-4d7add31ef46
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length — Lengths of encoded lists
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The framed encoding of a list (`Turing.MultiTapeTM.encList`) spends `2 * |enc a| + 1` symbols on
--   each element `a`. In particular the sum of the lengths of its encoded elements is no longer than
--   the encoding, as is the list itself (`Turing.MultiTapeTM.length_le_length_encList`). Such bounds
--   are what a reduction needs to bound the size of its output, or a verifier the length of a
--   certificate, in terms of the input.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.length_encList`: the exact length.
--   * `Turing.MultiTapeTM.sum_length_le_length_encList`: the encoded elements are no longer, in total,
--     than the encoded list.
--   * `Turing.MultiTapeTM.length_unframe_add_dropFrame_le`: the unframed prefix and remaining suffix
--     of any bit list satisfy `2 * (unframe v).length + (dropFrame v).length ≤ v.length`.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Length.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Lengths of encoded lists

The framed encoding of a list (`Turing.MultiTapeTM.encList`) spends `2 * |enc a| + 1` symbols on
each element `a`. In particular the sum of the lengths of its encoded elements is no longer than
the encoding, as is the list itself (`Turing.MultiTapeTM.length_le_length_encList`). Such bounds
are what a reduction needs to bound the size of its output, or a verifier the length of a
certificate, in terms of the input.

## Main results

* `Turing.MultiTapeTM.length_encList`: the exact length.
* `Turing.MultiTapeTM.sum_length_le_length_encList`: the encoded elements are no longer, in total,
  than the encoded list.
* `Turing.MultiTapeTM.length_unframe_add_dropFrame_le`: the unframed prefix and remaining suffix
  of any bit list satisfy `2 * (unframe v).length + (dropFrame v).length ≤ v.length`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α : Type*} (enc : α ↪ List Bool)

theorem length_encList (l : List α) :
    (encList enc l).length = (l.map fun a => 2 * (enc a).length + 1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Reversing a list preserves the full encoded size, including each element's framing. -/
@[simp] theorem length_encList_reverse (l : List α) :
    (encList enc l.reverse).length = (encList enc l).length := by
  simp only [length_encList, List.map_reverse, List.sum_reverse]

/-- The encoded elements of a list are no longer, in total, than the encoded list. -/
theorem sum_length_le_length_encList (l : List α) :
    (l.map fun a => (enc a).length).sum ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; omega

/-- The unframed prefix and remaining suffix of any bit list satisfy
`2 * (unframe v).length + (dropFrame v).length ≤ v.length`. -/
theorem length_unframe_add_dropFrame_le :
    ∀ v : List Bool, 2 * (unframe v).length + (dropFrame v).length ≤ v.length
  | [] | [true] => by simp [unframe, dropFrame]
  | false :: v => by simp [unframe, dropFrame]
  | true :: b :: v => by
    have ih := length_unframe_add_dropFrame_le v
    simp only [unframe, dropFrame, List.length_cons]
    omega

end Turing.MultiTapeTM


