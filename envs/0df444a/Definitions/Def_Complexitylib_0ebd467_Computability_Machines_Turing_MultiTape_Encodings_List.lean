-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:32.969822+00:00
-- url     : https://prove2.me/theorems/e2c74f5d-7d17-460f-a537-7e571fd32bd0
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.List — Encodings of lists
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.List` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `encList enc` encodes a list as the concatenation of its framed elements
--   (`Turing.MultiTapeTM.frame`), for any encoding `enc` of the elements. Lists of Booleans also have
--   the plain encoding `encBits`, the list itself, which is the concatenation of the elements encoded by
--   `Turing.MultiTapeTM.encBool`. Both have the capabilities of `Turing.MultiTapeTM.ListEncoding`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.encList`: the concatenation of the framed elements.
--   * `Turing.MultiTapeTM.encBits`: lists of Booleans encoded as themselves.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/List.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.List` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Encodings of lists

`encList enc` encodes a list as the concatenation of its framed elements
(`Turing.MultiTapeTM.frame`), for any encoding `enc` of the elements. Lists of Booleans also have
the plain encoding `encBits`, the list itself, which is the concatenation of the elements encoded by
`Turing.MultiTapeTM.encBool`. Both have the capabilities of `Turing.MultiTapeTM.ListEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encList`: the concatenation of the framed elements.
* `Turing.MultiTapeTM.encBits`: lists of Booleans encoded as themselves.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Lists encoded as the concatenation of their framed elements. -/
@[expose] public def encList (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨fun l => l.flatMap (frame ∘ enc), fun l l' h => by
    induction l generalizing l' with
    | nil => cases l' <;> simp_all
    | cons a l ih =>
      cases l' with
      | nil => simp at h
      | cons a' l' => rw [enc.injective (frame_append_inj h).1, ih _ (frame_append_inj h).2]⟩

variable {enc : α ↪ List Bool}

@[simp]
public lemma encList_nil : encList enc [] = [] := rfl

@[simp]
public lemma encList_cons (a : α) (l : List α) :
    encList enc (a :: l) = frame (enc a) ++ encList enc l := rfl

public instance : ListEncoding enc (encList enc) where
  headD d := .of_isEmpty_ite d (fun l hl => by cases l <;> simp_all)
    (.of_unframe fun ⟨l, hl⟩ => by cases l <;> simp at hl ⊢)
  tail := .of_dropFrame fun l => by cases l <;> simp [dropFrame]
  isEmpty := .of_isEmpty fun l => by cases l <;> simp

/-- Lists of Booleans encoded as themselves. -/
@[expose] public def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

@[simp]
public lemma encBits_apply (l : List Bool) : encBits l = l := rfl

public instance : ListEncoding encBool encBits where
  headD d := .of_isEmpty_ite d (fun l hl => by simp_all)
    (.of_take_one fun ⟨l, hl⟩ => by cases l; exacts [by simp at hl, rfl])
  tail := .of_tail fun _ => rfl
  isEmpty := .of_isEmpty fun _ => rfl

end Turing.MultiTapeTM


