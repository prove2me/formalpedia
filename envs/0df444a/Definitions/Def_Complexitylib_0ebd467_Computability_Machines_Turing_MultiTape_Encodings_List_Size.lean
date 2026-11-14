-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:07.808261+00:00
-- url     : https://prove2.me/theorems/187532ac-4c07-4a8c-bf93-7f8b4f737a68
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size — Size bounds for readable list encodings
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The pure interface and instances are moved unchanged from the quantitative fold provider.
--   The framed-list upper bound retains its original statement and proof from the list provider.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/List/Size.lean

/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger, Anton Kovsharov
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Size bounds for readable list encodings

The pure interface and instances are moved unchanged from the quantitative fold provider.
The framed-list upper bound retains its original statement and proof from the list provider.
-/

namespace Turing.MultiTapeTM

/-- A list encoding whose encoded lists are at least as long as their elements, their suffixes and
their lengths. -/
public class SizedListEncoding {α : Type*} (encA : α ↪ List Bool) (encL : List α ↪ List Bool) :
    Prop where
  length_le (l : List α) : l.length ≤ (encL l).length
  length_elem_le (l : List α) : ∀ a ∈ l, (encA a).length ≤ (encL l).length
  length_drop_le (l : List α) (i : ℕ) : (encL (l.drop i)).length ≤ (encL l).length

public instance {α : Type*} (enc : α ↪ List Bool) : SizedListEncoding enc (encList enc) where
  length_le l := by induction l <;> grind [encList_cons, length_frame]
  length_elem_le l a ha := by induction l <;> grind [encList_cons, length_frame]
  length_drop_le l i := ((List.drop_sublist i l).flatMap (frame ∘ enc)).length_le

public instance : SizedListEncoding encBool encBits where
  length_le l := by simp
  length_elem_le l a ha := by
    simp only [encBool_apply, List.length_singleton, encBits_apply]
    exact List.length_pos_of_mem ha
  length_drop_le l i := by simp

variable {α : Type}

/-- A list of elements of bounded size has bounded size. -/
public lemma length_encList_le (enc : α ↪ List Bool) (l : List α) {b : ℕ}
    (h : ∀ a ∈ l, (enc a).length ≤ b) : (encList enc l).length ≤ l.length * (2 * b + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h₁ := h a (List.mem_cons_self ..)
    have h₂ := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp only [encList_cons, List.length_append, length_frame, List.length_cons]
    nlinarith

/-- Sublists do not increase framed list encoding length. -/
public lemma length_encList_sublist {α : Type*} (enc : α ↪ List Bool) {l₁ l₂ : List α}
    (h : List.Sublist l₁ l₂) : (encList enc l₁).length ≤ (encList enc l₂).length :=
  (h.flatMap (frame ∘ enc)).length_le

/-- Elementwise encoding-length bounds lift across `List.map` on framed list encodings. -/
public lemma length_encList_map_le {α β : Type*} (ea : α ↪ List Bool) (eb : β ↪ List Bool)
    {f : α → β} {l : List α} (hf : ∀ x ∈ l, (eb (f x)).length ≤ (ea x).length) :
    (encList eb (l.map f)).length ≤ (encList ea l).length := by
  induction l with
  | nil => exact le_rfl
  | cons a ls ih =>
    have ha := hf a List.mem_cons_self
    have hls := ih fun x hx => hf x (List.mem_cons_of_mem a hx)
    simp only [List.map_cons, encList_cons, List.length_append, length_frame]; omega

end Turing.MultiTapeTM


