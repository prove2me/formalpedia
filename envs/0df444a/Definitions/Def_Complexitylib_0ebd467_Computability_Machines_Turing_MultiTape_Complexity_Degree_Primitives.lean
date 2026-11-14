-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Primitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Primitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:20.984541+00:00
-- url     : https://prove2.me/theorems/f4392b58-99bd-43d2-9856-7c16995bd119
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives — Direct primitives for plain degree bounds
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These rules retain independent cost and encoded-output degrees. Constants have cost degree one
--   and output degree zero; encoded equality uses the upstream copy machine. Output and input
--   encoding transports reuse the same realizing machine and preserve both degrees, including zero.
--   No higher computability calculus is used in their proofs.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInDegree.const`: a constant encoded result.
--   * `Turing.MultiTapeTM.ComputableInDegree.of_finite`: a function on any finite input type.
--   * `Turing.MultiTapeTM.ComputableInDegree.of_eq`: copy an unchanged encoded word.
--   * `Turing.MultiTapeTM.ComputableInDegree.of_enc_eq`, `.of_encIn_eq`: transport encoded equality.
--
--   ### References
--
--   Uses cslib's constant and copy machines and the independent degree bounds of this library.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Primitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Degree/Primitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Combinators_AlmostConstant
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Combinators_Id
import Mathlib.Data.Fintype.Lattice

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct primitives for plain degree bounds

These rules retain independent cost and encoded-output degrees. Constants have cost degree one
and output degree zero; encoded equality uses the upstream copy machine. Output and input
encoding transports reuse the same realizing machine and preserve both degrees, including zero.
No higher computability calculus is used in their proofs.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.const`: a constant encoded result.
* `Turing.MultiTapeTM.ComputableInDegree.of_finite`: a function on any finite input type.
* `Turing.MultiTapeTM.ComputableInDegree.of_eq`: copy an unchanged encoded word.
* `Turing.MultiTapeTM.ComputableInDegree.of_enc_eq`, `.of_encIn_eq`: transport encoded equality.

## References

Uses cslib's constant and copy machines and the independent degree bounds of this library.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {d e : ℕ}

/-- A fixed encoded result has linear cost and constant encoded-output growth. -/
theorem const (b : β) : ComputableInDegree (fun _ : α => b) encIn encMid 1 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  exact ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, h⟩,
    DegreeBounded.const (encMid b).length⟩

/-- A function on a finite input type has linear cost and constant output growth.
The machine has constant time and zero workspace; no inhabitedness assumption is needed. -/
theorem of_finite [Finite α] (f : α → β) : ComputableInDegree f encIn encMid 1 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encMid) f
  refine ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, h⟩, ?_⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, fun a => isEmptyElim a⟩
  · obtain ⟨a₀, ha₀⟩ := Finite.exists_max fun a => (encMid (f a)).length
    exact ⟨_, fun a => by simpa using ha₀ a⟩

/-- Copy a word whose output encoding is exactly its input encoding. -/
theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableInDegree f encIn encMid 1 1 := by
  obtain ⟨k, State, hfin, tm, htm⟩ := computableInTimeAndSpace_id (enc := encIn)
  refine ⟨⟨fun a => (encIn a).length + 1, fun _ => 0,
    DegreeBounded.self.add_const 1, DegreeBounded.const 0,
    k, State, hfin, tm, fun a => ?_⟩, ?_⟩
  · simpa only [h a, id_eq] using htm a
  · exact DegreeBounded.self.mono fun a => by rw [h a]

/-- Equal output words retain the realizing machine and both independent degrees. -/
theorem of_enc_eq {f : α → β} {g : α → γ}
    (hf : ComputableInDegree f encIn encMid d e) (h : ∀ a, encOut (g a) = encMid (f a)) :
    ComputableInDegree g encIn encOut d e := by
  obtain ⟨⟨t, s, ht, hs, k, State, hfin, tm, htm⟩, hl⟩ := hf
  refine ⟨⟨t, s, ht, hs, k, State, hfin, tm, fun a => ?_⟩, ?_⟩
  · simpa only [h a] using htm a
  · exact hl.mono fun a => by rw [h a]

/-- An input map preserving the complete encoded word retains the same machine and degrees.
The semantic map needs no separate computational assumption: the machine sees the same word. -/
theorem of_encIn_eq {α' : Type*} {encIn' : α' ↪ List Bool} {f : α → β}
    (map : α' → α) (henc : ∀ a, encIn' a = encIn (map a))
    (hf : ComputableInDegree f encIn encMid d e) :
    ComputableInDegree (f ∘ map) encIn' encMid d e := by
  obtain ⟨⟨t, s, ⟨ct, ht⟩, ⟨cs, hs⟩, k, State, hfin, tm, htm⟩, ⟨cl, hl⟩⟩ := hf
  refine ⟨⟨fun a => t (map a), fun a => s (map a),
    ⟨ct, fun a => ?_⟩, ⟨cs, fun a => ?_⟩, k, State, hfin, tm, fun a => ?_⟩,
    ⟨cl, fun a => ?_⟩⟩
  · simpa only [henc a] using ht (map a)
  · simpa only [henc a] using hs (map a)
  · simpa only [henc a, Function.comp_apply] using htm (map a)
  · simpa only [henc a, Function.comp_apply] using hl (map a)

/-- Restricting inputs preserves the same machine and both degrees. -/
theorem restrict {f : α → β} (h : ComputableInDegree f encIn encMid d e) (p : α → Prop) :
    ComputableInDegree (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn) encMid d e :=
  h.of_encIn_eq Subtype.val fun _ => rfl

end Turing.MultiTapeTM.ComputableInDegree


