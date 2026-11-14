-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:38.239334+00:00
-- url     : https://prove2.me/theorems/3a7b5d27-f353-4421-ad92-e726200ddadb
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic — Pure framed words
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The original framing definitions and laws are moved unchanged below encoding-machine
--   capabilities so their machine implementations do not create an import cycle.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Frame/Basic.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.List.Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Pure framed words

The original framing definitions and laws are moved unchanged below encoding-machine
capabilities so their machine implementations do not create an import cycle.
-/

namespace Turing.MultiTapeTM

/-! ### Framed words -/

/-- Each symbol `b` of `w` as `[true, b]`, followed by `[false]`. -/
@[expose] public def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- The word framed at the start of `v`, see `Turing.MultiTapeTM.frame`. -/
@[expose] public def unframe : List Bool → List Bool
  | true :: b :: v => b :: unframe v
  | _ => []

/-- What follows the frame at the start of `v`, see `Turing.MultiTapeTM.frame`. -/
@[expose] public def dropFrame : List Bool → List Bool
  | true :: _ :: v => dropFrame v
  | false :: v => v
  | _ => []

@[simp]
public lemma frame_nil : frame [] = [false] := rfl

@[simp]
public lemma frame_cons (b : Bool) (w : List Bool) : frame (b :: w) = true :: b :: frame w := rfl

@[simp]
public lemma length_frame (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w <;> simp [*]; omega

@[simp]
public lemma unframe_frame_append (w u : List Bool) : unframe (frame w ++ u) = w := by
  induction w <;> simp [unframe, *]

@[simp]
public lemma unframe_frame (w : List Bool) : unframe (frame w) = w := by
  simpa using unframe_frame_append w []

@[simp]
public lemma dropFrame_frame_append (w u : List Bool) : dropFrame (frame w ++ u) = u := by
  induction w <;> simp [dropFrame, *]

/-- A framed word followed by another word determines both. -/
public theorem frame_append_inj {w w' u u' : List Bool} (h : frame w ++ u = frame w' ++ u') :
    w = w' ∧ u = u' :=
  ⟨by simpa using congrArg unframe h, by simpa using congrArg dropFrame h⟩

/-- Framing is injective. -/
public theorem frame_injective : Function.Injective frame := fun _ _ h =>
  (frame_append_inj (u := []) (u' := []) (by simpa using h)).1

@[simp]
public lemma frame_ne_nil (w : List Bool) : frame w ≠ [] := by simp [frame]

end Turing.MultiTapeTM


