-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Basic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:22.540706+00:00
-- url     : https://prove2.me/theorems/5f480713-cb8b-40b7-a4c7-74f5c6bc90d8
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic — Word operations for encodings
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The building blocks of concrete encodings of pairs, options and lists, and their plain computability
--   in linear time and space (`Turing.MultiTapeTM.ComputableInDegree` with degrees `1 1`).
--
--   A word `w` is *framed* by writing each symbol `b` as `[true, b]` and appending `[false]`. A framed
--   word marks its own end, so it can be followed by any word and still be read back.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.frame`: the framed word.
--   * `Turing.MultiTapeTM.unframe`, `Turing.MultiTapeTM.dropFrame`: the word framed at the start of a
--     word, and what follows the frame.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.frame_append_inj`: a framed word followed by another word determines both.
--   * Functions that act on encoded values by `frame`, `unframe`, `dropFrame`, `List.cons true`,
--     `List.tail` or `List.take 1`, or that test the encoded value for emptiness, are computable
--     in linear time and space.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Basic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Basic.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Encoding
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearCodecPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FrameMachines

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Word operations for encodings

The building blocks of concrete encodings of pairs, options and lists, and their plain computability
in linear time and space (`Turing.MultiTapeTM.ComputableInDegree` with degrees `1 1`).

A word `w` is *framed* by writing each symbol `b` as `[true, b]` and appending `[false]`. A framed
word marks its own end, so it can be followed by any word and still be read back.

## Main definitions

* `Turing.MultiTapeTM.frame`: the framed word.
* `Turing.MultiTapeTM.unframe`, `Turing.MultiTapeTM.dropFrame`: the word framed at the start of a
  word, and what follows the frame.

## Main results

* `Turing.MultiTapeTM.frame_append_inj`: a framed word followed by another word determines both.
* Functions that act on encoded values by `frame`, `unframe`, `dropFrame`, `List.cons true`,
  `List.tail` or `List.take 1`, or that test the encoded value for emptiness, are computable
  in linear time and space.
-/

namespace Turing.MultiTapeTM

open Encodings Internal.FrameMachines

open Encodings Internal.FrameMachines

namespace ComputableTidilyInLinearTimeAndSpace

-- vendored: `of_cons_true`, `of_tail`, `of_take_one` and `of_isEmpty` below use the run equations
-- of `Internal/CodecWordMachines` instead of the inline case analysis of crei:crei/tidy-universal

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}

/-- Framing an encoded value. -/
public theorem of_frame (h : ∀ a, encOut (f a) = frame (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  frameT.computableTidilyInLinearTimeAndSpace fun a => by rw [h, frameT_run]

/-- Reading the word framed at the start of an encoded value. -/
public theorem of_unframe (h : ∀ a, encOut (f a) = unframe (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (readFrameT true).computableTidilyInLinearTimeAndSpace fun a =>
    (h a).trans (readFrameT_run_true _).symm

/-- Dropping the frame at the start of an encoded value. -/
public theorem of_dropFrame (h : ∀ a, encOut (f a) = dropFrame (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (readFrameT false).computableTidilyInLinearTimeAndSpace fun a =>
    (h a).trans (readFrameT_run_false _).symm

/-- Prepending `true` to an encoded value. -/
public theorem of_cons_true (h : ∀ a, encOut (f a) = true :: encIn a) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (headT none).computableTidilyInLinearTimeAndSpace fun a => by rw [h, headT_none_run]

/-- Dropping the first symbol of an encoded value. -/
public theorem of_tail (h : ∀ a, encOut (f a) = (encIn a).tail) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (headT (some false)).computableTidilyInLinearTimeAndSpace fun a => by
    rw [h, headT_some_false_run]

/-- Keeping just the first symbol of an encoded value. -/
public theorem of_take_one (h : ∀ a, encOut (f a) = (encIn a).take 1) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (headT (some true)).computableTidilyInLinearTimeAndSpace fun a => by
    rw [h, headT_some_true_run]

/-- Testing an encoded value for emptiness. -/
public theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableTidilyInLinearTimeAndSpace f encIn encBool :=
  isEmptyT.computableTidilyInLinearTimeAndSpace fun a => by rw [h, isEmptyT_run]; rfl

end ComputableTidilyInLinearTimeAndSpace

end Turing.MultiTapeTM


