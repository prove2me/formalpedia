-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:41:45.41349+00:00
-- url     : https://prove2.me/theorems/f5938f27-47cb-4b26-9ec9-7caff5fba187
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words — Word operations for encodings
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
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
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Words.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Capabilities
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearCodecPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FrameMachines

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words` — generated mechanically from
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

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `encOfEquiv` below, from that revision's `Encodings/Basic`
/-- The encoding of `α` through an equivalence with `β`, such as that of a structure with the
tuple of its fields. -/
@[expose] public def encOfEquiv {α β : Type*} (e : α ≃ β) (enc : β ↪ List Bool) :
    α ↪ List Bool :=
  e.toEmbedding.trans enc

@[simp] public lemma encOfEquiv_apply {α β : Type*} (e : α ≃ β) (enc : β ↪ List Bool) (a : α) :
    encOfEquiv e enc a = enc (e a) := rfl

end Turing.MultiTapeTM


