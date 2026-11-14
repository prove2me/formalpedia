-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Decode
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Decode
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:01:12.987458+00:00
-- url     : https://prove2.me/theorems/8d17f09e-2124-4c1a-b975-06268f1720aa
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode — Decoding descriptions of machines
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Every word decodes to a description of a machine (`Turing.MultiTapeTM.Universal.descDecoder`):
--   the decoder inverts the encoding `Turing.MultiTapeTM.Universal.eDesc` of descriptions, returns a
--   description of polynomial encoded length on every other word, and is computable within
--   bounds of fixed degrees. It is assembled from the generic decoders of
--   `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder` along the fields of a
--   description, its transitions, their keys and their actions.
--
--   A description framed at the start of a word is recovered whatever follows it
--   (`Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append`), so a description can be padded
--   to any length.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.decodeDesc`: the description decoded from a word.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Universal.decodeDesc_eDesc`: decoding inverts the encoding.
--   * `Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append`: padded descriptions.
--   * `Turing.MultiTapeTM.Universal.exists_computableInDegree_decodeDesc`: decoding is
--     computable within bounds of fixed degrees.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Decode`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Decode.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Complexity
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Decoding descriptions of machines

Every word decodes to a description of a machine (`Turing.MultiTapeTM.Universal.descDecoder`):
the decoder inverts the encoding `Turing.MultiTapeTM.Universal.eDesc` of descriptions, returns a
description of polynomial encoded length on every other word, and is computable within
bounds of fixed degrees. It is assembled from the generic decoders of
`Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder` along the fields of a
description, its transitions, their keys and their actions.

A description framed at the start of a word is recovered whatever follows it
(`Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append`), so a description can be padded
to any length.

## Main definitions

* `Turing.MultiTapeTM.Universal.decodeDesc`: the description decoded from a word.

## Main results

* `Turing.MultiTapeTM.Universal.decodeDesc_eDesc`: decoding inverts the encoding.
* `Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append`: padded descriptions.
* `Turing.MultiTapeTM.Universal.exists_computableInDegree_decodeDesc`: decoding is
  computable within bounds of fixed degrees.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace Universal

/-- The sign read from a word: zero if it is empty (`q.1`), and otherwise positive or negative as
its head (`q.2`) is `true` or `false`. -/
def signOf (q : Bool × Bool) : SignType := if q.1 then 0 else if q.2 then 1 else -1

/-- Moves are decoded from the head of the word. -/
def signDecoder : Decoder encSign where
  decode w := signOf (w.isEmpty, w.headD false)
  decode_enc m := by cases m <;> rfl
  computable := ⟨_, _, (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encSign) signOf).comp
      (Internal.DecoderWords.empty_degree.prod Internal.DecoderWords.bool_degree)⟩

/-- Symbols and blanks. -/
def symDecoder : Decoder eSym := .option .unary

/-- Keys of transitions, from their fields. -/
def keyDecoder : Decoder eKey :=
  (Decoder.pair .unary (.pair symDecoder (.list symDecoder))).map
    (fun t => ⟨t.1, t.2.1, t.2.2⟩) (fun k => (k.state, k.input, k.work)) (fun _ => rfl)
    fun _ => rfl

/-- Actions on a work tape. -/
def tapeActDecoder : Decoder eTA := .pair (.option symDecoder) signDecoder

/-- Actions, from their fields. -/
def actDecoder : Decoder eAct :=
  (Decoder.pair signDecoder (.pair (.list tapeActDecoder) (.pair symDecoder symDecoder))).map
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun a => (a.inputTape, a.workTapes, a.output, a.state)) (fun _ => rfl) fun _ => rfl

/-- **The decoder of descriptions.** -/
def descDecoder : Decoder eDesc :=
  (Decoder.pair .unary (.pair .unary (.list (.pair keyDecoder actDecoder)))).map
    (fun t => ⟨t.1, t.2.1, t.2.2⟩) (fun d => (d.tapes, d.q₀, d.table)) (fun _ => rfl)
    fun _ => rfl

/-- The description decoded from a word. -/
def decodeDesc (w : List Bool) : Desc := descDecoder.decode w

/-- Decoding inverts the encoding of descriptions. -/
theorem decodeDesc_eDesc (d : Desc) : decodeDesc (eDesc d) = d :=
  descDecoder.decode_enc d

/-- **Padded descriptions.** A description framed at the start of a word is decoded from the
framed word, whatever follows it. -/
theorem decodeDesc_unframe_frame_append (d : Desc) (pad : List Bool) :
    decodeDesc (unframe (frame (eDesc d) ++ pad)) = d := by
  rw [unframe_frame_append, decodeDesc_eDesc]

/-- **Decoding is efficient.** It is computable, and the decoded descriptions have
encoded length polynomial in the length of the word, within bounds of fixed degrees. -/
theorem exists_computableInDegree_decodeDesc :
    ∃ d e, ComputableInDegree decodeDesc encBits eDesc d e :=
  descDecoder.computable

end Universal

end Turing.MultiTapeTM


