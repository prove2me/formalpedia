-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Basic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:17.210525+00:00
-- url     : https://prove2.me/theorems/a1d37f93-00af-479e-b733-300d52d90189
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic — Total decoders with plain degree certificates
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A decoder is total on every word, inverts its encoding, and carries independent cost and encoded
--   output degrees. The basic constructors preserve totality and the round-trip law.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Decoder`: total decoding with independent cost and output degrees.
--   * `Turing.MultiTapeTM.Decoder.computableInPolyTime`: the ordinary polynomial-time certificate.
--   * `Turing.MultiTapeTM.Decoder.bits`, `.unary`, `.bool`, `.option`, `.pair`, `.map`: basic decoders.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Decoder.option_computableInDegree`: option decoding preserves the
--     supplied output degree, including zero, with cost degree `max 1 (max d e)`.
--
--   **Contents.** The module is published as a whole: 10 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Basic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Decoder/Basic.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeOptionPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Total decoders with plain degree certificates

A decoder is total on every word, inverts its encoding, and carries independent cost and encoded
output degrees. The basic constructors preserve totality and the round-trip law.

## Main definitions

* `Turing.MultiTapeTM.Decoder`: total decoding with independent cost and output degrees.
* `Turing.MultiTapeTM.Decoder.computableInPolyTime`: the ordinary polynomial-time certificate.
* `Turing.MultiTapeTM.Decoder.bits`, `.unary`, `.bool`, `.option`, `.pair`, `.map`: basic decoders.

## Main results

* `Turing.MultiTapeTM.Decoder.option_computableInDegree`: option decoding preserves the
  supplied output degree, including zero, with cost degree `max 1 (max d e)`.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-- A total decoder with polynomial cost and encoded-output growth on every input word. -/
structure Decoder {α : Type} (enc : α ↪ List Bool) where
  /-- The decoded value of any word. -/
  decode : List Bool → α
  /-- Decoding inverts the encoding. -/
  decode_enc (a : α) : decode (enc a) = a
  /-- Decoding has independent cost and encoded-output degrees, including zero. -/
  computable : ∃ d e, ComputableInDegree decode encBits enc d e

namespace Decoder
variable {α β : Type} {enc : α ↪ List Bool} {enc' : β ↪ List Bool}

/-- Every total decoder has a plain polynomial-time certificate. -/
@[fun_prop]
theorem computableInPolyTime (D : Decoder enc) : ComputableInPolyTime D.decode encBits enc := by
  obtain ⟨_, _, h⟩ := D.computable
  exact h.computableInPolyTime

/-- Bit strings are their own encoding. -/
def bits : Decoder encBits where
  decode := id
  decode_enc _ := rfl
  computable := ⟨1, 1, Internal.DecoderWords.bits_degree⟩

/-- Unary numbers are decoded by the length of the word. -/
def unary : Decoder encUnary where
  decode w := w.length
  decode_enc n := by simp
  computable := ⟨1, 1, Internal.DecoderWords.unary_degree⟩

/-- Booleans are decoded from the first symbol. -/
def bool : Decoder encBool where
  decode w := w.headD false
  decode_enc _ := rfl
  computable := ⟨1, 1, Internal.DecoderWords.bool_degree⟩

private theorem option_decode_degree {decode : List Bool → α} {d e : ℕ}
    (h : ComputableInDegree decode encBits enc d e) :
    ComputableInDegree (fun w => if w.isEmpty then none else some (decode w.tail))
      encBits (encOption enc) (max 1 (max d e)) e := by
  have hsome : ComputableInDegree (fun w => some (decode w.tail))
      encBits (encOption enc) (max 1 (max d e)) e :=
    ((ComputableInDegree.optionSome (enc₁ := enc) (enc := encOption enc)).comp
      (h.comp Internal.DecoderWords.tail_degree)).mono (by omega) (by omega)
  exact (ComputableInDegree.ite (f := fun _ => none)
    (g := fun w => some (decode w.tail)) Internal.DecoderWords.empty_degree
    (ComputableInDegree.const none)
    (ComputableInDegree.of_encIn_eq Subtype.val (fun _ => rfl) hsome)).mono
      (d' := max 1 (max d e)) (e' := e) (by omega) (by omega)

/-- Options are decoded as `none` from the empty word, and otherwise from the tail. -/
def option (D : Decoder enc) : Decoder (encOption enc) where
  decode w := if w.isEmpty then none else some (D.decode w.tail)
  decode_enc o := by cases o <;> simp [encOption, D.decode_enc]
  computable := by
    obtain ⟨d, e, hD⟩ := D.computable
    exact ⟨max 1 (max d e), e, option_decode_degree hD⟩

/-- Option decoding preserves any supplied encoded-output degree, including zero. Its cost
accounts for reading the input, running the decoder, and emitting the tagged decoded output. -/
theorem option_computableInDegree (D : Decoder enc) {d e : ℕ}
    (hD : ComputableInDegree D.decode encBits enc d e) :
    ComputableInDegree (option D).decode encBits (encOption enc) (max 1 (max d e)) e :=
  option_decode_degree hD

/-- Pairs are decoded from the framed first component and what follows it. -/
def pair {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} (D₁ : Decoder enc₁)
    (D₂ : Decoder enc₂) : Decoder (encPair enc₁ enc₂) where
  decode w := (D₁.decode (unframe w), D₂.decode (dropFrame w))
  decode_enc p := by
    simp [unframe_frame_append, dropFrame_frame_append, D₁.decode_enc, D₂.decode_enc]
  computable := by
    obtain ⟨d₁, e₁, h₁⟩ := D₁.computable
    obtain ⟨d₂, e₂, h₂⟩ := D₂.computable
    exact ⟨_, _, (h₁.comp Internal.DecoderWords.unframe_degree).prod
      (h₂.comp Internal.DecoderWords.dropFrame_degree)⟩

/-- Transport a decoder along an encoding equality and a right inverse. -/
def map (D : Decoder enc) (f : α → β) (g : β → α) (hfg : ∀ b, f (g b) = b)
    (henc : ∀ a, enc' (f a) = enc a) : Decoder enc' where
  decode w := f (D.decode w)
  decode_enc b := by
    conv_lhs => rw [← hfg b, henc, D.decode_enc]
    exact hfg b
  computable :=
    let ⟨d, e, h⟩ := D.computable
    ⟨d, e, h.of_enc_eq fun w => henc _⟩

end Decoder
end Turing.MultiTapeTM


