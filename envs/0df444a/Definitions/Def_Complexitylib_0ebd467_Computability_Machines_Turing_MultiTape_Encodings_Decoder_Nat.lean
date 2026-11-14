-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Nat
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Nat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:47:43.828398+00:00
-- url     : https://prove2.me/theorems/3ba39b23-20bd-420b-aa6b-fe9274385e17
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat — Total binary-number decoding
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Binary digits are read least significant first. Trailing false symbols are ignored, including on
--   malformed words, and empty input returns zero. The decoder satisfies the encoding round-trip law
--   and has a certificate from direct plain machines.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Nat`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Decoder/Nat.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryNormalization
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Bits

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Total binary-number decoding

Binary digits are read least significant first. Trailing false symbols are ignored, including on
malformed words, and empty input returns zero. The decoder satisfies the encoding round-trip law
and has a certificate from direct plain machines.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace Decoder

/-- Binary numbers are decoded from their digits up to the last `true`. -/
def nat : Decoder encNat where
  decode := ofBits
  -- A tactic proof keeps the foundational binary-digit lemma a proof-only dependency.
  decode_enc n := by exact Nat.foldr_bit_bits n
  computable :=
    (ComputableInO.bitsToNat.computableInPolyTime
      (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
      (PolyBounded.of_forall_le 1 1 (fun _ => by simp))).exists_degree

end Decoder

/-- Decode every little-endian bit word, including noncanonical trailing false symbols. -/
@[fun_prop]
theorem ComputableInPolyTime.bitsToNat : ComputableInPolyTime ofBits encBits encNat :=
  Decoder.nat.computableInPolyTime

end Turing.MultiTapeTM


