-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryNormalization
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryNormalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:59.268996+00:00
-- url     : https://prove2.me/theorems/7cb34284-141d-483d-a435-5b658366046b
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization — Direct charged bounds for binary-word normalization
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Reverse the raw little-endian word, drop its leading false symbols with the existing transducer,
--   and reverse back. Both component machines have linear clocks and zero work tapes; composition
--   retains linear time and linear workspace, including the encoded output charge. No qualitative
--   polynomial-time certificate supplies the quantitative bound.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInO.bitsToNat`: linear-time, charged linear-space binary decoding.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryNormalization`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/BinaryNormalization.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCombinators
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderWordMachines
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Reverse

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct charged bounds for binary-word normalization

Reverse the raw little-endian word, drop its leading false symbols with the existing transducer,
and reverse back. Both component machines have linear clocks and zero work tapes; composition
retains linear time and linear workspace, including the encoded output charge. No qualitative
polynomial-time certificate supplies the quantitative bound.

## Main results

* `Turing.MultiTapeTM.ComputableInO.bitsToNat`: linear-time, charged linear-space binary decoding.
-/

public section
namespace Turing.MultiTapeTM.ComputableInO

private theorem reverse_linear :
    ComputableInO List.reverse encBits encBits List.length List.length := by
  have h : ComputableInTimeAndSpace List.reverse encBits encBits
      (fun w => 2 * w.length + 2) (fun _ => 0) :=
    ⟨0, Bool, inferInstance, reverseInput Bool, fun w => ReverseInput.computesInTimeAndSpace w⟩
  exact ComputableInO.of_bounds h 2 (fun _ => by omega) (fun _ => by omega)
    (fun w => by simp only [encBits_apply, List.length_reverse]; omega)
private theorem drop_linear :
    ComputableInO (fun w : List Bool => w.dropWhile (!·)) encBits encBits
      List.length List.length := by
  have h : ComputableInTimeAndSpace (fun w : List Bool => w.dropWhile (!·)) encBits encBits
      (fun w => 2 * w.length + 3) (fun _ => 0) := by
    refine ⟨0, _, inferInstance, dropFalsesT.toTM, fun w => ?_⟩
    simpa only [show dropFalsesT.q₀ = false from rfl, dropFalsesT_run,
      encBits, Function.Embedding.refl_apply] using dropFalsesT.computesInTimeAndSpace_toTM w
  exact ComputableInO.of_bounds h 3 (fun _ => by omega) (fun _ => by omega)
    (fun w => by simpa only [encBits_apply] using
      (List.length_dropWhile_le (!·) w).trans (by omega))
/-- Read arbitrary little-endian words in linear time and charged linear workspace,
including empty words and noncanonical trailing false symbols. -/
theorem bitsToNat :
    ComputableInO ofBits encBits encNat List.length List.length := by
  have h := reverse_linear.comp_linear (drop_linear.comp_linear reverse_linear)
  exact h.of_enc_eq fun w => by rw [encNat_apply, bits_ofBits]; rfl

end Turing.MultiTapeTM.ComputableInO


