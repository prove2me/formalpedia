-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearCodecPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearCodecPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:41:03.918951+00:00
-- url     : https://prove2.me/theorems/8f32ad3a-bdc7-4e03-b278-1f2024d4bb3f
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearCodecPrimitives — Direct linear capabilities used by codecs
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearCodecPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The witnesses normalize only realizing machines. No higher tidy computability rule is used.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearCodecPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/LinearCodecPrimitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate
-- vendored: codec machines retain crei/tidy-universal @7f7c0696 credit.
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_CodecWordMachines
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeClosure
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Capabilities

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearCodecPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Direct linear capabilities used by codecs

The witnesses normalize only realizing machines. No higher tidy computability rule is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Prepend the marker of the existing option encoding. -/
theorem of_cons_true {f : α → β} (h : ∀ a, encMid (f a) = true :: encIn a) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Encodings.headT none) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Drop the input word's first symbol using the existing head machine. -/
theorem of_tail {f : α → β} (h : ∀ a, encMid (f a) = (encIn a).tail) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Encodings.headT (some false)) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Keep the input word's first symbol using the existing head machine. -/
theorem of_take_one {f : α → β} (h : ∀ a, encMid (f a) = (encIn a).take 1) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Encodings.headT (some true)) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Test the encoded input for emptiness using the existing finite transducer. -/
theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableInDegree f encIn encBool 1 1 :=
  of_transducer Encodings.isEmptyT fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.isEmptyT_run_true, Encodings.isEmptyT_q₀,
      Encodings.isEmptyT_step, Encodings.isEmptyT_final]

/-- A fixed default on the empty word and a linear certificate on nonempty encoded inputs. -/
theorem of_isEmpty_ite {f : α → β} (d : β) (hd : ∀ a, encIn a = [] → f a = d)
    (h : ComputableInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype fun a => (encIn a).isEmpty = false).trans encIn) encMid 1 1) :
    ComputableInDegree f encIn encMid 1 1 := by
  convert ite (c := fun a => (encIn a).isEmpty) (of_isEmpty fun _ => rfl)
    ((const d).restrict _) h using 1
  · funext a
    split_ifs with ha <;> simp_all
  all_goals decide

end Turing.MultiTapeTM.ComputableInDegree


