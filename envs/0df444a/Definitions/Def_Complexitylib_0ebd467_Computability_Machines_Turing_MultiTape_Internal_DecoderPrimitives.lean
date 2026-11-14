-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:06.546643+00:00
-- url     : https://prove2.me/theorems/5c15d9cf-3661-4af8-97e8-c74625699995
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives — Direct certificates for total decoder leaves
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These witnesses apply to every input word, with the original independent degree-one cost and
--   output bounds. The type-indexed Decoder field can reuse them without a higher tidy calculus.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/DecoderPrimitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderWordMachines
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Primitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FrameMachines
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Direct certificates for total decoder leaves

These witnesses apply to every input word, with the original independent degree-one cost and
output bounds. The type-indexed Decoder field can reuse them without a higher tidy calculus.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.DecoderWords

/-- A runtime word decodes to itself. -/
theorem bits_degree : ComputableInDegree id encBits encBits 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- The unary decoder counts every symbol, including malformed false symbols. -/
theorem unary_degree : ComputableInDegree List.length encBits encUnary 1 1 := by
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, unaryLengthT.toTM, fun w => ?_⟩,
    ⟨1, fun w => by simp⟩⟩
  simpa only [show unaryLengthT.q₀ = () from rfl, unaryLengthT_run, encUnary_apply,
    encBits, Function.Embedding.refl_apply] using
    unaryLengthT.computesInTimeAndSpace_toTM w

/-- The Boolean decoder returns false on empty input and the first symbol otherwise. -/
theorem bool_degree : ComputableInDegree (fun w : List Bool => w.headD false)
    encBits encBool 1 1 := by
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, (headDefaultT false).toTM, fun w => ?_⟩,
    ⟨1, fun w => by simp⟩⟩
  simpa only [show (headDefaultT false).q₀ = false from rfl, headDefaultT_run,
    encBool_apply, encBits, Function.Embedding.refl_apply] using
    (headDefaultT false).computesInTimeAndSpace_toTM w

/-- The existing bit-list codec machine drops one symbol, including on empty input. -/
theorem tail_degree : ComputableInDegree List.tail encBits encBits 1 1 :=
  ListEncoding.tail (enc₁ := encBool) (enc := encBits)

/-- The existing bit-list codec machine tests whether the complete input is empty. -/
theorem empty_degree : ComputableInDegree List.isEmpty encBits encBool 1 1 :=
  ListEncoding.isEmpty (enc₁ := encBool) (enc := encBits)

/-- Read the initial frame on every word, including incomplete frames. -/
theorem unframe_degree : ComputableInDegree unframe encBits encBits 1 1 := by
  let τ := Internal.FrameMachines.readFrameT true
  have htm (w : List Bool) := τ.computesInTimeAndSpace_toTM w
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, τ.toTM, fun w => ?_⟩,
    ⟨3, fun w => ?_⟩⟩
  · simpa only [τ, show (Internal.FrameMachines.readFrameT true).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_true,
      encBits, Function.Embedding.refl_apply] using htm w
  · have hlen := (htm w).length_output_le
    simpa only [τ, show (Internal.FrameMachines.readFrameT true).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_true,
      encBits, Function.Embedding.refl_apply, pow_one] using hlen.trans
        (by omega : 2 * w.length + 3 ≤ 3 * (w.length + 1))

/-- Read what follows the initial frame on every word, including incomplete frames. -/
theorem dropFrame_degree : ComputableInDegree dropFrame encBits encBits 1 1 := by
  let τ := Internal.FrameMachines.readFrameT false
  have htm (w : List Bool) := τ.computesInTimeAndSpace_toTM w
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, τ.toTM, fun w => ?_⟩,
    ⟨3, fun w => ?_⟩⟩
  · simpa only [τ, show (Internal.FrameMachines.readFrameT false).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_false,
      encBits, Function.Embedding.refl_apply] using htm w
  · have hlen := (htm w).length_output_le
    simpa only [τ, show (Internal.FrameMachines.readFrameT false).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_false,
      encBits, Function.Embedding.refl_apply, pow_one] using hlen.trans
        (by omega : 2 * w.length + 3 ≤ 3 * (w.length + 1))

end Turing.MultiTapeTM.Internal.DecoderWords


