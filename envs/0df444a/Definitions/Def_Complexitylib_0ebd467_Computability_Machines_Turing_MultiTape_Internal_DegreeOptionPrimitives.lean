-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeOptionPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeOptionPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:59.689268+00:00
-- url     : https://prove2.me/theorems/6e965b98-4132-47c2-ab12-92d86a5c333f
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives — Direct degree certificates for option encoding machines
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Construction and fixed-default elimination reuse the encoding capability's degree certificates.
--   The Boolean test retains its constant output degree. No higher tidy calculus is used.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeOptionPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/DegreeOptionPrimitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Primitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_WordPredicates

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct degree certificates for option encoding machines

Construction and fixed-default elimination reuse the encoding capability's degree certificates.
The Boolean test retains its constant output degree. No higher tidy calculus is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree
open Internal.WordPredicates

variable {β : Type*} {enc₁ : β ↪ List Bool}

/-- Construct an optional value in an encoding with the option capability. -/
theorem optionSome {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] :
    ComputableInDegree some enc₁ enc 1 1 := OptionEncoding.some

/-- Eliminate an optional value using a fixed default. -/
theorem getD {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] (d : β) :
    ComputableInDegree (fun o => o.getD d) enc enc₁ 1 1 := OptionEncoding.getD d

/-- Whether a standard encoded option holds a value; the Boolean output has degree zero. -/
theorem isSome (enc : β ↪ List Bool) :
    ComputableInDegree (fun o : Option β => o.isSome) (encOption enc) encBool 1 0 := by
  refine ⟨⟨fun o => 2 * (encOption enc o).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, nonemptyT.toTM, fun o => ?_⟩,
    ⟨1, fun o => by simp⟩⟩
  have heq : encBool o.isSome = nonemptyT.run nonemptyT.q₀ (encOption enc o) := by
    cases o with
    | none => rfl
    | some b =>
      change [true] = [true] ++ nonemptyT.run true (enc b)
      rw [nonemptyT_run_true, List.append_nil]
  simpa only [heq] using nonemptyT.computesInTimeAndSpace_toTM (encOption enc o)

end Turing.MultiTapeTM.ComputableInDegree


