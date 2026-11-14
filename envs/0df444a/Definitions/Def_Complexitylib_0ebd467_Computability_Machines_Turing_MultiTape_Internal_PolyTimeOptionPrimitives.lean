-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeOptionPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeOptionPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:57.955032+00:00
-- url     : https://prove2.me/theorems/2b506802-7811-437e-a178-9b52a4cbe3a3
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives — Direct plain polynomial-time option operations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The option encoding machines supply construction and fixed-default elimination. Composition
--   retains every encoded input, including captured arguments and a runtime fallback. Empty value
--   types need no inhabitant assumption.
--
--   ### Main results
--
--   * `ComputableInPolyTime.optionSome`: construct an optional value.
--   * `ComputableInPolyTime.optionIsSome`: test a computed optional value.
--   * `ComputableInPolyTime.optionGetD`: read an option with a runtime fallback.
--   * `ComputableInPolyTime.optionGetDWithInput`, `.optionElimWithInput`: retain captured inputs.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeOptionPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeOptionPrimitives.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeOptionPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct plain polynomial-time option operations

The option encoding machines supply construction and fixed-default elimination. Composition
retains every encoded input, including captured arguments and a runtime fallback. Empty value
types need no inhabitant assumption.

## Main results

* `ComputableInPolyTime.optionSome`: construct an optional value.
* `ComputableInPolyTime.optionIsSome`: test a computed optional value.
* `ComputableInPolyTime.optionGetD`: read an option with a runtime fallback.
* `ComputableInPolyTime.optionGetDWithInput`, `.optionElimWithInput`: retain captured inputs.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Construct an optional value with the standard option encoding. -/
@[fun_prop]
theorem optionSome (enc : α ↪ List Bool) :
    ComputableInPolyTime (some (α := α)) enc (encOption enc) :=
  ComputableInDegree.optionSome.computableInPolyTime

/-- Test whether a computed option contains a value, without requiring a default value. -/
@[fun_prop]
theorem optionIsSome {value : α → Option β}
    (hvalue : ComputableInPolyTime value encA (encOption encB)) :
    ComputableInPolyTime (fun a => (value a).isSome) encA encBool :=
  (ComputableInDegree.isSome encB).computableInPolyTime.comp hvalue

/-- Read an option with a fallback supplied as part of the input. -/
@[fun_prop]
theorem optionGetD (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    have hread := ComputableInPolyTime.ite (encC := encBool)
      ((ComputableInDegree.isSome enc).computableInPolyTime.comp (fst (encOption enc) enc))
      ((ComputableInDegree.getD fallback).computableInPolyTime.comp (fst (encOption enc) enc))
      (snd (encOption enc) enc)
    convert hread using 1
    funext ⟨value, d⟩
    cases value <;> rfl

/-- Read a computed option with a computed fallback, using their shared value encoding. -/
@[fun_prop]
theorem optionGetDWithInput {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encB) :
    ComputableInPolyTime (fun a => (value a).getD (fallback a)) encA encB :=
  (optionGetD encB).comp (hvalue.prod hfallback)

/-- Branch on a computed option, charging its full value and any captured original input. -/
@[fun_prop]
theorem optionElimWithInput {γ : Type} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encC)
    (hbody : ComputableInPolyTime (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC) :
    ComputableInPolyTime
      (fun a => (value a).elim (fallback a) (body a)) encA encC := by
  rcases isEmpty_or_nonempty β with h | h
  · convert hfallback using 1
    funext a
    cases value a with
    | none => rfl
    | some b => exact isEmptyElim b
  · obtain ⟨b⟩ := h
    have hget : ComputableInPolyTime (fun a => (value a).getD b) encA encB :=
      (ComputableInDegree.getD b).computableInPolyTime.comp hvalue
    have hbranch := ComputableInPolyTime.ite (encC := encBool) hvalue.optionIsSome
      (hbody.comp (id'.prod hget)) hfallback
    convert hbranch using 1
    funext a
    dsimp only [Function.comp_def]
    cases value a <;> rfl

end Turing.MultiTapeTM.ComputableInPolyTime


