-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:53:12.284014+00:00
-- url     : https://prove2.me/theorems/f4b9edb2-11b5-4ba3-8e3a-61185e8d5c2d
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option — Polynomial-time option operations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Option elimination reuses the degree-bounded encoding operations. Both the optional value and
--   its fallback may be computed from the input; no inhabitant of the value type is required.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.optionSome`: construct an optional value.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.optionGetD`: read an option with a fallback
--     supplied as part of the input.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.optionGetDWithInput`: the composition rule.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.optionIsSome`: test a computed optional value.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.optionElimWithInput`: branch on an optional
--     value while retaining the original input, including empty value types.
--
--   ### References
--
--   Uses Christian Reitwiessner's option encoding and degree-bounded machine calculus.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Option.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeOptionPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time option operations

Option elimination reuses the degree-bounded encoding operations. Both the optional value and
its fallback may be computed from the input; no inhabitant of the value type is required.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.optionSome`: construct an optional value.
* `Turing.MultiTapeTM.ComputableInPolyTime.optionGetD`: read an option with a fallback
  supplied as part of the input.
* `Turing.MultiTapeTM.ComputableInPolyTime.optionGetDWithInput`: the composition rule.
* `Turing.MultiTapeTM.ComputableInPolyTime.optionIsSome`: test a computed optional value.
* `Turing.MultiTapeTM.ComputableInPolyTime.optionElimWithInput`: branch on an optional
  value while retaining the original input, including empty value types.

## References

Uses Christian Reitwiessner's option encoding and degree-bounded machine calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Construct an optional value with the standard option encoding. -/
@[fun_prop]
theorem optionSome (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (some (α := α)) enc (encOption enc) :=
  of_linear (Internal.NormalForm.linear OptionEncoding.some)

/-- Test whether a computed option contains a value, without requiring a default value. -/
@[fun_prop]
theorem optionIsSome {value : α → Option β}
    (hvalue : ComputableTidilyInPolyTime value encA (encOption encB)) :
    ComputableTidilyInPolyTime (fun a => (value a).isSome) encA encBool :=
  (ComputableTidilyInDegree.isSome encB).computableTidilyInPolyTime.comp hvalue

/-- Read an option with a fallback supplied as part of the input. -/
@[fun_prop]
theorem optionGetD (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    have h := ((ComputableTidilyInDegree.isSome enc).computableTidilyInPolyTime.comp
      (fst (encOption enc) enc)).cond
        ((ComputableTidilyInDegree.getD fallback).computableTidilyInPolyTime.comp
          (fst (encOption enc) enc)) (snd (encOption enc) enc)
    convert h using 1
    funext ⟨value, d⟩
    cases value <;> rfl

/-- Read a computed option with a computed fallback, using their shared value encoding. -/
@[fun_prop]
theorem optionGetDWithInput {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableTidilyInPolyTime value encA (encOption encB))
    (hfallback : ComputableTidilyInPolyTime fallback encA encB) :
    ComputableTidilyInPolyTime (fun a => (value a).getD (fallback a)) encA encB :=
  (optionGetD encB).comp (hvalue.prod hfallback)

/-- Branch on a computed option, charging its full value and any captured original input. -/
@[fun_prop]
theorem optionElimWithInput {γ : Type} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hvalue : ComputableTidilyInPolyTime value encA (encOption encB))
    (hfallback : ComputableTidilyInPolyTime fallback encA encC)
    (hbody : ComputableTidilyInPolyTime (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC) :
    ComputableTidilyInPolyTime
      (fun a => (value a).elim (fallback a) (body a)) encA encC := by
  rcases isEmpty_or_nonempty β with h | h
  · convert hfallback using 1
    funext a
    cases value a with
    | none => rfl
    | some b => exact isEmptyElim b
  · obtain ⟨b⟩ := h
    have hget : ComputableTidilyInPolyTime (fun a => (value a).getD b) encA encB :=
      (ComputableTidilyInDegree.getD b).computableTidilyInPolyTime.comp hvalue
    convert hvalue.optionIsSome.cond (hbody.comp (id'.prod hget)) hfallback using 1
    funext a
    dsimp only [Function.comp_def]
    cases value a <;> rfl

end Turing.MultiTapeTM.ComputableTidilyInPolyTime


