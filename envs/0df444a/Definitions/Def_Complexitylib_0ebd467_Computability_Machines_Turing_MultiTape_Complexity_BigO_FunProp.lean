-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunProp
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunProp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:37.443196+00:00
-- url     : https://prove2.me/theorems/f9b4775f-4030-4789-977f-7173af5caa2d
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp — `fun_prop` rules for bounds up to constants
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `fun_prop` proves `Turing.MultiTapeTM.ComputableInO f encIn encOut T S` from rules in
--   compositional form. The bounds of each rule's conclusion are a function of the bounds of its
--   premises, so in a goal whose bounds `T` and `S` are metavariables, `fun_prop` assembles them from
--   the parts of `f`. The usual pattern compares the assembled bounds with the intended ones in a
--   single step:
--
--   ```
--   refine .mono (by fun_prop) k (fun a => ?_) fun a => ?_
--   ```
--
--   The rules cover constants, the identity, composition, pairs and their projections, case
--   distinction on a computed Boolean, and `Option.isSome` and `Option.getD`. Other certificates
--   become rules in the same compositional form, for example `fun x => F (g x)` from
--   `Turing.MultiTapeTM.ComputableInO.comp'`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInO.id'`, `.comp'`: the identity and composition, in the form
--     required by `fun_prop`.
--   * `Turing.MultiTapeTM.ComputableInO.optionIsSome`, `.optionGetD`: option tests and defaults, with
--     the bounds of the option.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunProp`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/FunProp.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Quantitative
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCombinators

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# `fun_prop` rules for bounds up to constants

`fun_prop` proves `Turing.MultiTapeTM.ComputableInO f encIn encOut T S` from rules in
compositional form. The bounds of each rule's conclusion are a function of the bounds of its
premises, so in a goal whose bounds `T` and `S` are metavariables, `fun_prop` assembles them from
the parts of `f`. The usual pattern compares the assembled bounds with the intended ones in a
single step:

```
refine .mono (by fun_prop) k (fun a => ?_) fun a => ?_
```

The rules cover constants, the identity, composition, pairs and their projections, case
distinction on a computed Boolean, and `Option.isSome` and `Option.getD`. Other certificates
become rules in the same compositional form, for example `fun x => F (g x)` from
`Turing.MultiTapeTM.ComputableInO.comp'`.

## Main results

* `Turing.MultiTapeTM.ComputableInO.id'`, `.comp'`: the identity and composition, in the form
  required by `fun_prop`.
* `Turing.MultiTapeTM.ComputableInO.optionIsSome`, `.optionGetD`: option tests and defaults, with
  the bounds of the option.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {T S : α → ℕ}

attribute [fun_prop] ComputableInO
attribute [fun_prop] const prod fst' snd' ite

/-- Copy an encoded value, within linear time and space. -/
@[fun_prop]
theorem id' : ComputableInO (fun b : β => b) encMid encMid (fun b => (encMid b).length)
    fun b => (encMid b).length :=
  of_eq fun _ => rfl

/-- `Turing.MultiTapeTM.ComputableInO.comp` in the form required by `fun_prop`. -/
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encMid encOut T₂ S₂) (hg : ComputableInO g encIn encMid T₁ S₁) :
    ComputableInO (fun a => f (g a)) encIn encOut (fun a => T₁ a + T₂ (g a))
      fun a => S₁ a + S₂ (g a) :=
  hf.comp hg

/-- Whether a computed option holds a value, within the bounds of the option. -/
@[fun_prop]
theorem optionIsSome {enc : β ↪ List Bool} {o : α → Option β}
    (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun a => (o a).isSome) encIn encBool T S :=
  (ComputableInDegree.isSome enc).inO_one.comp_linear h

/-- The value of a computed option, or a fixed default, within the bounds of the option. -/
@[fun_prop]
theorem optionGetD {enc : β ↪ List Bool} {o : α → Option β} (d : β)
    (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun a => (o a).getD d) encIn enc T S :=
  (ComputableInDegree.optionGetD enc d).inO_one.comp_linear h

end Turing.MultiTapeTM.ComputableInO


