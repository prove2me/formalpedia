-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:38.063043+00:00
-- url     : https://prove2.me/theorems/b28614a9-1e30-4a2a-a037-f5abbb507b69
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option — The encoding of options
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `encOption enc` encodes `none` as the empty word and `some a` as `true` followed by `enc a`. It has
--   the capabilities of `Turing.MultiTapeTM.OptionEncoding`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.encOption`: the encoding of options.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Option.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The encoding of options

`encOption enc` encodes `none` as the empty word and `some a` as `true` followed by `enc a`. It has
the capabilities of `Turing.MultiTapeTM.OptionEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encOption`: the encoding of options.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Options encoded with `none` as the empty word and `some a` as `true` followed by `enc a`. -/
@[expose] public def encOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  ⟨fun o => o.elim [] (true :: enc ·), by rintro (_ | a) (_ | b) h <;> simp_all⟩

variable {enc : α ↪ List Bool}

@[simp]
public lemma encOption_none : encOption enc none = [] := rfl

@[simp]
public lemma encOption_some (a : α) : encOption enc (some a) = true :: enc a := rfl

public instance : OptionEncoding enc (encOption enc) where
  none_eq := rfl
  some := .of_cons_true fun _ => rfl
  getD d := .of_isEmpty_ite d (fun o ho => by cases o <;> simp_all)
    (.of_tail fun ⟨o, ho⟩ => by cases o <;> simp at ho ⊢)

end Turing.MultiTapeTM


