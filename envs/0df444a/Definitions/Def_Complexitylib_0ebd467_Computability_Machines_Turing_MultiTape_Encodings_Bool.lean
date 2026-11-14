-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Bool
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Bool
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:36.294034+00:00
-- url     : https://prove2.me/theorems/a11ac1ca-0c96-45bf-8f75-915a761cb6ab
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool — Encodings of Booleans, signs and the unit type
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `Turing.MultiTapeTM.encBool` encodes a Boolean by one symbol, `Turing.MultiTapeTM.encSign` a sign,
--   such as a head move, by at most one symbol, and `Turing.MultiTapeTM.encUnit` the unit by the empty
--   word.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Bool`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Bool.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.Sign.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Embedding.Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Encodings of Booleans, signs and the unit type

`Turing.MultiTapeTM.encBool` encodes a Boolean by one symbol, `Turing.MultiTapeTM.encSign` a sign,
such as a head move, by at most one symbol, and `Turing.MultiTapeTM.encUnit` the unit by the empty
word.
-/

namespace Turing.MultiTapeTM

/-- The encoding `b ↦ [b]` of `Bool`. -/
@[expose] public def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => List.head_eq_of_cons_eq h⟩

@[simp]
public lemma encBool_apply (b : Bool) : encBool b = [b] := rfl

/-- Signs: `0 ↦ []`, `-1 ↦ [false]` and `1 ↦ [true]`. -/
@[expose] public def encSign : SignType ↪ List Bool :=
  ⟨fun m => match m with | .zero => [] | .neg => [false] | .pos => [true], by
    intro a b h
    cases a <;> cases b <;> simp_all⟩

/-- The unit type, encoded by the empty word. -/
@[expose] public def encUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

@[simp]
public lemma encUnit_apply (u : Unit) : encUnit u = [] := rfl

end Turing.MultiTapeTM


