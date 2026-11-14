-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:05.00522+00:00
-- url     : https://prove2.me/theorems/4c2a91a9-741d-4ab7-aac6-87fb7839444d
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.PolyTime — Polynomial time on multi-tape machines
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.PolyTime` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut`: some machine with a binary alphabet and
--   finitely many states computes `f` in the sense of `Turing.MultiTapeTM.ComputableInTimeAndSpace`,
--   within time and space bounded by polynomially bounded functions of the length of the encoded input
--   [Arora and Barak, Chapter 1][AroraBarak09]. Time and space are independent bounds, as in
--   `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`; that a polynomial time bound already bounds
--   the space is a lemma about machines, not part of the definition.
--
--   The predicate is registered with `fun_prop`. This file proves the closure rules that need no
--   machine construction beyond upstream's: the identity, constants, functions on finite types and
--   changes of representation.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime`: computability in polynomial time.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.of_eq`, `Turing.MultiTapeTM.ComputableInPolyTime.id'`:
--     functions that do not change the encoded word.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.const`,
--     `Turing.MultiTapeTM.ComputableInPolyTime.of_finite`: constant functions and functions on finite
--     types.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/PolyTime.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
public import Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_PolynomialBound
public import Mathlib.Tactic.FunProp
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Combinators_AlmostConstant
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Combinators_Id

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.PolyTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time on multi-tape machines

`Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut`: some machine with a binary alphabet and
finitely many states computes `f` in the sense of `Turing.MultiTapeTM.ComputableInTimeAndSpace`,
within time and space bounded by polynomially bounded functions of the length of the encoded input
[Arora and Barak, Chapter 1][AroraBarak09]. Time and space are independent bounds, as in
`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`; that a polynomial time bound already bounds
the space is a lemma about machines, not part of the definition.

The predicate is registered with `fun_prop`. This file proves the closure rules that need no
machine construction beyond upstream's: the identity, constants, functions on finite types and
changes of representation.

## Main definitions

* `Turing.MultiTapeTM.ComputableInPolyTime`: computability in polynomial time.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.of_eq`, `Turing.MultiTapeTM.ComputableInPolyTime.id'`:
  functions that do not change the encoded word.
* `Turing.MultiTapeTM.ComputableInPolyTime.const`,
  `Turing.MultiTapeTM.ComputableInPolyTime.of_finite`: constant functions and functions on finite
  types.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

/-- `f` is computable in polynomial time: some machine with a binary alphabet and finitely many
states computes `f`, relative to the encodings `encIn` and `encOut`, within time and space
bounded by polynomially bounded functions of the length of the encoded input. -/
def ComputableInPolyTime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    ComputableInTimeAndSpaceOfLength f encIn encOut t s

namespace ComputableInPolyTime

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function whose encoded values are its encoded arguments is computable in polynomial time:
the machine copies its input. -/
theorem of_eq {f : α → β} (h : ∀ a, encOut (f a) = encIn a) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := computableInTimeAndSpace_id (enc := encIn)
  refine ⟨fun n => n + 1, fun _ => 0, polynomiallyBounded_iff_le.mpr ⟨1, 1, fun _ => by simp⟩,
    polynomiallyBounded_iff_le.mpr ⟨0, 0, fun _ => le_rfl⟩, k, State, hfinite, tm, fun a => ?_⟩
  rw [h a]
  exact htm a

/-- Every function on a finite type is computable in polynomial time, by a lookup machine. -/
theorem of_finite [Finite α] (f : α → β) : ComputableInPolyTime f encIn encOut :=
  let ⟨c, h⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encOut) f
  ⟨fun _ => c, fun _ => 0, polynomiallyBounded_iff_le.mpr ⟨c, 0, fun _ => by simp⟩,
    polynomiallyBounded_iff_le.mpr ⟨0, 0, fun _ => le_rfl⟩, h⟩

/-! ### Automation -/

attribute [fun_prop] ComputableInPolyTime

@[fun_prop]
theorem id' : ComputableInPolyTime (fun a : α => a) encIn encIn :=
  of_eq fun _ => rfl

@[fun_prop]
theorem const (b : β) : ComputableInPolyTime (fun _ : α => b) encIn encOut :=
  let ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encOut) b
  ⟨fun _ => c, fun _ => 0, polynomiallyBounded_iff_le.mpr ⟨c, 0, fun _ => by simp⟩,
    polynomiallyBounded_iff_le.mpr ⟨0, 0, fun _ => le_rfl⟩, h⟩

end ComputableInPolyTime

end Turing.MultiTapeTM


