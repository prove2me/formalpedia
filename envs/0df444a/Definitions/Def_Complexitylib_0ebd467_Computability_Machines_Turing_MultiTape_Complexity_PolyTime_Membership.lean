-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Membership
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Membership
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:55:37.079401+00:00
-- url     : https://prove2.me/theorems/261c91ee-fcee-447c-95d2-603c3e63bfa1
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership — Polynomial-time membership tests
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Reduction maps and verifiers test membership as they are written on paper, for example keeping
--   the pairs `(u, v)` with `(u, v) ∉ G.2`. `fun_prop` already certifies `decide` of conjunctions,
--   disjunctions, equalities and disequalities
--   (`Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_and` and its neighbours). This file adds
--   negation and membership of a computed value in a computed list, so such tests need no rewriting
--   into Boolean operations before `fun_prop` or `polytime` runs. Membership is decided by scanning
--   the list for an equal element (`Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWithInput`).
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_not`: negating a decided proposition.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_mem`: membership in a computed list.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Membership`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Membership.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time membership tests

Reduction maps and verifiers test membership as they are written on paper, for example keeping
the pairs `(u, v)` with `(u, v) ∉ G.2`. `fun_prop` already certifies `decide` of conjunctions,
disjunctions, equalities and disequalities
(`Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_and` and its neighbours). This file adds
negation and membership of a computed value in a computed list, so such tests need no rewriting
into Boolean operations before `fun_prop` or `polytime` runs. Membership is decided by scanning
the list for an equal element (`Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWithInput`).

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_not`: negating a decided proposition.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_mem`: membership in a computed list.
-/

public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}

/-- Negation of an efficiently decidable proposition uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_not {p : γ → Prop} [∀ x, Decidable (p x)]
    (h : ComputableTidilyInPolyTime (fun x => decide (p x)) encIn encBool) :
    ComputableTidilyInPolyTime (fun x => decide ¬p x) encIn encBool := by
  simpa only [Function.comp_def, _root_.decide_not] using bool_not.comp h

/-- Membership of a computed value in a computed list is decided by scanning the list for an equal
element. -/
@[fun_prop]
theorem decide_mem {list : γ → List α} {value : γ → α} [∀ x, Decidable (value x ∈ list x)]
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hvalue : ComputableTidilyInPolyTime value encIn encA) :
    ComputableTidilyInPolyTime (fun x => decide (value x ∈ list x)) encIn encBool := by
  classical
  have hscan (x : γ) : decide (value x ∈ list x) = (list x).any fun b => decide (b = value x) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
    exact ⟨fun h => ⟨_, h, decide_eq_true rfl⟩, fun ⟨b, hb, e⟩ => of_decide_eq_true e ▸ hb⟩
  simp only [hscan]
  exact anyWithInput (test := fun x b => decide (b = value x)) hlist
    (decide_eq' (snd _ _) (hvalue.comp (fst _ _)))

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Membership of a computed value in a computed list is decided by scanning the list for an equal
element. -/
@[fun_prop]
theorem decide_mem {γ : Type}
    {α : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {list : γ → List α}
    {value : γ → α}
    [_inst6 : (x : γ) → Decidable (value x ∈ list x)]
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime
  (fun (x : γ) => Decidable.decide (value x ∈ list x)) encIn encBool :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_mem γ α encIn encA list value
      _inst6 hlist.tidy hvalue.tidy)

/-- Negation of an efficiently decidable proposition uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_not {γ : Type}
    {encIn : γ ↪ List Bool}
    {p : γ → Prop}
    [_inst3 : (x : γ) → Decidable (p x)]
    (h : ComputableInPolyTime (fun (x : γ) => Decidable.decide (p x)) encIn
  encBool) :
    ComputableInPolyTime (fun (x : γ) => Decidable.decide ¬p x) encIn
  encBool :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_not γ encIn p _inst3 h.tidy)

end Turing.MultiTapeTM.ComputableInPolyTime


