-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Pi
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Pi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:55:42.567195+00:00
-- url     : https://prove2.me/theorems/4c56aeb3-cd74-45a0-8e9c-1081b4a4578b
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi — Polynomial-time finite table operations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Programs construct finite tables as ordinary functions and use ordinary application and update.
--   The certificates store the complete table using `encPi` and the existing list machinery.
--   The index type is fixed independently of the input; values need not be finite or inhabited.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.ofFn`, `.pi`: construct fixed finite families.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply`, `.pi_update`: fixed-index access.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply'`: computed-index access.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_eval`: lookup from an encoded table/index pair.
--
--   ### References
--
--   Adapts Computability/Probabilistic/Pi.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy deterministic calculus.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Pi`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Pi.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePiPrimitives

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pi
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Finite

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time finite table operations

Programs construct finite tables as ordinary functions and use ordinary application and update.
The certificates store the complete table using `encPi` and the existing list machinery.
The index type is fixed independently of the input; values need not be finite or inhabited.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.ofFn`, `.pi`: construct fixed finite families.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply`, `.pi_update`: fixed-index access.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply'`: computed-index access.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_eval`: lookup from an encoded table/index pair.

## References

Adapts Computability/Probabilistic/Pi.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy deterministic calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α Index Value : Type} {input : α ↪ List Bool} {enc : Value ↪ List Bool}

/-- Construct a list of a fixed number of efficiently computed entries. -/
@[fun_prop]
theorem ofFn {count : ℕ} {values : α → Fin count → Value}
    (hvalues : ∀ i, ComputableTidilyInPolyTime (fun a => values a i) input enc) :
    ComputableTidilyInPolyTime (fun a => List.ofFn (values a)) input (encList enc) := by
  induction count with
  | zero => simpa using (const (encIn := input) (encMid := encList enc) [])
  | succ count ih =>
    simpa only [List.ofFn_succ] using (hvalues 0).cons'
      (ih (values := fun a i => values a i.succ) (fun i => hvalues i.succ))

/-- Construct a table by computing each entry, retaining the original input in each computation. -/
@[fun_prop]
theorem pi [Fintype Index] {values : α → Index → Value}
    (hvalues : ∀ i, ComputableTidilyInPolyTime (fun a => values a i) input enc) :
    ComputableTidilyInPolyTime values input (encPi enc) :=
  (ofFn (fun i => hvalues ((Fintype.equivFin Index).symm i))).of_enc_eq (fun _ => rfl)

/-- Read a fixed entry, charging for the stored prefix without requiring a default value. -/
@[fun_prop]
theorem pi_apply [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableTidilyInPolyTime (fun values : Index → Value => values i) (encPi enc) enc := by
  classical
  cases isEmpty_or_nonempty Value with
  | inl hempty =>
    let : IsEmpty (Index → Value) := ⟨fun values => isEmptyElim (values i)⟩
    exact of_finite _
  | inr hnonempty =>
    have hlist : ComputableTidilyInPolyTime (fun values : Index → Value =>
        List.ofFn (fun j => values ((Fintype.equivFin Index).symm j)))
        (encPi enc) (encList enc) := of_eq (fun _ => rfl)
    have hlookup := (listGetD (encA := enc) (Classical.choice hnonempty)).comp
      (hlist.prod (const (encMid := encUnary) (Fintype.equivFin Index i).val))
    simpa [Function.comp_def] using hlookup

/-- Update a fixed table entry while charging for all preserved entries. -/
@[fun_prop]
theorem pi_update [Fintype Index] [DecidableEq Index]
    {values : α → Index → Value} {value : α → Value}
    (hvalues : ComputableTidilyInPolyTime values input (encPi enc))
    (hvalue : ComputableTidilyInPolyTime value input enc) (i : Index) :
    ComputableTidilyInPolyTime (fun a => Function.update (values a) i (value a))
      input (encPi enc) := by
  apply pi
  intro j
  by_cases h : j = i
  · subst j
    simpa using hvalue
  · simpa [Function.update_of_ne h, Function.comp_def] using (pi_apply enc j).comp hvalues

/-- Read a computed index of a fixed finite table, charging the index and all stored entries. -/
theorem pi_apply' [Fintype Index] {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index}
    (hvalues : ComputableTidilyInPolyTime values input (encPi enc))
    (hindex : ComputableTidilyInPolyTime index input indexEncoding) :
    ComputableTidilyInPolyTime (fun a => values a (index a)) input enc :=
  hindex.finite_cases (fun i => (pi_apply enc i).comp hvalues)

/-- Evaluate a stored table at a stored index. The product view is registered with `fun_prop`;
for separately computed tables and indices, apply `pi_apply'` to their certificates. -/
@[fun_prop]
theorem pi_eval [Fintype Index] (indexEncoding : Index ↪ List Bool) (enc : Value ↪ List Bool) :
    ComputableTidilyInPolyTime (fun pair : (Index → Value) × Index => pair.1 pair.2)
      (encPair (encPi enc) indexEncoding) enc := pi_apply' (fst _ _) (snd _ _)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime


