-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePiPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePiPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:53:26.051969+00:00
-- url     : https://prove2.me/theorems/b8987e21-a582-44b7-9513-cf69a8b1750d
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives — Direct finite-table construction, lookup and update
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The fixed index order and framed-list representation are unchanged. Lookup composes the existing
--   head and tail codec machines; finite runtime dispatch retains the full captured input in each
--   branch. The direct proofs introduce no default inhabitant requirement on the value or index type.
--
--   **Contents.** The module is published as a whole: 9 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePiPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimePiPrimitives.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pi
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Finite
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Fold
import Mathlib.Data.List.GetD

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct finite-table construction, lookup and update

The fixed index order and framed-list representation are unchanged. Lookup composes the existing
head and tail codec machines; finite runtime dispatch retains the full captured input in each
branch. The direct proofs introduce no default inhabitant requirement on the value or index type.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α Index Value : Type} {input : α ↪ List Bool} {enc : Value ↪ List Bool}

/-- Construct a list of a fixed number of efficiently computed entries. -/
@[fun_prop]
theorem ofFn {count : ℕ} {values : α → Fin count → Value}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input enc) :
    ComputableInPolyTime (fun a => List.ofFn (values a)) input (encList enc) := by
  induction count with
  | zero => simpa using (const (encIn := input) (encOut := encList enc) [])
  | succ count ih =>
    simpa only [List.ofFn_succ] using (hvalues 0).cons'
      (ih (values := fun a i => values a i.succ) (fun i => hvalues i.succ))

/-- Construct a table by computing each entry, retaining the original input in each computation. -/
@[fun_prop]
theorem pi [Fintype Index] {values : α → Index → Value}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input enc) :
    ComputableInPolyTime values input (encPi enc) :=
  (ofFn (fun i => hvalues ((Fintype.equivFin Index).symm i))).of_enc_eq (fun _ => rfl)

private theorem listTail :
    ComputableInPolyTime (List.tail : List Value → List Value) (encList enc) (encList enc) := by
  exact (ListEncoding.tail (enc₁ := enc) (enc := encList enc)).computableInPolyTime

private theorem listHeadD (fallback : Value) :
    ComputableInPolyTime (fun l : List Value => l.headD fallback) (encList enc) enc := by
  exact (ListEncoding.headD
    (enc₁ := enc) (enc := encList enc) fallback).computableInPolyTime

private theorem fixedDrop (count : ℕ) :
    ComputableInPolyTime (fun l : List Value => l.drop count) (encList enc) (encList enc) := by
  induction count with
  | zero => simpa only [List.drop_zero] using (id' (encIn := encList enc))
  | succ count ih =>
    simpa only [Function.comp_def, List.tail_drop] using listTail.comp ih

/-- Read a fixed entry, charging for the stored prefix without requiring a default value. -/
@[fun_prop]
theorem pi_apply [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableInPolyTime (fun values : Index → Value => values i) (encPi enc) enc := by
  classical
  cases isEmpty_or_nonempty Value with
  | inl hempty =>
    let : IsEmpty (Index → Value) := ⟨fun values => isEmptyElim (values i)⟩
    exact of_finite _
  | inr hnonempty =>
    have hlist : ComputableInPolyTime (fun values : Index → Value =>
        List.ofFn (fun j => values ((Fintype.equivFin Index).symm j)))
        (encPi enc) (encList enc) := of_eq (fun _ => rfl)
    have hlookup := (listHeadD (enc := enc) (Classical.choice hnonempty)).comp
      ((fixedDrop (enc := enc) (Fintype.equivFin Index i).val).comp hlist)
    simpa [Function.comp_def, List.headD_eq_getD, List.getD_eq_getElem?_getD] using hlookup

/-- Update a fixed table entry while charging for all preserved entries. -/
@[fun_prop]
theorem pi_update [Fintype Index] [DecidableEq Index]
    {values : α → Index → Value} {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hvalue : ComputableInPolyTime value input enc) (i : Index) :
    ComputableInPolyTime (fun a => Function.update (values a) i (value a))
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
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding) :
    ComputableInPolyTime (fun a => values a (index a)) input enc :=
  hindex.finite_cases (fun i => (pi_apply enc i).comp hvalues)

/-- Update a computed index while retaining and charging every other entry. -/
@[fun_prop]
theorem pi_update' [Fintype Index] [DecidableEq Index] {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index} {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding)
    (hvalue : ComputableInPolyTime value input enc) :
    ComputableInPolyTime (fun a => Function.update (values a) (index a) (value a))
      input (encPi enc) := hindex.finite_cases (fun i => pi_update hvalues hvalue i)

end Turing.MultiTapeTM.ComputableInPolyTime


