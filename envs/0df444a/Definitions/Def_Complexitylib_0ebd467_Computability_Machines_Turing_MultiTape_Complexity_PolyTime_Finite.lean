-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Finite
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Finite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:52:42.794619+00:00
-- url     : https://prove2.me/theorems/a3d71e56-37aa-4379-b44b-80efd92de3d5
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite — Polynomial-time finite case analysis
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   An efficiently computed finite tag selects a branch retaining the original input. Both the tag
--   encoding and output encoding are arbitrary. The finite type and all branch machines are fixed
--   independently of runtime input; this does not enumerate a family whose size grows with the input.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.finite_cases`,
--     `Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases`: finite dispatch with captured input.
--
--   ### References
--
--   Adapts Computability/Probabilistic/Finite.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Finite`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Finite.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Fold
import Mathlib.Data.Fintype.Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time finite case analysis

An efficiently computed finite tag selects a branch retaining the original input. Both the tag
encoding and output encoding are arbitrary. The finite type and all branch machines are fixed
independently of runtime input; this does not enumerate a family whose size grows with the input.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.finite_cases`,
  `Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases`: finite dispatch with captured input.

## References

Adapts Computability/Probabilistic/Finite.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases
    {α β Tag : Type} [Finite Tag] {input : α ↪ List Bool} {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableInPolyTime (branch choice) input output) :
    ComputableInPolyTime (fun a => branch (tag a) a) input output := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableInPolyTime (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        simpa only [List.foldr_cons, decide_eq_true_eq] using
          (htag.decide_eq' (const choice)).ite (hbranch choice) ih
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases
    {α β Tag : Type} [Finite Tag] {input : α ↪ List Bool} {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableTidilyInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableTidilyInPolyTime (branch choice) input output) :
    ComputableTidilyInPolyTime (fun a => branch (tag a) a) input output := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableTidilyInPolyTime (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih => exact (htag.decide_eq' (const choice)).ite_decide (hbranch choice) ih
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime


