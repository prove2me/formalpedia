-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDups
-- name    : Complexitylib_0ebd467_Foundations_Data_List_EraseDups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:15.422205+00:00
-- url     : https://prove2.me/theorems/66419285-f1cb-4fb8-b0f7-2bb5ceff53ab
-- title:
--   Complexity.Foundations.Data.List.EraseDups — Erasing duplicates, keeping first occurrences
-- statement:
--   This is module `Complexity.Foundations.Data.List.EraseDups` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Core `List.eraseDups` keeps the first occurrence of each entry, in order, and core proves that it
--   keeps every entry (`List.mem_eraseDups`). This file adds that the result is a duplicate-free
--   sublist, that it fixes exactly the duplicate-free lists, and that its length is the number of
--   distinct entries.
--
--   ### Main results
--
--   * `List.eraseDups_sublist`, `List.nodup_eraseDups`, `List.eraseDups_eq_self`.
--   * `List.toFinset_eraseDups`, `List.length_eraseDups`.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDups`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/List/EraseDups.lean

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
public import Mathlib.Data.Finset.Card
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDupsBy

/- Prove2me definition bundle for `Complexity.Foundations.Data.List.EraseDups` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Erasing duplicates, keeping first occurrences

Core `List.eraseDups` keeps the first occurrence of each entry, in order, and core proves that it
keeps every entry (`List.mem_eraseDups`). This file adds that the result is a duplicate-free
sublist, that it fixes exactly the duplicate-free lists, and that its length is the number of
distinct entries.

## Main results

* `List.eraseDups_sublist`, `List.nodup_eraseDups`, `List.eraseDups_eq_self`.
* `List.toFinset_eraseDups`, `List.length_eraseDups`.
-/

public section

namespace List

variable {α : Type*}

/-- `eraseDups` keeps a sublist. -/
theorem eraseDups_sublist [BEq α] (l : List α) : l.eraseDups.Sublist l :=
  eraseDupsBy_sublist l

/-- `eraseDups` leaves no duplicates. -/
theorem nodup_eraseDups [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup :=
  (pairwise_eraseDupsBy l).imp fun h hab => by subst hab; simp at h

/-- `eraseDups` fixes exactly the duplicate-free lists. -/
theorem eraseDups_eq_self [BEq α] [LawfulBEq α] {l : List α} : l.eraseDups = l ↔ l.Nodup := by
  refine ⟨fun h => h ▸ nodup_eraseDups l, fun h => ?_⟩
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := nodup_cons.1 h
    have hfilter : (l.filter fun b => !b == a) = l :=
      filter_eq_self.2 fun b hb => by
        have hba : b ≠ a := fun hba => ha (hba ▸ hb)
        simpa using hba
    rw [eraseDups_cons, hfilter, ih hl]

variable [DecidableEq α]

@[simp] theorem toFinset_eraseDups (l : List α) : l.eraseDups.toFinset = l.toFinset := by
  ext
  simp

/-- The length of `eraseDups` is the number of distinct entries. -/
theorem length_eraseDups (l : List α) : l.eraseDups.length = l.toFinset.card := by
  rw [← toFinset_eraseDups, toFinset_card_of_nodup (nodup_eraseDups l)]

end List


