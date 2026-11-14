-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDupsBy
-- name    : Complexitylib_0ebd467_Foundations_Data_List_EraseDupsBy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:54.053312+00:00
-- url     : https://prove2.me/theorems/d93e7f94-6233-4e0b-85e5-491cf0f4e302
-- title:
--   Complexity.Foundations.Data.List.EraseDupsBy — Erasing duplicates by a comparison
-- statement:
--   This is module `Complexity.Foundations.Data.List.EraseDupsBy` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `List.eraseDupsBy r l` keeps the first entry of `l` in each run of entries related by `r`, in
--   order. This file supplies the lemmas that core Lean lacks: the result is a sublist of `l`
--   (`List.eraseDupsBy_sublist`), no kept entry is related to an earlier one
--   (`List.pairwise_eraseDupsBy`), and every entry of `l` is related to some kept entry or is one
--   (`List.exists_mem_eraseDupsBy`). The function is also a left fold that appends an entry
--   when no kept entry is related to it (`List.eraseDupsBy_eq_foldl`), which lets fold rules
--   certify it.
--
--   ### Main results
--
--   * `List.eraseDupsBy_eq_foldl`: `eraseDupsBy` as a left fold.
--   * `List.eraseDupsBy_sublist`, `List.pairwise_eraseDupsBy`, `List.exists_mem_eraseDupsBy`.
--   * `List.nodup_eraseDupsBy_eq`, `List.mem_eraseDupsBy_eq`: erasing duplicates by equality keeps
--     one copy of each entry.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDupsBy`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/List/EraseDupsBy.lean

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
public import Mathlib.Data.List.Basic

/- Prove2me definition bundle for `Complexity.Foundations.Data.List.EraseDupsBy` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Erasing duplicates by a comparison

`List.eraseDupsBy r l` keeps the first entry of `l` in each run of entries related by `r`, in
order. This file supplies the lemmas that core Lean lacks: the result is a sublist of `l`
(`List.eraseDupsBy_sublist`), no kept entry is related to an earlier one
(`List.pairwise_eraseDupsBy`), and every entry of `l` is related to some kept entry or is one
(`List.exists_mem_eraseDupsBy`). The function is also a left fold that appends an entry
when no kept entry is related to it (`List.eraseDupsBy_eq_foldl`), which lets fold rules
certify it.

## Main results

* `List.eraseDupsBy_eq_foldl`: `eraseDupsBy` as a left fold.
* `List.eraseDupsBy_sublist`, `List.pairwise_eraseDupsBy`, `List.exists_mem_eraseDupsBy`.
* `List.nodup_eraseDupsBy_eq`, `List.mem_eraseDupsBy_eq`: erasing duplicates by equality keeps
  one copy of each entry.
-/

@[expose] public section

namespace List

variable {α : Type*} {r : α → α → Bool}

private theorem eraseDupsBy_loop_eq_foldl (as bs : List α) :
    eraseDupsBy.loop r as bs =
      as.foldl (fun kept a => if kept.any (r a) then kept else kept ++ [a]) bs.reverse := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
    rw [eraseDupsBy.loop, foldl_cons, any_reverse]
    cases h : bs.any (r a) <;> simp [ih]

/-- `eraseDupsBy` appends each entry that is related to no entry kept so far. -/
theorem eraseDupsBy_eq_foldl (l : List α) :
    l.eraseDupsBy r = l.foldl (fun kept a => if kept.any (r a) then kept else kept ++ [a]) [] :=
  eraseDupsBy_loop_eq_foldl l []

/-- `eraseDupsBy` keeps a sublist. -/
theorem eraseDupsBy_sublist : ∀ l : List α, (l.eraseDupsBy r).Sublist l
  | [] => by simp
  | a :: as => by
    have : (as.filter fun b => r b a = false).length < as.length + 1 :=
      Nat.lt_add_one_of_le (length_filter_le _ as)
    rw [eraseDupsBy_cons]
    exact ((eraseDupsBy_sublist _).trans (filter_sublist ..)).cons_cons a
termination_by l => l.length
decreasing_by
  all_goals first
    | exact Nat.lt_add_one_of_le (length_filter_le _ _)
    | (simp only [length_cons]; exact Nat.lt_add_one_of_le (length_filter_le _ _))

/-- No entry kept by `eraseDupsBy` is related to an earlier kept entry. -/
theorem pairwise_eraseDupsBy : ∀ l : List α,
    (l.eraseDupsBy r).Pairwise fun a b => r b a = false
  | [] => by simp
  | a :: as => by
    have : (as.filter fun b => r b a = false).length < as.length + 1 :=
      Nat.lt_add_one_of_le (length_filter_le _ as)
    rw [eraseDupsBy_cons]
    refine pairwise_cons.2 ⟨fun b hb => ?_, pairwise_eraseDupsBy _⟩
    simpa using (mem_filter.1 ((eraseDupsBy_sublist _).subset hb)).2
termination_by l => l.length
decreasing_by
  all_goals first
    | exact Nat.lt_add_one_of_le (length_filter_le _ _)
    | (simp only [length_cons]; exact Nat.lt_add_one_of_le (length_filter_le _ _))

/-- Every entry of `l` is kept by `eraseDupsBy`, or related to a kept entry. -/
theorem exists_mem_eraseDupsBy : ∀ {l : List α} {a : α}, a ∈ l →
    ∃ b ∈ l.eraseDupsBy r, a = b ∨ r a b = true
  | [], _, ha => by simp at ha
  | c :: as, a, ha => by
    have : (as.filter fun b => r b c = false).length < as.length + 1 :=
      Nat.lt_add_one_of_le (length_filter_le _ as)
    rw [eraseDupsBy_cons]
    rcases mem_cons.1 ha with rfl | ha
    · exact ⟨a, mem_cons_self .., .inl rfl⟩
    · cases hrc : r a c
      · obtain ⟨b, hb, hab⟩ := exists_mem_eraseDupsBy (l := as.filter fun b => r b c = false)
          (mem_filter.2 ⟨ha, by simpa using hrc⟩)
        exact ⟨b, mem_cons_of_mem _ hb, hab⟩
      · exact ⟨c, mem_cons_self .., .inr hrc⟩
termination_by l => l.length
decreasing_by
  all_goals first
    | exact Nat.lt_add_one_of_le (length_filter_le _ _)
    | (simp only [length_cons]; exact Nat.lt_add_one_of_le (length_filter_le _ _))

section Eq

variable [DecidableEq α]

/-- Erasing duplicates by equality leaves no duplicates. -/
theorem nodup_eraseDupsBy_eq (l : List α) : (l.eraseDupsBy fun a b => decide (a = b)).Nodup :=
  (pairwise_eraseDupsBy l).imp fun h => by simpa [eq_comm] using h

/-- Erasing duplicates by equality keeps every entry. -/
theorem mem_eraseDupsBy_eq {l : List α} {a : α} :
    a ∈ l.eraseDupsBy (fun a b => decide (a = b)) ↔ a ∈ l := by
  refine ⟨fun h => (eraseDupsBy_sublist l).subset h, fun h => ?_⟩
  obtain ⟨b, hb, rfl | hab⟩ := exists_mem_eraseDupsBy (r := fun a b => decide (a = b)) h
  · exact hb
  · rwa [of_decide_eq_true hab]

end Eq

end List


