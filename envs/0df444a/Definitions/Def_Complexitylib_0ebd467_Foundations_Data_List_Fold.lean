-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Fold
-- name    : Complexitylib_0ebd467_Foundations_Data_List_Fold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:54.545219+00:00
-- url     : https://prove2.me/theorems/cf63c104-b482-4843-8898-06d3b176a692
-- title:
--   Complexity.Foundations.Data.List.Fold — List fold invariants and selection
-- statement:
--   This is module `Complexity.Foundations.Data.List.Fold` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   ### Main results
--
--   * `List.foldl_take_invariant`: an index-dependent invariant holds after every prefix of a fold.
--   * `List.foldl_keep_fst`: folding a step that keeps the first component of a pair preserves that
--     component and folds over the second.
--   * `List.foldr_ite_eq_of_mem`: a chain of equality tests selects the branch of a contained tag,
--     regardless of duplicates or fallback. Used by finite-control certificates.
--   * `List.foldl_or_eq`, `List.foldl_min_add_eq`: folding a disjunction is `List.any`, and folding a
--     sum capped at `cap` caps the sum.
--
--   ### References
--
--   Adapts the selection identity from Computability/Probabilistic/Finite.lean on the cslib
--   `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Fold`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/List/Fold.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.List.Basic

/- Prove2me definition bundle for `Complexity.Foundations.Data.List.Fold` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# List fold invariants and selection

## Main results

* `List.foldl_take_invariant`: an index-dependent invariant holds after every prefix of a fold.
* `List.foldl_keep_fst`: folding a step that keeps the first component of a pair preserves that
  component and folds over the second.
* `List.foldr_ite_eq_of_mem`: a chain of equality tests selects the branch of a contained tag,
  regardless of duplicates or fallback. Used by finite-control certificates.
* `List.foldl_or_eq`, `List.foldl_min_add_eq`: folding a disjunction is `List.any`, and folding a
  sum capped at `cap` caps the sum.

## References

Adapts the selection identity from Computability/Probabilistic/Finite.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

/-- An invariant depending on the number of consumed elements holds after every bounded prefix
fold if it holds initially and is preserved by the next list element. Unlike `List.foldlRecOn`,
preservation may depend on the position. This is a semantic rule with no resource assumptions. -/
theorem List.foldl_take_invariant {α β : Type*} (l : List α) (step : β → α → β) (init : β)
    (P : ℕ → β → Prop) (hbase : P 0 init)
    (hstep : ∀ i (hi : i < l.length) state, P i state → P (i + 1) (step state l[i])) :
    ∀ i, i ≤ l.length → P i ((l.take i).foldl step init) := by
  intro i
  induction i with
  | zero => intro _; simpa only [List.take_zero, List.foldl_nil] using hbase
  | succ i ih =>
    intro hi
    have hlt : i < l.length := Nat.lt_of_succ_le hi
    simpa only [List.take_succ_eq_append_getElem hlt, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hstep i hlt _ (ih (Nat.le_of_lt hlt))

/-- Folding a step that keeps the first component of a pair preserves that component and folds
over the second. -/
theorem List.foldl_keep_fst {ι π α : Type*} (step : π → α → ι → α)
    (par : π) (xs : List ι) (init : α) :
    xs.foldl (fun pa i => (pa.1, step pa.1 pa.2 i)) (par, init) =
      (par, xs.foldl (step par) init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- A chain of equality tests selects a contained tag, regardless of duplicates or fallback. -/
theorem List.foldr_ite_eq_of_mem {Tag Value : Type*} [DecidableEq Tag]
    (tags : List Tag) (tag : Tag) (branch : Tag → Value) (fallback : Value) (h : tag ∈ tags) :
    tags.foldr (fun candidate rest => if tag = candidate then branch candidate else rest)
      fallback = branch tag := by
  induction tags with
  | nil => simp at h
  | cons candidate tags ih =>
    by_cases heq : tag = candidate
    · simp [heq]
    · simp only [List.foldr_cons, heq, ↓reduceIte]
      exact ih (List.mem_cons.mp h |>.resolve_left heq)

/-- Folding a disjunction over a list adds whether some element satisfies the test. -/
theorem List.foldl_or_eq {α : Type*} (f : α → Bool) (b : Bool) (l : List α) :
    l.foldl (fun acc x => acc || f x) b = (b || l.any f) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => simp [ih, Bool.or_assoc]

/-- Folding a sum capped at `cap` over a list, from a value at most `cap`, caps the whole sum. -/
theorem List.foldl_min_add_eq {α : Type*} (cap : ℕ) (f : α → ℕ) {b : ℕ} (hb : b ≤ cap)
    (l : List α) : l.foldl (fun acc x => min cap (acc + f x)) b = min cap (b + (l.map f).sum) := by
  induction l generalizing b with
  | nil => simpa using (Nat.min_eq_right hb).symm
  | cons x l ih =>
    rw [List.foldl_cons, ih (Nat.min_le_left _ _), List.map_cons, List.sum_cons]
    omega


