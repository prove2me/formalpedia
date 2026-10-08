-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_List
-- name    : APSPSource_ThreeSumApsp_Util_List
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:54.334244+00:00
-- url     : https://prove2.me/theorems/a39a7127-3ffd-4efe-90f5-a6b48d29fd10
-- title:
--   List bounds, entrywise sums, and running minima
-- statement:
--   For an integer list $l$ and integer bound $U$, define
--
--   $$\operatorname{AbsLe}(l,U)\iff\forall x\in l,\ |x|\le U.$$
--
--   The entrywise-sum operation starts with $N$ zeros and repeatedly adds a list using paired entries. When every input list has length $N$, its entry $i<N$ is the sum of their entries at $i$. With unequal lengths, paired addition truncates to the shorter list.
--
--   The accompanying list interfaces identify an entry of the table $[f(0),\ldots,f(n-1)]$ with $f(i)$ for $i<n$. For $f:\mathbb N\to B$ into any linearly ordered type, the running minimum initialized at $f(0)$ and updated through $f(m)$ satisfies
--
--   $$M_m\le f(k)\quad(k\le m),\qquad \exists k\le m,\ M_m=f(k).$$
--
--   These definitions and structural properties support bounded integer arrays, table lookups, and finite selection routines.
--
--   References:
--
--   1. [Source formalization, lines 67–71](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L67-L71).
--   2. [Source formalization, lines 280–301](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L280-L301).
--   3. [Source formalization, lines 435–436](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L435-L436).
--   4. [Source formalization, lines 455–457](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L455-L457).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L67-L71; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L280-L301; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L435-L436; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L455-L457

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/























/-- Entry `i < n` of the table `f 0, …, f (n - 1)`. -/
theorem getD_map_range (f : ℕ → α) {n i : ℕ} (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp



































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/

/-- A running minimum over `f 0, …, f m` is a lower bound of these values. -/
theorem foldl_min_le [LinearOrder β] (f : ℕ → β) (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) ≤ f k := by
  induction m with
  | zero => exact (Nat.le_zero.1 hk ▸ le_rfl : f 0 ≤ f k)
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.le_succ_iff.1 hk with h | rfl
    · exact (min_le_left _ _).trans (ih h)
    · exact min_le_right _ _

/-- A running minimum over `f 0, …, f m` is one of these values. -/
theorem exists_foldl_min_eq [LinearOrder β] (f : ℕ → β) (m : ℕ) :
    ∃ k ≤ m, (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) = f k := by
  induction m with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk, he⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, he]
    rcases le_total (f k) (f (m + 1)) with h | h
    · exact ⟨k, Nat.le_succ_of_le hk, min_eq_left h⟩
    · exact ⟨m + 1, le_rfl, min_eq_right h⟩

/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/

/-- All members of the list `l` have absolute value at most `U`. -/
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U
















/-! ## The entrywise sum of lists -/

/-- The entrywise sum of lists of length `len`. -/
def sumLists (len : ℕ) (ls : List (List ℤ)) : List ℤ :=
  ls.foldl (fun acc l => List.zipWith (· + ·) acc l) (List.replicate len 0)


















end ThreeSumApsp


