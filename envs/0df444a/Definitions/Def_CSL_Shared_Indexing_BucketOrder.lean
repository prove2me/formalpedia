-- Prove2me | Definitions.Def_CSL_Shared_Indexing_BucketOrder
-- name    : CSL_Shared_Indexing_BucketOrder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:33.245838+00:00
-- url     : https://prove2.me/theorems/1f790f50-6b3d-4182-b858-13ea26cf374b
-- title:
--   Coded sorting library: Shared / Indexing / BucketOrder
-- statement:
--   Module `CodedSorting.Shared.Indexing.BucketOrder` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Ordered bucket concatenation. These combinatorial lemmas show that concatenating internally ordered buckets gives a sorted list when every value in an earlier bucket is at most every value in a later bucket.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Indexing.BucketOrder

import Definitions.Def_CSL_Compat
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Init

/-! Ordered bucket concatenation. These combinatorial lemmas show that concatenating internally ordered buckets gives a sorted list when every value in an earlier bucket is at most every value in a later bucket. 






-/

namespace CSL.BucketOrder

variable {α : Type*}

/-- Every element of the first list precedes every element of the second. -/
def Between (R : α → α → Prop) (xs ys : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ ys, R x y

/-- Appending internally ordered lists is valid under the full cross-boundary
ordering condition, including empty lists and repeated values. -/
theorem pairwise_append_of_between {R : α → α → Prop} {xs ys : List α}
    (hx : xs.Pairwise R) (hy : ys.Pairwise R) (hxy : Between R xs ys) :
    (xs ++ ys).Pairwise R := by
  induction xs with
  | nil => simpa using hy
  | cons a xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hx
    apply List.pairwise_cons.mpr
    constructor
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hhead b hb
      · exact hxy a (by simp) b hb
    · apply ih htail
      intro x hx y hy
      exact hxy x (by simp [hx]) y hy

/-- All buckets internally ordered, and every earlier bucket entirely before
any later bucket, imply that their concatenation is ordered. -/
theorem pairwise_flatten_of_buckets {R : α → α → Prop}
    {buckets : List (List α)}
    (hwithin : ∀ xs ∈ buckets, xs.Pairwise R)
    (hbetween : buckets.Pairwise (Between R)) :
    buckets.flatten.Pairwise R := by
  induction buckets with
  | nil => simp
  | cons xs rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hbetween
    simp only [List.flatten_cons]
    apply pairwise_append_of_between (hwithin xs (by simp))
    · apply ih
      · intro ys hys
        exact hwithin ys (by simp [hys])
      · exact htail
    · intro x hx y hy
      obtain ⟨ys, hys, hy⟩ := List.mem_flatten.mp hy
      exact hhead ys hys x hx y hy

/-- Reordering each bucket preserves the multiset of all records. This is a
`List.Perm` statement, so multiplicities are retained. -/
theorem flatten_perm_of_bucket_perms {source target : List (List α)}
    (h : List.Forall₂ List.Perm source target) :
    source.flatten.Perm target.flatten := by
  induction h with
  | nil => exact List.Perm.refl []
  | cons hp hs ih =>
    simpa only [List.flatten_cons] using hp.append ih

/-- An existing decomposition of the input, followed by independent bucket
permutations, leaves the concatenated output a permutation of the input. -/
theorem output_perm_input {input : List α} {source target : List (List α)}
    (hpartition : input.Perm source.flatten)
    (hreorder : List.Forall₂ List.Perm source target) :
    target.flatten.Perm input := by
  exact (flatten_perm_of_bucket_perms hreorder).symm.trans hpartition.symm

/-- Complete combinatorial contract for merging already sorted buckets.
This is conditional on the four explicitly supplied bucket properties. -/
theorem sorted_permutation_of_buckets [LE α]
    {input : List α} {source target : List (List α)}
    (hpartition : input.Perm source.flatten)
    (hreorder : List.Forall₂ List.Perm source target)
    (hwithin : ∀ xs ∈ target, xs.Pairwise (· ≤ ·))
    (hbetween : target.Pairwise (Between (· ≤ ·))) :
    target.flatten.Pairwise (· ≤ ·) ∧ target.flatten.Perm input := by
  exact ⟨pairwise_flatten_of_buckets hwithin hbetween,
    output_perm_input hpartition hreorder⟩

/-- Strict ordering of the high part forces strict ordering of the full
nonnegative integer. For radix sorting `base` is a positive power of two. -/
theorem lt_of_high_part_lt {a b base : ℕ} (h : a / base < b / base) : a < b := by
  exact Nat.lt_of_div_lt_div h

/-- Two buckets identified by strictly increasing high parts satisfy the
cross-bucket ordering hypothesis used above. -/
theorem between_of_high_parts {base ka kb : ℕ} {xs ys : List ℕ}
    (hkey : ka < kb)
    (hx : ∀ x ∈ xs, x / base = ka)
    (hy : ∀ y ∈ ys, y / base = kb) :
    Between (· ≤ ·) xs ys := by
  intro x hxm y hym
  apply Nat.le_of_lt
  apply lt_of_high_part_lt (base := base)
  rw [hx x hxm, hy y hym]
  exact hkey

end CSL.BucketOrder


