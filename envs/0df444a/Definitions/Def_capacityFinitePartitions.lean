-- Prove2me | Definitions.Def_capacityFinitePartitions
-- name    : capacityFinitePartitions
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T18:02:52.794249+00:00
-- url     : https://prove2.me/theorems/0e4b124c-d299-4d9d-98fa-b2ccb8383675
-- title:
--   Finite partitions and additive block scores
-- statement:
--   Let $X$ be a finite label set. A partition of $X$ consists of disjoint nonempty subsets whose union is $X$. For each nonempty $B\subseteq X$, the bundle constructs the partition with block $B$ and singleton blocks outside $B$. For rational coefficients $c_C$ indexed by subsets, define the additive block score
--
--   $$R_c(P)=\sum_{C\in P}c_C.$$
--
--   The accompanying constructor support identifies the coefficients of a row relation: if $R_c(P)=0$ for every partition, then each nonempty-block coefficient is the sum of its singleton coefficients, whose total is zero. Conversely, zero-sum singleton potentials give zero additive score on every partition. These constructions provide the finite-partition interface used by the incidence-rank theorems. The definitions allow an empty label set where their arguments exist; the empty-block coefficient never contributes to a genuine partition score.
-- source:
--   The four-label correlation threshold, Theorem 2.1 and equations (2.3)–(2.5). Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/Partition.lean, source-file SHA-256 e27cd0d841c3f89c9cb3f99679bd9d9533f521e19d7d895da92e77377a128630. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

set_option autoImplicit false

/-!
# Finite partitions and their block-incidence rows

We use mathlib's `Finpartition` representation.  The key test partition has
one prescribed nonempty block `S` and singleton blocks outside `S`.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset

variable {α R : Type*} [Fintype α] [DecidableEq α]

/-- The blocks of the partition with one prescribed block `S` and singleton
blocks on its complement. -/
def isolateBlockParts (S : Finset α) : Finset (Finset α) :=
  insert S ((univ \ S).image singleton)

/-- The partition with one prescribed nonempty block and singleton blocks
outside it. -/
def isolateBlock (S : Finset α) (hS : S.Nonempty) : Finpartition (univ : Finset α) :=
  Finpartition.ofExistsUnique (isolateBlockParts S)
    (by
      intro p hp
      simp only [isolateBlockParts, mem_insert, mem_image] at hp
      rcases hp with rfl | ⟨a, _, rfl⟩
      · exact subset_univ _
      · exact subset_univ {a})
    (by
      intro a _
      by_cases ha : a ∈ S
      · refine ⟨S, ⟨mem_insert_self S _, ha⟩, ?_⟩
        intro t ht
        simp only [isolateBlockParts, mem_insert] at ht
        rcases ht.1 with h | h
        · exact h
        · obtain ⟨b, hb, rfl⟩ := mem_image.mp h
          simp only [mem_sdiff, mem_univ, true_and] at hb
          simp only [mem_singleton] at ht
          have hab : a = b := ht.2
          subst b
          exact (hb ha).elim
      · refine ⟨{a}, ⟨mem_insert_of_mem (mem_image.mpr ⟨a, ?_, rfl⟩), mem_singleton_self a⟩, ?_⟩
        · simp [ha]
        · intro t ht
          simp only [isolateBlockParts, mem_insert] at ht
          rcases ht.1 with h | h
          · subst t
            exact (ha ht.2).elim
          · obtain ⟨b, _, rfl⟩ := mem_image.mp h
            simp only [mem_singleton] at ht
            simp [ht.2])
    (by
      intro h
      simp only [isolateBlockParts, mem_insert] at h
      rcases h with h | h
      · exact hS.ne_empty h.symm
      · obtain ⟨a, _, hEq⟩ := mem_image.mp h
        exact Finset.singleton_ne_empty a hEq)

@[simp]
theorem isolateBlock_parts (S : Finset α) (hS : S.Nonempty) :
    (isolateBlock S hS).parts = isolateBlockParts S := rfl

/-- Every block of a finite partition contributes its coefficient once. -/
def blockRowSum [AddCommMonoid R] (c : Finset α → R)
    (P : Finpartition (univ : Finset α)) : R :=
  ∑ B ∈ P.parts, c B

/-- A block-incidence row relation is necessarily a modular singleton
potential.  This is the structural statement behind `rank A_n = 2^n - n`.
-/
theorem rowRelation_eq_sum_singletons
    [AddCommGroup R] (c : Finset α → R)
    (hrel : ∀ P : Finpartition (univ : Finset α), blockRowSum c P = 0)
    {S : Finset α} (hS : S.Nonempty) :
    c S = ∑ i ∈ S, c {i} := by
  have hS_not_image : S ∉ (univ \ S).image singleton := by
    intro h
    obtain ⟨a, ha, hEq⟩ := mem_image.mp h
    have ha_not : a ∉ S := by simpa using ha
    have ha_mem : a ∈ S := by
      have : a ∈ ({a} : Finset α) := mem_singleton_self a
      rwa [hEq] at this
    exact ha_not ha_mem
  have hisolate := hrel (isolateBlock S hS)
  simp only [blockRowSum, isolateBlock_parts, isolateBlockParts,
    sum_insert hS_not_image] at hisolate
  have hsingle_inj : Set.InjOn (fun x : α ↦ ({x} : Finset α))
      (↑(univ \ S) : Set α) := by
    intro a _ b _ h
    exact singleton_injective h
  rw [sum_image hsingle_inj] at hisolate

  have hdiscrete := hrel (⊥ : Finpartition (univ : Finset α))
  simp only [blockRowSum, Finpartition.parts_bot] at hdiscrete
  rw [sum_map] at hdiscrete
  simp only [Function.Embedding.coeFn_mk] at hdiscrete

  have hunion : S ∪ (univ \ S) = (univ : Finset α) := by ext i; simp
  have hdisj : Disjoint S (univ \ S) := Finset.disjoint_sdiff
  have hsplit :
      (∑ i ∈ (univ : Finset α), c {i}) =
        (∑ i ∈ S, c {i}) + ∑ i ∈ (univ \ S), c {i} := by
    rw [← sum_union hdisj, hunion]
  rw [hsplit] at hdiscrete
  exact (eq_neg_of_add_eq_zero_left hisolate).trans
    (neg_eq_of_add_eq_zero_left hdiscrete)

/-- The singleton potentials in a block-incidence row relation sum to zero. -/
theorem rowRelation_singletons_sum_zero
    [AddCommGroup R] (c : Finset α → R)
    (hrel : ∀ P : Finpartition (univ : Finset α), blockRowSum c P = 0) :
    ∑ i : α, c {i} = 0 := by
  have h := hrel (⊥ : Finpartition (univ : Finset α))
  simp only [blockRowSum, Finpartition.parts_bot] at h
  rw [sum_map] at h
  simpa only [Function.Embedding.coeFn_mk, sum_attach] using h

/-- Conversely, zero-sum singleton potentials give block-incidence row
relations on every finite partition. -/
theorem sum_singletons_rowRelation
    [AddCommGroup R] (a : α → R) (ha : ∑ i, a i = 0)
    (P : Finpartition (univ : Finset α)) :
    ∑ B ∈ P.parts, (∑ i ∈ B, a i) = 0 := by
  calc
    (∑ B ∈ P.parts, (∑ i ∈ B, a i)) =
        ∑ i ∈ P.parts.biUnion id, a i :=
      (Finset.sum_biUnion (f := a) (t := id) P.disjoint).symm
    _ = ∑ i : α, a i := by rw [P.biUnion_parts]
    _ = 0 := ha

end FormalCapacity.Finite


