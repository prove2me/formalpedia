-- Prove2me | Definitions.Def_OddOrder_GroupTheory_SolvablePrimeIndex
-- name    : OddOrder_GroupTheory_SolvablePrimeIndex
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:29.198749+00:00
-- url     : https://prove2.me/theorems/58ab54a4-c38d-4c32-930a-5c67a4962c67
-- title:
--   Normal subgroups of prime index in finite solvable groups
-- statement:
--   A shared lemma: a nontrivial finite solvable group has a normal subgroup of prime index. It consolidates a roughly 30-line proof that had been duplicated in the Fong–Swan file and in the BG §7 Hypothesis 7.5 file.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/SolvablePrimeIndex.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/SolvablePrimeIndex.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OddOrder.GroupTheory

/-- **A nontrivial finite solvable group has a normal subgroup of prime index.**  Take a proper
normal subgroup `N` of maximal order; the quotient `Q ⧸ N` is simple and solvable, hence abelian,
so `Group.is_simple_iff_prime_card` gives `[Q:N] = |Q ⧸ N|` prime. -/
theorem exists_normal_index_prime_of_isSolvable {Q : Type*} [Group Q] [Finite Q]
    [Group.IsSolvable Q] (hQ : Nontrivial Q) : ∃ N : Subgroup Q, N.Normal ∧ N.index.Prime := by
  obtain ⟨N, hNmem, hNmax⟩ :=
    Set.exists_max_image {N : Subgroup Q | N.Normal ∧ N < ⊤} (fun N : Subgroup Q => Nat.card ↥N)
      (Set.toFinite _) ⟨⊥, inferInstance, bot_lt_top⟩
  obtain ⟨hNnorm, hNlt⟩ := hNmem
  have := hNnorm
  refine ⟨N, hNnorm, ?_⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hntq : Nontrivial (Q ⧸ N) := by
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt hNlt
    exact ⟨QuotientGroup.mk x, 1, by rw [Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  have hsimple : IsSimpleGroup (Q ⧸ N) := by
    refine ⟨fun Nbar hNbar => ?_⟩
    set N' : Subgroup Q := Nbar.comap (QuotientGroup.mk' N) with hN'
    have : N'.Normal := hNbar.comap _
    have hNN' : N ≤ N' := by
      intro x hx
      rw [hN', Subgroup.mem_comap,
        show (QuotientGroup.mk' N) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hmapeq : N'.map (QuotientGroup.mk' N) = Nbar := by
      rw [hN', Subgroup.map_comap_eq_self_of_surjective hsurj]
    rcases lt_or_eq_of_le (le_top : N' ≤ ⊤) with hN'lt | hN'top
    · left
      have hcard : Nat.card ↥N' ≤ Nat.card ↥N := hNmax N' ⟨inferInstance, hN'lt⟩
      have hN'eqN : N = N' := Subgroup.eq_of_le_of_card_ge hNN' hcard
      rw [← hmapeq, ← hN'eqN]
      simp [QuotientGroup.map_mk'_self]
    · right
      rw [← hmapeq, hN'top, Subgroup.map_top_of_surjective _ hsurj]
  have : IsMulCommutative (Q ⧸ N) := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
  rw [Subgroup.index_eq_card]
  exact Group.is_simple_iff_prime_card.mp hsimple

end OddOrder.GroupTheory


