-- Prove2me | Definitions.Def_CSL_Circuit_Framework_CircuitCounts
-- name    : CSL_Circuit_Framework_CircuitCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:34:08.73839+00:00
-- url     : https://prove2.me/theorems/fb5560ee-bdb3-4207-bc1e-cb81295d598a
-- title:
--   Coded sorting library: Circuit / Framework / CircuitCounts
-- statement:
--   Module `CodedSorting.Circuit.Framework.CircuitCounts` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Counting the actual register types
--
--   The side-register count is obtained from a bijection, not by assigning the
--   paper's numerical formula to an unrelated natural-number definition.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.CircuitCounts

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_CircuitProgram
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring

/-!
# Counting the actual register types

The side-register count is obtained from a bijection, not by assigning the
paper's numerical formula to an unrelated natural-number definition.
-/

namespace CSL.CircuitCounts

open CSL.Circuit CSL.CircuitProgram
open scoped BigOperators

variable {d : ℕ}

abbrev OutsidePairs (S : Triple d) :=
  {r : Finset (Fin d) // r ∈ (Finset.univ \ S.val).powersetCard 2}

abbrev Neighbours (S : Triple d) := {T : Triple d // side S T}

noncomputable instance (S : Triple d) : Fintype (Neighbours S) := Fintype.ofFinite _

theorem outside_properties (S : Triple d) (r : OutsidePairs S) :
    r.val ⊆ Finset.univ \ S.val ∧ r.val.card = 2 := Finset.mem_powersetCard.mp r.property

theorem outside_not_mem (S : Triple d) (r : OutsidePairs S) (x : Fin d)
    (hx : x ∈ r.val) : x ∉ S.val := (Finset.mem_sdiff.mp ((outside_properties S r).1 hx)).2

theorem inserted_intersection (S : Triple d) (i : S.val) (r : OutsidePairs S) :
    S.val ∩ insert i.val r.val = {i.val} := by
  ext x
  have hr := outside_not_mem S r x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, heq | hm⟩
    · exact heq
    · exact False.elim (hr hm hs)
  · intro heq
    subst x
    exact ⟨i.property, Or.inl rfl⟩

theorem inserted_difference (S : Triple d) (i : S.val) (r : OutsidePairs S) :
    insert i.val r.val \ S.val = r.val := by
  ext x
  have hr := outside_not_mem S r x
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨heq | hm, hn⟩
    · subst x
      exact False.elim (hn i.property)
    · exact hm
  · intro hm
    exact ⟨Or.inr hm, hr hm⟩

noncomputable def makeNeighbour (S : Triple d) (p : S.val × OutsidePairs S) : Neighbours S := by
  let T : Triple d := ⟨insert p.1.val p.2.val, by
    have hn : p.1.val ∉ p.2.val := fun h => outside_not_mem S p.2 _ h p.1.property
    rw [Finset.card_insert_of_notMem hn, (outside_properties S p.2).2]⟩
  exact ⟨T, by unfold side; dsimp only [T]; rw [inserted_intersection]; simp⟩

theorem makeNeighbour_injective (S : Triple d) : Function.Injective (makeNeighbour S) := by
  rintro ⟨i, r⟩ ⟨j, t⟩ heq
  have hs : insert i.val r.val = insert j.val t.val := congrArg (fun n : Neighbours S => n.val.val) heq
  have hi := congrArg (fun u => S.val ∩ u) hs
  try dsimp only at hi
  rw [inserted_intersection, inserted_intersection] at hi
  have hij : i = j := Subtype.ext (Finset.singleton_injective hi)
  have ht := congrArg (fun u => u \ S.val) hs
  try dsimp only at ht
  rw [inserted_difference, inserted_difference] at ht
  exact Prod.ext hij (Subtype.ext ht)

theorem makeNeighbour_surjective (S : Triple d) : Function.Surjective (makeNeighbour S) := by
  intro T
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp T.property
  have his : i ∈ S.val ∧ i ∈ T.val.val := by
    have hm : i ∈ S.val ∩ T.val.val := by rw [hi]; simp
    simpa using hm
  have hcard : (T.val.val \ S.val).card = 2 := by
    have hc := Finset.card_sdiff_add_card_inter T.val.val S.val
    rw [Finset.inter_comm, hi, Finset.card_singleton, T.val.property] at hc
    omega
  let r : OutsidePairs S := ⟨T.val.val \ S.val, Finset.mem_powersetCard.mpr
    ⟨by intro x hx; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩,
      hcard⟩⟩
  refine ⟨(⟨i, his.1⟩, r), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change insert i (T.val.val \ S.val) = T.val.val
  have hrec := Finset.sdiff_union_inter T.val.val S.val
  rw [Finset.inter_comm, hi] at hrec
  calc
    insert i (T.val.val \ S.val) = (T.val.val \ S.val) ∪ {i} := by
      ext x
      simp [or_comm]
    _ = T.val.val := hrec

noncomputable def neighbourEquiv (S : Triple d) :
    (S.val × OutsidePairs S) ≃ Neighbours S :=
  Equiv.ofBijective (makeNeighbour S) ⟨makeNeighbour_injective S, makeNeighbour_surjective S⟩

theorem neighbours_card (S : Triple d) :
    Fintype.card (Neighbours S) = 3 * (d - 3).choose 2 := by
  rw [← Fintype.card_congr (neighbourEquiv S), Fintype.card_prod]
  simp only [OutsidePairs, Fintype.card_coe]
  rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _), S.property]
  simp

theorem triples_card : Fintype.card (Triple d) = d.choose 3 := by
  simpa only [Fintype.card_fin] using (Fintype.card_finset_len (α := Fin d) 3)

def sideEquivSigma : SideIndex d ≃ Σ S : Triple d, Neighbours S where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem side_registers_card :
    Fintype.card (SideIndex d) = (d.choose 3) * (3 * (d - 3).choose 2) := by
  rw [Fintype.card_congr sideEquivSigma, Fintype.card_sigma]
  simp only [neighbours_card, Finset.sum_const, Finset.card_univ, smul_eq_mul, triples_card]

theorem data_registers_card : Fintype.card (DataIndex d) = (d.choose 3)^3 := by
  simp only [DataIndex, Fintype.card_prod, triples_card]
  ring

theorem groups_card : Fintype.card (GroupIndex d) = (d.choose 3)^2 := by
  simp only [GroupIndex, Fintype.card_prod, triples_card]
  ring

/-- This is the cardinality of the actual full-program register type. -/
theorem all_registers_card :
    Fintype.card (GlobalReg d) =
      2 * (d.choose 3)^3 + 3 * (d.choose 3)^2 * ((d.choose 3) * (3 * (d - 3).choose 2) + d) := by
  simp only [GlobalReg, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    data_registers_card, groups_card, side_registers_card, triples_card]
  ring

end CSL.CircuitCounts


