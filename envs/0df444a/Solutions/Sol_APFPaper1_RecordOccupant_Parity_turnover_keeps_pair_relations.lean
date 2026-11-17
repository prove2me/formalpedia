-- Prove2me | solution 1 for APFPaper1.RecordOccupant.Parity.turnover_keeps_pair_relations
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:28:09.423197+00:00
-- url     : https://prove2.me/submissions/69c7fc99-7f24-4fc1-9fc9-915e3eedd0fc

import Definitions.Def_APFPaper1_RecordOccupant_three_way_relation_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_three_way_relation
title: A record that an odd number of three distinctions are on the true side leaves each of them in raw form and settles no relation between any two, and is not fixed by the relations between pairs; yet it is a relation between two marks one level up, the mark "the first two differ" and the third
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:48: "Jointness stops at pairs". 20:54: "Proceed" (to the test: do the
 eight admit a world with a three-way relation record). Def_APFPaper1_RecordOccupant and
 Thm_APFPaper1_RecordOccupant_sections_and_free_moves (this seat; the Triangle world).
 NOTE_two_way_superposition_orientations_2026-11-14, NOTE_four_and_six_way_2026-11-14.
standing: A WORLD at the level of sides and records. It is NOT a world meeting the eight declared forms:
 no protocols, costs or capacities are supplied, so nothing here says the eight admit such a record with a
 cost. Only B02's second sentence is checked (every_combination_held).
what this file says:
 1. members_raw, pairs_unsettled, triple_settled. With the one record kept, each of the three
    distinctions has no side, no two of them have a settled relation, and the relation of all three is
    settled.
 2. turnover_keeps_pair_relations, turnover_breaks_record. Turning every side over keeps the relation
    between every two distinctions and breaks the record. So the record is not fixed by the pair
    relations among the three: in terms of the three alone it is three-way.
 3. is_pair_relation_one_level_up. The same record says that the mark "the first two differ" and the third
    distinction are on opposite sides. If a relation between two marks is itself a mark, the record is a
    relation between two marks.
reading: whether "jointness stops at pairs" excludes this record depends on what counts as a unit. Counted
 over the three distinctions alone it is three-way. Counted with relations as marks it is two-way, one
 level up. The author's adopted reading of B06 takes a held relation to be a tested task of its own.
what this file does NOT say: that the eight admit or exclude this record with a cost; that every three-way
 relation reduces in this way (with unrestricted derived marks every relation would, trivially); anything
 about a quadratic form. No lane. No claim that the transfer is forced, that the carrier gap is closed or
 narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper1_RecordOccupant_sections_and_free_moves_Vocabulary
import Theorems.Thm_APFPaper1_RecordOccupant_Triangle_three_cannot_be_kept

set_option autoImplicit false

namespace APFPaper1.RecordOccupant.Parity

open Triangle







theorem only_allowed (k : Corner) : only k ∈ allowed odd ({()} : Finset Unit) := by
  intro r _
  cases k <;> rfl

theorem allTrue_allowed : allTrue ∈ allowed odd ({()} : Finset Unit) := by
  intro r _
  rfl

/-- B02's second sentence holds: every combination of sides is held by some potential state. -/
theorem every_combination_held : APFB02.EveryCombinationHeld side :=
  Triangle.every_combination_held

/-- Each of the three distinctions is in raw form. -/
theorem members_raw (d : Corner) : NoSide side odd ({()} : Finset Unit) d := by
  refine ⟨⟨only d, only_allowed d, ?_⟩, ?_⟩
  · cases d <;> rfl
  · cases d
    · exact ⟨only .b, only_allowed .b, rfl⟩
    · exact ⟨only .c, only_allowed .c, rfl⟩
    · exact ⟨only .a, only_allowed .a, rfl⟩

/-- No relation between two of them is settled: some allowed state has them on the same side and some has
them on different sides. -/
theorem pairs_unsettled (d e : Corner) (h : d ≠ e) :
    (∃ x ∈ allowed odd ({()} : Finset Unit), x d = x e) ∧
      (∃ y ∈ allowed odd ({()} : Finset Unit), y d ≠ y e) := by
  refine ⟨⟨allTrue, allTrue_allowed, rfl⟩, ⟨only d, only_allowed d, ?_⟩⟩
  cases d <;> cases e <;> first | exact absurd rfl h | decide

/-- The relation of all three is settled: every allowed state has an odd number on the true side. -/
theorem triple_settled (x : Corner → Bool) (hx : x ∈ allowed odd ({()} : Finset Unit)) : odd () x :=
  hx () (Finset.mem_singleton_self ())

/-- Turning every side over keeps the relation between every two distinctions. -/
theorem turnover_keeps_pair_relations (x : Corner → Bool) (d e : Corner) :
    ((!x d) = (!x e)) ↔ x d = x e := by
  cases x d <;> cases x e <;> simp

/-- Turning every side over breaks the record. -/
theorem turnover_breaks_record (x : Corner → Bool) (hx : odd () x) : ¬ odd () (fun d => !x d) := by
  unfold odd at hx ⊢
  cases h1 : x .a <;> cases h2 : x .b <;> cases h3 : x .c <;> simp_all

/-- One level up it is a relation between two marks: "the first two differ" and the third are on opposite
sides. -/
theorem is_pair_relation_one_level_up (x : Corner → Bool) :
    odd () x ↔ (x .a != x .b) ≠ x .c := by
  unfold odd
  cases (x .a != x .b) <;> cases x .c <;> simp

end APFPaper1.RecordOccupant.Parity


theorem solution :
∀ (x : APFPaper1.RecordOccupant.Triangle.Corner → Bool) (d e : APFPaper1.RecordOccupant.Triangle.Corner),
  Iff (@Eq.{1} Bool (Bool.not (x d)) (Bool.not (x e))) (@Eq.{1} Bool (x d) (x e)) := by
  exact @APFPaper1.RecordOccupant.Parity.turnover_keeps_pair_relations
