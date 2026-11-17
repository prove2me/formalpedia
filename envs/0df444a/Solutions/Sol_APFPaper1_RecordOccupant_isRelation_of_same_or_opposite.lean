-- Prove2me | solution 1 for APFPaper1.RecordOccupant.isRelation_of_same_or_opposite
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:40:40.046189+00:00
-- url     : https://prove2.me/submissions/1b1bec00-23b2-4ff7-9a58-ff8acccaab63

import Definitions.Def_APFPaper1_RecordOccupant_units_and_levels_Vocabulary
/-
APF Foundation Ledger — definition and theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv,
 2026-11-14; not gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_units_and_levels
title: Units, relations and levels for two-sided marks: a relation that a common turn leaves unchanged, that settles neither unit and that says something is "same side" or "opposite sides"; a unit is a distinction or the relation between two units; and across any cut a unit's side is the relation between a reading of one part and a reading of the other
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:48: "Jointness stops at pairs". 21:06: "Yes" (by levels; units are
 distinctions and recorded relations between two units). 21:15: "Proceed as advised" on
 TEE_UP_unit_rule_2026-11-14: call 1, candidate B (a relation is a record that settles neither unit and
 that turning both units over leaves unchanged); call 2, candidate C (only separate units may be related).
 Def_APFPaper1_RecordOccupant and the Triangle and Parity worlds (this seat).
standing:
 - IsRelation, Unt, Unt.reading, Unt.support, Unt.Separate, Unt.level: DEFINITIONS, adopted by the author
   at 21:15 HST as advised. They assert nothing and in particular no existence.
 - ByLevels: the author's statement of 20:48 and 21:06 HST written out for two-sided marks: every kept
   record says which side some unit is on. It is a CLAIM about a set of records, not a definition that
   holds by construction. STATED BY THE AUTHOR; not derived from the eight, not installed, and not yet
   sorted as a reading or an input. Every theorem that uses it takes it as a hypothesis.
what this file says:
 1. isRelation_same_or_opposite, isRelation_of_same_or_opposite. For two-sided units candidate B is
    exactly "same side" or "opposite sides".
 2. Unt.reading_factors_across_cut. Cut the distinctions into two parts in any way. The side of any unit
    is the relation between a reading that looks only at the first part and a reading that looks only at
    the second. No hypothesis; separateness is not needed for it.
 3. parity_is_side_of_level_two_unit, parity_world_is_by_levels. The parity record of pass 31 is the side
    record of a unit of level two built from separate units, and its world meets ByLevels.
what this file does NOT say:
 - That ByLevels holds of any physical context.
 - The condition of pass 32 on the builder seat's joint record book (FixedByProducts). Item 2 is its
   counterpart for two-sided marks only. The step from two-sided marks to a joint record book with values
   and rates is NOT made here and is not known to go through.
 - Anything about a continuum, a carrier or tensor closure. No lane. No claim that the transfer is forced,
   that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper1_RecordOccupant_three_way_relation_Vocabulary
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_every_combination_held
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_members_raw
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_pairs_unsettled
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_triple_settled
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_turnover_keeps_pair_relations
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_turnover_breaks_record
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_is_pair_relation_one_level_up

set_option autoImplicit false

universe u

namespace APFPaper1.RecordOccupant



/-- Such a relation is "same side" or "opposite sides". -/
theorem isRelation_same_or_opposite (f : Bool → Bool → Prop) (h : IsRelation f) :
    ∃ c : Bool, ∀ a b, f a b ↔ (a != b) = c := by
  obtain ⟨hinv, ⟨⟨b1, h1⟩, _, _, _⟩, ⟨a0, b0, hno⟩⟩ := h
  by_cases hs : f true true
  · refine ⟨false, ?_⟩
    have hff : f false false := (hinv true true).mp hs
    have hnt : ¬ f true false := by
      intro htf
      have hft : f false true := (hinv true false).mp htf
      cases a0 <;> cases b0
      · exact hno hff
      · exact hno hft
      · exact hno htf
      · exact hno hs
    have hnf : ¬ f false true := fun hft => hnt ((hinv false true).mp hft)
    clear hinv hno h1
    intro a b
    cases a <;> cases b <;> simp_all
  · refine ⟨true, ?_⟩
    have hnff : ¬ f false false := fun hff => hs ((hinv false false).mp hff)
    have htf : f true false := by
      cases b1
      · exact h1
      · exact absurd h1 hs
    have hft : f false true := (hinv true false).mp htf
    clear hinv hno h1
    intro a b
    cases a <;> cases b <;> simp_all

/-- "Same side" and "opposite sides" are such relations. -/
theorem isRelation_of_same_or_opposite (c : Bool) : IsRelation (fun a b => (a != b) = c) := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    cases a <;> cases b <;> simp
  · exact ⟨!c, by cases c <;> decide⟩
  · exact ⟨c, by cases c <;> decide⟩
  · exact ⟨!c, by cases c <;> decide⟩
  · exact ⟨c, by cases c <;> decide⟩
  · exact ⟨c, true, by cases c <;> decide⟩



namespace Unt

variable {D : Type u} {X : Type*}









/-- Across any cut of the distinctions into two parts, the side of a unit is the relation between a
reading of the first part and a reading of the second. -/
theorem reading_factors_across_cut (reads : D → X → Bool) (A : Set D) (p : Unt D) :
    ∃ fA fB : X → Bool,
      (∀ x y, (∀ d ∈ A, reads d x = reads d y) → fA x = fA y) ∧
      (∀ x y, (∀ d, d ∉ A → reads d x = reads d y) → fB x = fB y) ∧
      ∀ x, reading reads p x = (fA x != fB x) := by
  induction p with
  | base d =>
      by_cases hd : d ∈ A
      · refine ⟨reads d, fun _ => false, fun x y h => h d hd, fun _ _ _ => rfl, fun x => ?_⟩
        show reads d x = (reads d x != false)
        cases reads d x <;> rfl
      · refine ⟨fun _ => false, reads d, fun _ _ _ => rfl, fun x y h => h d hd, fun x => ?_⟩
        show reads d x = (false != reads d x)
        cases reads d x <;> rfl
  | rel p q ihp ihq =>
      obtain ⟨fA, fB, hA, hB, h⟩ := ihp
      obtain ⟨gA, gB, kA, kB, k⟩ := ihq
      refine ⟨fun x => fA x != gA x, fun x => fB x != gB x, ?_, ?_, ?_⟩
      · intro x y hxy
        show (fA x != gA x) = (fA y != gA y)
        rw [hA x y hxy, kA x y hxy]
      · intro x y hxy
        show (fB x != gB x) = (fB y != gB y)
        rw [hB x y hxy, kB x y hxy]
      · intro x
        show (reading reads p x != reading reads q x) = ((fA x != gA x) != (fB x != gB x))
        rw [h x, k x]
        cases fA x <;> cases fB x <;> cases gA x <;> cases gB x <;> rfl

end Unt



open Triangle in
/-- The parity record of pass 31 is the side record of a unit of level two. -/
theorem parity_is_side_of_level_two_unit (x : Corner → Bool) :
    Parity.odd () x ↔
      Unt.reading side (Unt.rel (Unt.rel (Unt.base Corner.a) (Unt.base Corner.b)) (Unt.base Corner.c))
        x = true :=
  Iff.rfl

open Triangle in
/-- The parity world meets the by-levels statement. -/
theorem parity_world_is_by_levels : ByLevels side Parity.odd ({()} : Finset Unit) := by
  intro r _
  refine ⟨Unt.rel (Unt.rel (Unt.base Corner.a) (Unt.base Corner.b)) (Unt.base Corner.c), ?_, true,
    fun x => Iff.rfl⟩
  simp [Unt.Separate, Unt.support]

end APFPaper1.RecordOccupant


theorem solution :
∀ (c : Bool),
  APFPaper1.RecordOccupant.IsRelation fun (a b : Bool) =>
    @Eq.{1} Bool (@bne.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) a b) c := by
  exact @APFPaper1.RecordOccupant.isRelation_of_same_or_opposite
