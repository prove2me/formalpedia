-- Prove2me | Definitions.Def_APFPaper1_RecordOccupant_units_and_levels_Vocabulary
-- name    : APFPaper1_RecordOccupant_units_and_levels_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:29:14.595507+00:00
-- url     : https://prove2.me/theorems/11159880-4ce1-45cc-970e-d17acb018dfb
-- title:
--   Model vocabulary — Boolean relations and recursively built units
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   IsRelation exposes three ordinary Boolean conditions: common-complement invariance, settling neither argument, and excluding at least one pair. They imply same/opposite sides and are proved for those examples. Unt builds XOR units recursively; ByLevels is an explicit, uninstalled predicate. Its parity witness and reading factorization do not establish physical K4.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper1_RecordOccupant_units_and_levels; Pullbacks v39, SHA-256 99fc6f50960d16a10761a351e4333cc422a25416f40f0b28c85d41319deb04c1. Theorems.Thm_APFPaper1_RecordOccupant_units_and_levels; pullbacks v39; SHA-256 99fc6f50960d16a10761a351e4333cc422a25416f40f0b28c85d41319deb04c1

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

/-- Candidate B for two-sided units. `f a b` says whether the record allows the first unit on side `a`
with the second on side `b`. -/
structure IsRelation (f : Bool → Bool → Prop) : Prop where
  unchanged_by_common_turn : ∀ a b, f a b ↔ f (!a) (!b)
  settles_neither : (∃ b, f true b) ∧ (∃ b, f false b) ∧ (∃ a, f a true) ∧ (∃ a, f a false)
  says_something : ∃ a b, ¬ f a b





/-- A unit: a distinction, or the relation between two units. -/
inductive Unt (D : Type u) : Type u
  | base : D → Unt D
  | rel : Unt D → Unt D → Unt D

namespace Unt

variable {D : Type u} {X : Type*}

/-- The side a unit is on. For a distinction, its own side. For a relation, whether its two units are on
opposite sides. -/
def reading (reads : D → X → Bool) : Unt D → X → Bool
  | base d, x => reads d x
  | rel p q, x => reading reads p x != reading reads q x

/-- The distinctions a unit is built from. -/
def support [DecidableEq D] : Unt D → Finset D
  | base d => {d}
  | rel p q => support p ∪ support q

/-- Candidate C: every relation inside the unit is between two units that share no distinction. -/
def Separate [DecidableEq D] : Unt D → Prop
  | base _ => True
  | rel p q => Separate p ∧ Separate q ∧ Disjoint (support p) (support q)

/-- The level of a unit: a distinction is at level 0; a relation is one above its higher unit. -/
def level : Unt D → ℕ
  | base _ => 0
  | rel p q => max (level p) (level q) + 1



end Unt

/-- The author's statement, by levels, for two-sided marks: every kept record says which side some unit
is on, the unit being built by relating separate units. -/
def ByLevels {D : Type u} {X Rec : Type*} [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) : Prop :=
  ∀ r ∈ K, ∃ p : Unt D, p.Separate ∧ ∃ c : Bool, ∀ x, allows r x ↔ Unt.reading reads p x = c





end APFPaper1.RecordOccupant


