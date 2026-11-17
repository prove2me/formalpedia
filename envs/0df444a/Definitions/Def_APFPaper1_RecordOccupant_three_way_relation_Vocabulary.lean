-- Prove2me | Definitions.Def_APFPaper1_RecordOccupant_three_way_relation_Vocabulary
-- name    : APFPaper1_RecordOccupant_three_way_relation_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:20:22.932969+00:00
-- url     : https://prove2.me/theorems/cbcb55e2-f602-496c-9a56-f7d64f49cee4
-- title:
--   Model vocabulary — A three-bit parity record
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The supplied parity example has raw individual sides and unsettled pair relations but a fixed triple parity. It checks EveryCombinationHeld, not all eight declared forms. Raw means no recorded side, not superposition.
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
--   Theorems.Thm_APFPaper1_RecordOccupant_three_way_relation; Pullbacks v39, SHA-256 c28267bf7a82e83c0ef24d6f35d735854c20bf478aa5668a3e83b13f67054660. Theorems.Thm_APFPaper1_RecordOccupant_three_way_relation; pullbacks v39; SHA-256 c28267bf7a82e83c0ef24d6f35d735854c20bf478aa5668a3e83b13f67054660

import Definitions.Def_APFPaper1_RecordOccupant
import Definitions.Def_APFB02_EachTakesBothSides
import Mathlib.Data.Finset.Insert
import Definitions.Def_APFPaper1_RecordOccupant_sections_and_free_moves_Vocabulary
import Theorems.Thm_APFPaper1_RecordOccupant_Triangle_three_cannot_be_kept
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_sections_and_free_moves
title: A move that no kept record sees and that flips a distinction leaves the occupant in raw form on it; record sets that can be kept together always have one potential state behind them; three relation records of which any two can be kept have none
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST 19:09: "Let's look to gauge to learn more about the occupant".
 RULING_occupant_forms_2026-11-14 (record form / raw form). Def_APFPaper1_RecordOccupant (this seat).
 Paper 12 v1.8 (The Gauge Sector of Admissibility Physics): lines 352-376 (an interface either admits "a
 global Boolean section" or does not; "the occupant" is the declared datum that it somewhere does not; the
 profile is read off the record and "never derived"); 564-566 (a register is "protected" when its cells
 "cannot be erased or overwritten by the substrate's free relabelings"); 2279-2334 (Step 2: a relabeling
 "that preserves every tested expectation is a free convention at zero marginal cost", the relabel-freedom
 clause, "adopted and named"; the gauge group is the group of such relabelings).
 Codebank: apf/core.py check_T_alg (the route from a joint surplus to a noncommutative record algebra is
 tagged [P+IJC]: it needs the no-section premise stated explicitly; the abstract route "does NOT logically
 go through"); apf/gauge.py check_Theorem_R, R1(e) (a zero-cost exchange makes a distinction "not robust");
 apf/gauge_quotient_ledger.py (GQL-1, a named identification, not banked: no enforceable separator pins a
 gauge-orbit position); apf/gauge_invariant_record.py (reading grade: the only sharp gauge-invariant colour
 record is the relation, not a member's side); apf/aboutness_occupancy_section.py.
standing: GENERAL LEMMAS AND ONE WORLD. Nothing here is a reading and nothing here is adopted.
what this file says:
 1. noSide_of_record_keeping_flip, no_record_keeping_flip_of_hasSide. A move of potential states that keeps
    every kept record, and flips the reading of a distinction, exists only where the occupant is in raw form
    on that distinction. In record form no such move exists. This is Paper 12's "protected" said in the
    occupant vocabulary: the free relabelings act only inside raw form.
 2. hasSection_of_one_family, hasSection_of_noSide, hasSection_of_kept_together. Raw form as typed in
    Def_APFPaper1_RecordOccupant always has a potential state behind it. More generally any record families
    that can all be kept together have one. So the definition, on one kept record set, cannot tell an
    occupant with no side from an occupant whose side is not recorded. To say "no side" in Paper 12's sense
    one needs record families that cannot all be kept together.
 3. Triangle. Three distinctions, three relation records ("these two differ"). Any two records can be kept;
    in every such pair each distinction is in raw form; the kept pair settles the third relation as "the
    same"; the three cannot be kept together; no potential state lies behind the three pairs. B02's second
    sentence (APFB02.EveryCombinationHeld) holds in this world.
what this file does NOT say:
 - That nature realizes the Triangle. It is the smallest logical world with no section. In quantum theory
   sharp tests that are pairwise compatible are jointly compatible, so this triangle does not occur there.
 - That an occupant shows both records of whichever pair is kept. That is a statement about what is
   realized in each kept set (Paper 12's "profile"), and it is what would make the Triangle an occupant
   with no side rather than three records that are never all true. It is not typed here.
 - That the eight inputs force a world with no section, or exclude one. Neither is shown.
 - Anything about a number, a carrier, a transfer or Born. No lane. No claim that the transfer is forced,
   that the carrier gap is closed or narrowed, or that Born is derived.
 - That "keeps every kept record" is the same as Paper 12's "preserves every tested expectation". Here a
   move is a map of potential states; there it is an automorphism of the record algebra.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/




namespace APFPaper1.RecordOccupant

variable {X D Rec : Type*}

/-! ### Moves that no kept record sees -/





/-! ### One potential state behind several record sets -/











/-! ### The triangle: any two relation records can be kept, and no potential state lies behind them -/

namespace Triangle









/-- B02's second sentence holds: every combination of sides is held by some potential state. -/
theorem every_combination_held : APFB02.EveryCombinationHeld side :=
  fun _ v => ⟨v, fun _ _ => rfl⟩













end Triangle

end APFPaper1.RecordOccupant

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



set_option autoImplicit false

namespace APFPaper1.RecordOccupant.Parity

open Triangle

/-- The one record: an odd number of the three distinctions are on the true side. -/
def odd (_ : Unit) (x : Corner → Bool) : Prop := ((x .a != x .b) != x .c) = true

/-- The state with only `k` on the true side. -/
def only : Corner → Corner → Bool
  | .a, .a => true
  | .b, .b => true
  | .c, .c => true
  | _, _ => false

/-- The state with all three on the true side. -/
def allTrue : Corner → Bool := fun _ => true



















end APFPaper1.RecordOccupant.Parity


