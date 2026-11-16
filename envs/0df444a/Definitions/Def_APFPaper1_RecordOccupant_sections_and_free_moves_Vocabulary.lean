-- Prove2me | Definitions.Def_APFPaper1_RecordOccupant_sections_and_free_moves_Vocabulary
-- name    : APFPaper1_RecordOccupant_sections_and_free_moves_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:45:24.563552+00:00
-- url     : https://prove2.me/theorems/7537a3a8-e891-4dcf-9236-bfbeb1f321a3
-- title:
--   Model vocabulary — Record-preserving flips and a classical triangle without a common section
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Record-preserving flips give NoSide on nonempty allowance. Every consistent single kept family, or collection kept together inside one consistent family, has a common point. A three-Boolean triangle of inequality records has consistent pairs but no common section. hkeep, hflip and nonemptiness are supplied. The triangle checks EveryCombinationHeld only, not all eight inputs or actual occupancy. It does not model quantum pairwise sharp compatibility or identify potential-state maps with record-algebra automorphisms. No physical no-section datum is proved.
--
--   **Supplied data and hypotheses**
--
--   - hkeep, hflip and nonemptiness are supplied. The triangle checks EveryCombinationHeld only, not all eight inputs or actual occupancy. It does not model quantum pairwise sharp compatibility or identify potential-state maps with record-algebra automorphisms. No physical no-section datum is proved.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper1_RecordOccupant_sections_and_free_moves; Sib v66 / pullbacks v22, SHA-256 15c7d42c40dac940ee5ce3dd02dcd64cee416799da1b6c7d07d24e311d818504. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper1_RecordOccupant_sections_and_free_moves.lean

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
import Definitions.Def_APFPaper1_RecordOccupant
import Definitions.Def_APFB02_EachTakesBothSides
import Mathlib.Data.Finset.Insert

namespace APFPaper1.RecordOccupant

variable {X D Rec : Type*}

/-! ### Moves that no kept record sees -/





/-! ### One potential state behind several record sets -/

/-- One potential state that every record of every family allows. -/
def HasSection {ι : Type*} (allows : Rec → X → Prop) (fam : ι → Finset Rec) : Prop :=
  ∃ x : X, ∀ i, x ∈ allowed allows (fam i)









/-! ### The triangle: any two relation records can be kept, and no potential state lies behind them -/

namespace Triangle

/-- Three distinctions; also the index of the three relation records. -/
inductive Corner
  | a | b | c
  deriving DecidableEq

/-- A potential state gives each of the three distinctions a side. -/
def side (d : Corner) (x : Corner → Bool) : Bool := x d

/-- Record `k` says: the two distinctions other than `k` are on different sides. -/
def differ : Corner → (Corner → Bool) → Prop
  | .a, x => x .b ≠ x .c
  | .b, x => x .c ≠ x .a
  | .c, x => x .a ≠ x .b

/-- The two relation records other than `k`. -/
def pair : Corner → Finset Corner
  | .a => {.b, .c}
  | .b => {.c, .a}
  | .c => {.a, .b}















end Triangle

end APFPaper1.RecordOccupant


