-- Prove2me | Definitions.Def_APFPaper1_RecordOccupant
-- name    : APFPaper1_RecordOccupant
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:41:35.293252+00:00
-- url     : https://prove2.me/theorems/18067958-d3fd-4e5b-9968-a904a5e6d37e
-- title:
--   Allowed potential states and record-determined sides
-- statement:
--   Defines allowed states as those satisfying every kept record; HasSide requires nonempty allowance and one fixed Boolean value; NoSide requires allowed states of both values; SpeaksOnlyOf expresses dependence on a finite family. The adopted raw/record-form interpretation is distinct from what these classical set predicates prove. It is not identified with the older OccupantBinding raw state. NoSide mathematically means not fixed by records, not a quantum superposition; no declared input changes.
--
--   **Supplied data and hypotheses**
--
--   - The adopted raw/record-form interpretation is distinct from what these classical set predicates prove. It is not identified with the older OccupantBinding raw state. NoSide mathematically means not fixed by records, not a quantum superposition; no declared input changes.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper1_RecordOccupant; Sib v66 / pullbacks v22, SHA-256 37388b56568bcc901a93814d30b1322d76887ae76a0078ff4271edefea7eaa3e. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFPaper1_RecordOccupant.lean

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant
title: The occupant's two forms on a distinction: record form, where the records it keeps give it a side, and raw form, where they give it none
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST: 18:31 "I think what is realized has no side - this is the superposition
 part of the occupant?"; 18:36 "The occupant can be in superposition or it can be in a fixed alignment that
 is associated with a record?"; 18:37 "This feels right - let's formalize and explore implications".
 FOUNDATION_INPUTS B02 (a distinction is a two-valued separator; every combination of sides is held by some
 potential state). Thm_APFB07b_no_side_without_a_record (this seat, pass 21). The archive's
 APFLoFStrengthening.recorded_coordinate_iff (read as a statement): recoverable exactly when recorded.
 Existing typing this departs from: Def_APFB07a_OccupantBinding (seat 01WrrBvu) takes an occupant to be a
 raw state, which has a side on every distinction.
standing: an ADOPTED READING. The author, 2026-11-14 HST: 18:55 "occupant can be in record form or in raw
 form- raw is superposition?"; asked at 18:57 whether, on a distinction with no record, the occupant itself
 has no side, as opposed to having one that is not recorded: "Yes". So HasSide is the occupant in RECORD
 FORM on d, and NoSide is the occupant in RAW FORM on d. The fully specified points X are B02's "potential
 states"; where the occupant is raw it is not one of them. This departs from Def_APFB07a_OccupantBinding
 (seat 01WrrBvu), which takes the occupant to be such a point and calls it a raw state; that difference is
 not settled, and the two uses of "raw" are opposite. The header of this file in bundle v18 said the
 occupant has every side; that was this seat's misreading of 18:46 HST and is withdrawn. No declared input
 is changed.
statement: allowed allows K is the set of potential states that every record in K allows. HasSide reads
 allows K d b says some potential state is allowed and every allowed one reads d as b. NoSide reads allows K
 d says an allowed state reads d one way and an allowed state reads it the other. SpeaksOnlyOf reads allows
 K S says that whether a record of K allows a state depends only on that state's sides on the family S.
not_claimed: that the occupant is nothing but its records; that what a record allows is physical; that "no side" is
 anything more than "not fixed by the records" without B07b (see Thm_APFB07b_no_side_without_a_record).
 No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
 derived.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

set_option autoImplicit false
namespace APFPaper1.RecordOccupant

variable {X D Rec : Type*}

/-- The potential states that every kept record allows. -/
def allowed (allows : Rec → X → Prop) (K : Finset Rec) : Set X :=
  {x | ∀ r ∈ K, allows r x}

/-- Record form: the occupant keeping `K` has side `b` on `d`. Some potential state is allowed, and
every allowed one reads `d` as `b`. -/
def HasSide (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec) (d : D)
    (b : Bool) : Prop :=
  (allowed allows K).Nonempty ∧ ∀ x ∈ allowed allows K, reads d x = b

/-- Raw form: the occupant keeping `K` has no side on `d`. Allowed potential states read it both
ways. -/
def NoSide (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec) (d : D) : Prop :=
  (∃ x ∈ allowed allows K, reads d x = true) ∧ (∃ y ∈ allowed allows K, reads d y = false)

/-- Whether a record of `K` allows a state depends only on that state's sides on the family `S`. -/
def SpeaksOnlyOf (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec)
    (S : Finset D) : Prop :=
  ∀ r ∈ K, ∀ x y : X, (∀ e ∈ S, reads e x = reads e y) → allows r x → allows r y

end APFPaper1.RecordOccupant


