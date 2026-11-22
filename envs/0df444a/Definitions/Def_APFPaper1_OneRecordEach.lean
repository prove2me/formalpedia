-- Prove2me | Definitions.Def_APFPaper1_OneRecordEach
-- name    : APFPaper1_OneRecordEach
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:26:48.578826+00:00
-- url     : https://prove2.me/theorems/85cd085a-278e-4770-b902-54c6f76cdcff
-- title:
--   Conditional protocol model: a fixed record set for each distinction
-- statement:
--   OneRecordEach asserts the existence of a protocol-independent SET of records for each distinction, with serving equivalent to keeping that set. It does not require a singleton record set or a unique assignment. DrawingCarries separately names monotonicity under inclusion of maintained records. These are supplied predicates; no physical fidelity or Foundation adoption is certified.
--
--   **Supplied data and hypotheses**
--
--   - Every formal parameter and hypothesis remains exposed. Historical model encodings and named conditions are not adopted as current physical inputs.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper1_OneRecordEach; USB pullbacks v58 batch B, SHA-256 7c12557c75d3cab5cf9b109d92408992e4aa6d9d40356353fc47cfe2e5e2c8ee. Definitions.Def_APFPaper1_OneRecordEach; USB pullbacks v58 batch B; SHA-256 7c12557c75d3cab5cf9b109d92408992e4aa6d9d40356353fc47cfe2e5e2c8ee

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-18; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper1_OneRecordEach
title: A distinction is recorded one way, typed on protocols: each distinction has one record, and a protocol draws the distinction exactly when it maintains that record
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 8426d1e7c96168bfe45b041d9e203dfa929d2110be7b1969b90a7cd366896216), kept in Old/ as
 Def_APFPaper1_OneRecordEach_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED
 BYTES ARE NOT RELEASED.
 Changed in this header: the revision named on the inputs_revision line, which was 2026-11-17.4, and this
 entry. Nothing else.
 WHAT HAPPENED: since revision 2026-11-17.4, which this header named until now, three revisions of
 FOUNDATION_INPUTS were installed. Revision 2026-11-18.2, installed 2026-11-18 at 18:22 HST (sha256
 290a59cad5591706d9b929fc98dde9f1b1215b4e40dc3d8eff790e8c59090cf0;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-18.2_2026-11-18): the reading of B02's first sentence
 (reading_20261114_list_complete) is scoped to what is recorded. It now reads: "The distinctions of a
 context are complete for what is recorded: potential states that every distinction of the context reads
 alike are recorded alike. They may differ in what they hold unrecorded. Then what can follow them tells
 them apart, and no side does." It is a reading and not a commitment; B02's two sentences are unchanged.
 Revision 2026-11-18.3, installed 2026-11-18 at 19:50 HST (sha256
 95815d3a9ef01dd631bd52729a66a79531ff4590ed44d451be5882af20cc35b2;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-18.3_and_GATE_POLICY_2026-11-18.inputs.2_2026-11-18): one block
 was added that records where 13 cited files now resolve. No wording of a commitment changed. Revision
 2026-11-20.2, installed 2026-11-20 at 12:36 HST (sha256
 05c831bf6e786f168d9a9f0bb366b496388bd049960e9df3ca0acad8680d6252;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-20.2_2026-11-20): B06 is reduced. After its first four sentences,
 which are unchanged, it now reads: "To draw a distinction is to keep its record: each distinction has one
 record, the same in every protocol, and a protocol draws the distinction exactly when it keeps that record.
 Every record a protocol keeps is the record of some tested distinction or family of tested distinctions,
 and is used for it. Every process pays epsilon for each record it keeps, and nothing else, where epsilon is
 positive and fixed by the context. In every context some protocol draws no distinction. The occupant draws
 exactly its family, and every part of that family is drawn alone by some protocol. A process that keeps no
 record costs nothing. A process that keeps no record changes nothing that is recorded." Against revision
 2026-11-18.3, six sentences are replaced by four and three are kept word for word. The six that are no
 longer sentences of the inputs: "Each record carries a cost. What a set of records is sufficient for does
 not depend on the protocol that keeps it. The occupant holds its distinctions with exactly the records they
 need, and its bill is the cost of those records. The same is true of every part of it: any family of its
 distinctions is held with exactly the records that family needs, at exactly their cost, and there is no
 cheaper way to hold that family. Epsilon is the unit of the occupant: each record it keeps costs epsilon,
 the floor of its context. Holding nothing costs nothing." B03 and B05 are retired as inputs and are kept in
 the inputs file as derived statements. B07a and B07b each gain a note, note_20261120_protocol_binding;
 their wording, scope and forms are unchanged. B01, B02 and B04 are unchanged. The commitments are six: B01,
 B02, B04, B06, B07a, B07b. The gate policy on the build machine is policy_revision 2026-11-20.inputs.1
 (sha256 5e9f3ec3cfa6c9a0a0b28549d13370c31ef78de38272ac6391efeac472f9a4aa) and requires this revision
 (INSTALL_RECEIPT_GATE_POLICY_2026-11-20.inputs.1_2026-11-20).
 HOW TO READ THE REST OF THIS HEADER: it named revision 2026-11-17.4 and is left as written, any earlier
 entries "restated" below included. Where it names revision 2026-11-17.4 or an earlier one as the revision
 in force, that is no longer so: the revision in force is 2026-11-20.2. Where it counts eight commitments,
 eight inputs or eight declared forms: there are now six commitments. The declared forms of B03 and B05 are
 unchanged and are now forms of derived statements. Where it calls B03 or B05 an input, or takes the
 declared form of either as a hypothesis: the installed file says of B03, and in the same words of B05, "A
 dependency on B03 is a dependency on its declared form, which is unchanged. From revision 2026-11-20.2 that
 form is a derived statement and not an input. The derivation is a draft and is not certified: until it is
 admitted through the gate, a node that consumes B03 is conditional on it. Resolve it before foundation
 certification. Do not treat an old use of B03 as a use of B06." Where it speaks of B06 by a count of its
 sentences or by their numbers, of the occupant statement, of the amended B06, or of a sentence of B06 as an
 input: that is B06 as it stood at the revision the header then named, and B06 now reads as quoted above. A
 statement here that takes one of the six replaced sentences as a premise stays true as a conditional;
 whether it follows from the reduced B06 is NOT SAID by this entry (for what used them see
 MEMO_pullbacks_passes119_and_120_what_used_the_dropped_sentences_and_one_world_for_all_eleven_2026-11-18 in
 Notes). Where it says of a sentence that is in B06 as quoted above that it is proposed, a ruling carried as
 a named hypothesis, NOT RULED, not installed or not an input: that is no longer so, for that sentence as
 worded above and for no typing of it. Where it takes the reading of B02's first sentence as first recorded
 (the distinctions of a context are complete: potential states that every distinction reads alike have the
 same continuation profile; the physical objects of a context correspond one to one with the combinations of
 sides of its distinctions) as a reading of the inputs: from revision 2026-11-18.2 the inputs do not assert
 it. A statement that takes it as a premise stays true as a conditional. A supplied world in which it holds
 is not excluded: the scoped reading adds no constraint. THE NEW SENTENCES OF B06 HAVE NO CERTIFIED LEAN
 FORM: the forms the inputs file names for the reduced B06 are drafts of the two seats, marked
 PROPOSED_NOT_CERTIFIED, and the Lean that derives the declared forms of B03 and B05 is a draft and is not
 gated. NOTHING in this entry says that a theorem of this file follows from the inputs at revision
 2026-11-20.2, or that a supplied world of this file is a world of them: each theorem stands as before, on
 its named hypotheses or on its supplied world, and a supplied world that breaks a sentence of the inputs at
 revision 2026-11-20.2 is not a world of the inputs at that revision, whatever this header says of an
 earlier one. The gate policy says of the move to this revision: "immutable; dependency compatibility must
 be established separately; no stale-basis waiver". This entry establishes no such compatibility. Proposed
 revision 2026-11-20.3 (one further note on each of B07a and B07b) is NOT installed.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-18 05:29 HST: "No", in answer to "May a distinction be recorded two different
 ways, yes or no?" (RULING_a_distinction_is_recorded_one_way_2026-11-18). With his word of 2026-11-17
 22:12 HST that the primitive he has in mind for occupancy is "to draw a distinction is to keep its
 record" (RULING_to_draw_a_distinction_is_to_keep_its_record_2026-11-17).
 Consulted before typing. Paper 1 Supplement v9.28: 2612-2618 (a shared record makes the interface term
 negative); 2625 (the support assignment of a protocol: support is protocol-relative); 2628-2640 (the three
 obstructions, minimizer nonuniqueness among them: the Supplement allows what the ruling excludes);
 2845-2866 and 2868 (chain rank and its floor, built to survive it); 2955-2997 (the worked overcharge: a
 record priced at zero, each distinction with one way); 3612 (two discriminators on one register); 1969-1975
 and 6043 (a case study that bills trials as well as records). Codebank: plec.py (regime exit Type II,
 minimizer nonuniqueness, a branching statement far from records); kappa_int_bounds.py (states the
 v9.24 marginal-floor results as needing support-novel, support-independent families); nothing found
 that states one record for each distinction. Existing Lean: Def_APFPaper5_K1_RecordModel (the builder
 seat's record model, in which each distinction has a finite set of records and a set is sufficient when
 it contains it); Thm_APFPaper5_K1_interface_bridge (hneed, "serving a distinction needs that
 distinction's own records", an adopted reading of 2026-11-14 16:45 HST); Thm_APFPaper5_K1_counted_from_
 the_occupant_statement (SufficiencyCarries, this seat's typing of B06's sentence 6);
 Def_APFPaper1_DrawingIsKeeping (KeepingDraws, pass 115).
standing: DEFINITIONS ONLY. The ruling is the author's; this typing of it is this seat's and is NOT RULED.
 Nothing here is an input, and nothing is proposed for the inputs by this file.
fidelity:
 (a) "Its record" is a set of records, one for each distinction, the same in every protocol. The typing
     asserts that such an assignment exists. It does not name it and does not say it is unique.
 (b) "Draws" is the serving clause of the declared family cost: the protocol maintains a set of records
     sufficient for the distinction and uses it.
 (c) The typing joins two things: the record is one (the ruling of 05:29 HST), and to keep it is to draw
     the distinction (the other direction of the primitive). The second is B06's sentence 6 as far as
     drawing goes.
 (d) Nothing is said of a family beyond its members: a protocol draws a family when it draws each member.
     A record that only a pair needs (a joint record) is not excluded; it shows in what the protocols that
     draw the pair maintain, as in the residue world.
not_claimed: that this holds of the physical data; that the author means this typing; that B06 reduces
 to it. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
-/
import Definitions.Def_APFPaper1_DrawingIsKeeping

set_option autoImplicit false

namespace APFPaper1.Source

section
variable {D P Record : Type*}
variable (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)

/-- A distinction is recorded one way: each distinction has one record, a set of records that is the
same in every protocol, and a protocol draws the distinction exactly when it maintains that record. -/
def OneRecordEach : Prop :=
  ∃ recordOf : D → Set Record, ∀ (p : P) (d : D),
    (∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ↔
      recordOf d ⊆ maintained p

/-- What a protocol draws is its records' own: a distinction drawn by a protocol is drawn by every
protocol that maintains at least the same records. -/
def DrawingCarries : Prop :=
  ∀ (p q : P) (d : D), maintained p ⊆ maintained q →
    (∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) →
    ∃ tau : Set Record, tau ⊆ maintained q ∧ sufficient q tau d ∧ usesToRealize q d tau

end

end APFPaper1.Source


