-- Prove2me | Definitions.Def_APFPaper1_DrawingIsKeeping
-- name    : APFPaper1_DrawingIsKeeping
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:26:08.126497+00:00
-- url     : https://prove2.me/theorems/239e042b-6cc8-4efc-a250-53192b9371d7
-- title:
--   Conditional protocol model: drawing, needed records and a uniform record bill
-- statement:
--   Definitions on supplied protocol data. KeepingDraws uses the records common to all protocols serving a family; EveryRecordIsDrawn requires each kept record to be needed by a nonempty tested family served by that protocol. DrawingIsKeeping additionally assumes a positive epsilon and an exact finite-record bill. These are candidate forms, not certified encodings of the current physical inputs. Protocol-independent need can be stronger than protocol-relative support in the Supplement. No claim about word execution or changes to recorded states follows from these definitions.
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
--   Definitions.Def_APFPaper1_DrawingIsKeeping; USB pullbacks v58 batch B, SHA-256 148f469868d20bbb97a319a2bb116907ba9c42dc770cc36bb73b1bc213d1c4f4. Definitions.Def_APFPaper1_DrawingIsKeeping; USB pullbacks v58 batch B; SHA-256 148f469868d20bbb97a319a2bb116907ba9c42dc770cc36bb73b1bc213d1c4f4

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper1_DrawingIsKeeping
title: A candidate single item for B06 beyond instantiation, typed on protocols: to draw a distinction is to keep its record, at epsilon
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 832139a31629694ea1f66da87a8dc6d0eb0ce2620f37bdcb6cd97111807df872), kept in Old/ as
 Def_APFPaper1_DrawingIsKeeping_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED
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
source: the author, 2026-11-17. 22:02 HST: "Occupancy reads like a bit of a kink drawer. Much of what's there
 should be. Derivation of something more primitive. I think we should dig in here- we can reduce occupancy
 to three items". 22:09 HST: "Can we reduce further? 1 would be best". 22:12 HST: "Yes, exactly", in answer
 to "Is \"to draw a distinction is to keep its record\" the primitive you have in mind?"
 (RULING_to_draw_a_distinction_is_to_keep_its_record_2026-11-17).
 Consulted before typing. Paper 1 Supplement v9.28: 1850 (a structural alignment is what the substrate is
 actually holding); 1873-1885 (occupancy, the explicit operational commitment); 1919 ("Holding a
 structural alignment costs nothing once it is instantiated; moving between two admissible alignments is
 what gets charged"); 2625 (the support assignment of a protocol maps each distinction to the set of
 maintained records the protocol uses to realize it: support is protocol-relative); 2628-2640 ("Minimizer
 nonuniqueness: two distinctions may share one record in one near-optimal protocol and use distinct
 records in another equally near-optimal protocol"); 3611-3613 (two discriminators read two digits of one
 maintained register: several distinctions may ride one record). Codebank: drawn_content_readings.py (a
 functional from banked representation content to readings; far downstream of records);
 occupant_cost_selection.py (an A2 selection, "does not derive the QAC"); nothing found that states the
 identification. Existing Lean: Def_APFPaper5_K1_SourcePartyScore (SourceServes, sourceNeeds);
 Def_APFPaper1_OccupantOf (IsOccupantOf); the typed candidates for B06's sentences 5 to 13.
standing: DEFINITIONS ONLY. A CANDIDATE. The author named the primitive in words; this typing of it is this
 seat's and is NOT RULED. Nothing here is an input, and nothing is proposed for the inputs by this file.
fidelity:
 (a) Typed on protocols, the source data of the declared forms: what a protocol maintains, what is
     sufficient, what it uses, what it bills. Nothing here speaks of words, steps or states. So B06's
     sentence 12 ("changes nothing that is recorded") is outside what this typing can reach.
 (b) "Its record" is typed through what a family NEEDS: the records every protocol that draws the family
     maintains (sourceNeeds). That makes the record of a distinction the same in every protocol. The
     Supplement lets support be protocol-relative (2625, 2628-2640). This typing is stronger than the
     Supplement there, and it fails in the two-ways world.
 (c) Several distinctions may need the same record (Supplement 3611-3613). Nothing here says a record
     belongs to one distinction only.
 (d) "At epsilon" is typed as: the bill of a protocol is epsilon for each record it maintains, and nothing
     else. That contains the bill as a sum, which the author kept out of the inputs on 2026-11-17 04:25
     HST.
not_claimed: that any of these holds of the physical data; that the author means this typing; that B06
 reduces to it. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed,
 or that Born is derived.
-/
import Definitions.Def_APFPaper5_K1_SourcePartyScore

set_option autoImplicit false

open APFPaper5.K1

namespace APFPaper1.Source

section
variable {D P R Record : Type*}
variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)

/-- To keep its record is to draw it: a protocol that maintains every record a family needs draws the
family. -/
def KeepingDraws : Prop :=
  ∀ (p : P) (S : Finset D), sourceNeeds maintained sufficient usesToRealize S ⊆ maintained p →
    SourceServes maintained sufficient usesToRealize p S

/-- Every record kept is the record of something drawn: it is needed by some nonempty family of tested
distinctions that the protocol draws. -/
def EveryRecordIsDrawn (tested : D → Prop) : Prop :=
  ∀ (p : P) (r : Record), r ∈ maintained p → ∃ S : Finset D, S.Nonempty ∧ (∀ d ∈ S, tested d) ∧
    SourceServes maintained sufficient usesToRealize p S ∧
    r ∈ sourceNeeds maintained sufficient usesToRealize S

/-- At epsilon: what a protocol maintains is a finite set of records, and its bill is epsilon for each of
them and nothing else. -/
def BillIsEpsilonPerRecord (kept : P → Finset Record) (eps : ℝ) : Prop :=
  (∀ p : P, maintained p = (↑(kept p) : Set Record)) ∧
    ∀ p : P, (calibration (wholeResource p) : ℝ) = eps * ((kept p).card : ℝ)

/-- The candidate: to draw a distinction is to keep its record, at epsilon. -/
def DrawingIsKeeping (tested : D → Prop) (kept : P → Finset Record) (eps : ℝ) : Prop :=
  KeepingDraws maintained sufficient usesToRealize ∧
    EveryRecordIsDrawn maintained sufficient usesToRealize tested ∧
    0 < eps ∧ BillIsEpsilonPerRecord wholeResource calibration maintained kept eps

end

end APFPaper1.Source


