-- Prove2me | Definitions.Def_APFPaper1_DrawsExactly
-- name    : APFPaper1_DrawsExactly
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:27:23.789808+00:00
-- url     : https://prove2.me/theorems/905fd509-0d63-4728-b2f6-251c0d919f2a
-- title:
--   Exact tested families and availability of their parts
-- statement:
--   DrawsExactly requires serving every member of a supplied finite family and serving no tested distinction outside it. It does not exclude untested distinctions. EveryPartDrawnAlone is an additional protocol-existence condition for every subset, including the empty subset. Neither existence nor physical realization is supplied by this definition.
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
--   Definitions.Def_APFPaper1_DrawsExactly; USB pullbacks v58 batch B, SHA-256 ce5e6cb684dad4faf6497858b94510d62d2d87fef36306f25176681d87236d7f. Definitions.Def_APFPaper1_DrawsExactly; USB pullbacks v58 batch B; SHA-256 ce5e6cb684dad4faf6497858b94510d62d2d87fef36306f25176681d87236d7f

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-18; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper1_DrawsExactly
title: A protocol draws exactly a family; every part of a family can be drawn alone
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 3c2fcfc78c9781be1478086d1ff4ac62ff3af6245c136d54792080927b25a533), kept in Old/ as
 Def_APFPaper1_DrawsExactly_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED BYTES
 ARE NOT RELEASED.
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
source: the dig into B06 the author asked for on 2026-11-17
 (RULING_to_draw_a_distinction_is_to_keep_its_record_2026-11-17), with his rulings of 2026-11-18 05:29 and
 05:48 HST. B06's sentence 2 ("let S be its entire nonempty carried family") and sentences 7, 8 and 10.
 Consulted before typing: FOUNDATION_INPUTS revision 2026-11-17.4, B06's thirteen sentences as installed;
 RULING_occupant_and_its_parts_2026-11-15 and Thm_APFPaper1_occupant_and_its_parts (every nonempty part
 of what the occupant holds is held exactly by some protocol: the typed form of sentence 8 on file);
 Def_APFPaper1_OccupantOf (EveryFamilyOccupied, the availability sentence, an adopted reading in its scoped
 wording, 2026-11-14 17:29 HST); Paper 1 Supplement v9.28:1850 (a structural alignment is what the substrate
 is actually holding); the author's usage, on record: "The occupant is everything".
standing: DEFINITIONS ONLY. Candidates of this seat, NOT RULED. Nothing here is an input, and nothing is
 proposed for the inputs by this file.
fidelity:
 (a) "Draws exactly" says two things of a protocol and a family: it draws every member, and every tested
     distinction it draws is a member. The second is this seat's reading of "entire carried family". The
     installed sentence says it of the alignment; whether the protocol of sentence 3 draws nothing else is
     not said there.
 (b) "Every part can be drawn alone" is an existence claim about which protocols there are, like
     instantiation. It is stronger than the form of sentence 8 on file (some protocol keeps exactly what
     the part needs): a protocol may keep exactly what a part needs and still draw a distinction outside
     the part, where that distinction rides the same records (Supplement v9.28:3612).
 (c) The empty part is included: some protocol draws no tested distinction.
not_claimed: that either holds of the physical data. No lane. No claim that the transfer is forced, that
 the carrier gap is closed or narrowed, or that Born is derived.
-/
import Definitions.Def_APFPaper1_OneRecordEach

set_option autoImplicit false

open APFPaper5.K1

namespace APFPaper1.Source

section
variable {D P Record : Type*}
variable (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)

/-- A protocol draws exactly a family, among the tested distinctions: it draws every member, and every
tested distinction it draws is a member. -/
def DrawsExactly (tested : D → Prop) (p : P) (S : Finset D) : Prop :=
  SourceServes maintained sufficient usesToRealize p S ∧
    ∀ d : D, tested d →
      (∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) → d ∈ S

/-- Every part of a family, the empty part included, can be drawn alone: some protocol draws exactly
it. -/
def EveryPartDrawnAlone (tested : D → Prop) (S0 : Finset D) : Prop :=
  ∀ S : Finset D, S ⊆ S0 →
    ∃ q : P, DrawsExactly maintained sufficient usesToRealize tested q S

end

end APFPaper1.Source


