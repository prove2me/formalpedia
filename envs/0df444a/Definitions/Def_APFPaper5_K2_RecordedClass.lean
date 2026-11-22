-- Prove2me | Definitions.Def_APFPaper5_K2_RecordedClass
-- name    : APFPaper5_K2_RecordedClass
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:26:07.952376+00:00
-- url     : https://prove2.me/theorems/d979c046-fa11-4243-8286-32f629214bef
-- title:
--   Recorded classes as indicator functions of kept records
-- statement:
--   keptClass and partyClass are record indicator functions; recordForm is their weighted overlap and markLift sums listed record indicators. heldFamily selects the listed distinctions reading true, and recordedClass applies keptClass to that family. These six unchanged definitions are moved into their own source file. They do not describe unrecorded held states, derive a physical carrier, or prescribe actions of holds or tests.
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
--   Definitions.Def_APFPaper5_K2_RecordedClass; USB pullbacks v58 batch B, SHA-256 3164b8195ed4ef242c472f82fa66fddbf48a31ca44264eda30d6e49d4bd8da58. Definitions.Def_APFPaper5_K2_RecordedClass; USB pullbacks v58 batch B; SHA-256 3164b8195ed4ef242c472f82fa66fddbf48a31ca44264eda30d6e49d4bd8da58

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not built in the ledger repo, not built on the build machine)
name: APFPaper5_K2_RecordedClass
title: What is recorded of a state: the list of records its held family keeps, as a class of records, with the weighted overlap of two such classes
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 82d53cb50899f4e6722a196cef11a5ffd60e8eb7ca1d5cdcbe42f7de35e472e9), kept in Old/ as
 Def_APFPaper5_K2_RecordedClass_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED
 BYTES ARE NOT RELEASED.
 Changed in this header: the revision named on the inputs_revision line, which was 2026-11-14.1, and this
 entry. Nothing else.
 WHAT HAPPENED: since revision 2026-11-14.1, which this header named until now, five revisions of
 FOUNDATION_INPUTS were installed. Revision 2026-11-17.2, installed 2026-11-17 at 06:12 HST (sha256
 21e889b3b56b78cc571392fb652da60d22d81cbc79c7185ea6fed0f866fca65a;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-17): seven sentences were added to the end of B06's wording: the
 six quoted below as replaced at revision 2026-11-20.2, then "A process that keeps no record costs nothing."
 A reading of B02's first sentence and a guard on the declared Lean form of B07b were recorded. There is no
 installed revision 2026-11-16.1. Revision 2026-11-17.4, installed 2026-11-17 at 19:11 HST (sha256
 641cb7725112dc24168d4b5342e8ab94feb8f7cb8803ded1fbb8ac1daf6316c8;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-17.4_2026-11-17): two sentences were added to the end of B06: "A
 process that keeps no record changes nothing that is recorded. Every record a protocol keeps is the record
 of some tested distinction or family of tested distinctions, and is used for it." There is no installed
 revision 2026-11-17.3. Revision 2026-11-18.2, installed 2026-11-18 at 18:22 HST (sha256
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
 HOW TO READ THE REST OF THIS HEADER: it named revision 2026-11-14.1 and is left as written, any earlier
 entries "restated" below included. Where it names revision 2026-11-14.1 or an earlier one as the revision
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
 THIS FILE IS ONE OF THE NINETEEN RELEASED FOR THE SPINE PATH (K2's recorded side, 2026-11-17 05:52 HST:
 RELEASE_K2_recorded_side_for_the_spine_path_2026-11-17). That release was of the bytes then, which are the
 bytes kept in Old/ as named above. The bytes as restated here are not released. This entry restates the
 revision named and nothing more: the node header is set at the builder seat's intake, which is not made;
 the gate and the auditor's read are still to come, and the gate policy's "no stale-basis waiver" is theirs
 to meet.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 13:52 HST, "Seems like this is ok as it's about records which are not ever in
 superposition?", and 13:54 HST, "Yes" (RULING_C_for_what_is_recorded_2026-11-15): C for what is recorded;
 records are never in superposition; the unrecorded part is left to K3.
source: the author, 2026-11-17 03:12 HST: "then let's bolt k2 to spine" (RULING_K2s_recorded_side_goes_on_the_spine_2026-11-17).
 MOVED, NOT NEW. The six definitions below were typed on 2026-11-15. keptClass, partyClass, recordForm and
 markLift were in Def_APFPaper5_K2_StateClass (pre-cut sha256
 0b92addd71027347a462e16e4d2483c4b94b1a093fd8e39cf8c9315e79099b89, kept in Old/). heldFamily and recordedClass
 were in Thm_APFPaper5_K2_recorded_classes (pre-cut sha256
 7b838b50b1566bc7bd9006c2d2840d9424bf5e9bb2adceae18b87e8d3e911c2b, kept in Old/). Each is unchanged, character
 for character. They were moved so that the definition node of the recorded class does not carry the two
 candidates the author did not choose, and so that its definitions sit in a definition file.
 Paper 1 Supplement v9.28:1829-1843 (a structural alignment is a carrier and a finite family of
 distinctions each reading 1 on it; "what the substrate is actually holding"), 1852-1860 (its cost).
 The builder seat's Def_APFPaper5_K1_MarkTable (ind).
standing: DEFINITIONS, carrying the ruling of 2026-11-15 13:54 HST: for what is RECORDED, the class of a held
 family is the list of records it keeps. Nothing here is an input. What a state holds that is not
 recorded is not typed; it is left to K3.
definitions:
 - keptClass (C, ruled for what is recorded): on each record, 1 if the family keeps it and 0 if not. A class
   of records, not of distinctions.
 - partyClass: on each record, 1 if the distinction is listed against it and 0 if not.
 - recordForm: the weighted overlap of two classes of records.
 - markLift: the class of records a class of distinctions stands for: each distinction's list, added up.
 - heldFamily: among listed distinctions, those that read true on the state.
 - recordedClass: the list of records the held family keeps.
not claimed: anything about what a state holds that is not recorded; any action of a hold or a test on
 recorded classes. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed,
 or that Born is derived.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper5_K1_MarkTable

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uX uD uW
variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}

/-- C, ruled for what is recorded: the records a family keeps, as a class of records. -/
def keptClass (keeps : Finset D → W → Bool) (S : Finset D) : W → ℝ :=
  fun a => ind (keeps S a)

/-- The records a distinction is listed against, as a class of records. -/
def partyClass (mark : ι → W → Bool) (i : ι) : W → ℝ :=
  fun a => ind (mark i a)

/-- The weighted overlap of two classes of records. -/
def recordForm [Fintype W] (w : W → ℝ) (u v : W → ℝ) : ℝ :=
  ∑ a, w a * (u a * v a)

/-- The class of records a class of distinctions stands for. -/
def markLift [Fintype ι] (mark : ι → W → Bool) (x : ι → ℝ) : W → ℝ :=
  fun a => ∑ i, x i * ind (mark i a)

/-- The held family of a state: among the listed distinctions, those that read true on it. -/
def heldFamily (reads : D → X → Bool) (S : Finset D) (x : X) : Finset D :=
  S.filter (fun d => reads d x = true)

/-- What is recorded of a state: the list of records its held family keeps. -/
def recordedClass (keeps : Finset D → W → Bool) (reads : D → X → Bool) (S : Finset D) (x : X) :
    W → ℝ :=
  keptClass keeps (heldFamily reads S x)

end APFPaper5.K2


