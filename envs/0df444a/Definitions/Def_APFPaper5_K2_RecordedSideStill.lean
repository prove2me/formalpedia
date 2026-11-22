-- Prove2me | Definitions.Def_APFPaper5_K2_RecordedSideStill
-- name    : APFPaper5_K2_RecordedSideStill
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:35:43.83118+00:00
-- url     : https://prove2.me/theorems/9951b7ba-c6fb-451b-8acc-5bbad1ae7ebd
-- title:
--   Conditional preservation of recorded readings by record-free closed words
-- statement:
--   NoFreeGain forbids a listed false reading becoming true under a record-free closed word. RecordedSideStill requires every listed reading to be unchanged. ChangingARecordedSideCostsTheFloor separately requires a positive supplied floor and charges any closed execution changing a listed reading at least that floor. These distinct supplied predicates are candidate typings; no physical form is certified, and nonclosed words or unrecorded states are not covered.
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
--   Definitions.Def_APFPaper5_K2_RecordedSideStill; USB pullbacks v58 batch B, SHA-256 63fbda123154e2c9d44fac9712b73cc44f0ae76514887782f4afbffc68ca5d48. Definitions.Def_APFPaper5_K2_RecordedSideStill; USB pullbacks v58 batch B; SHA-256 63fbda123154e2c9d44fac9712b73cc44f0ae76514887782f4afbffc68ca5d48

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper5_K2_RecordedSideStill
title: The other half of pinning: no process that keeps no record turns a side from not held to held; with pinning, the recorded side is still; and the cost form, that changing a recorded side costs the floor
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 082a0314bc4672d1d5656b35a23c28771de214eb0bb06908fc290cb83ffe1c10), kept in Old/ as
 Def_APFPaper5_K2_RecordedSideStill_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE
 RESTATED BYTES ARE NOT RELEASED.
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
restated: 2026-11-17 20:13 HST, for bundle v52, at the author's word of 20:04 HST, "yes, thats perect", to this
 seat's question "Shall I push those two now and then build v52 with them aboard?"
 (RULING_push_the_two_then_build_v52_2026-11-17). HEADER ONLY. Every line after this comment is the file as
 in bundle v51 (sha256 8cf9adb4dcc0994fe35a2a086ce7ff83f1029718e079e3dd354766f3d3af7648), kept in Old/ as
 Def_APFPaper5_K2_RecordedSideStill_pre-restating_v52_2026-11-17.lean. No declaration is changed. THE
 RESTATED BYTES ARE NOT RELEASED.
 Changed in this header: the revision named on the inputs_revision line, and this entry. Nothing else.
 WHAT HAPPENED: FOUNDATION_INPUTS revision 2026-11-17.4 was installed on 2026-11-17 at 19:11 HST (sha256
 641cb7725112dc24168d4b5342e8ab94feb8f7cb8803ded1fbb8ac1daf6316c8;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-17.4_2026-11-17). Two sentences were added to the end of B06's
 current wording: "A process that keeps no record changes nothing that is recorded. Every record a protocol
 keeps is the record of some tested distinction or family of tested distinctions, and is used for it." It
 changes no other wording and no declared Lean form. There is no installed revision 2026-11-17.3.
 HOW TO READ THE REST OF THIS HEADER: it was written before that install and is left as written. Where it
 says of either of those two sentences, or of what this seat's drafts call a record pinning its side, no
 free gain, the still recorded side (HeldFamilyPinned, NoFreeGain, RecordedSideStill), or of the sentence
 that every record a protocol keeps is some tested distinction's and used for it, that it is proposed, a
 ruling carried as a named hypothesis, NOT RULED, not installed or not an input: that is no longer so. The
 sentence is in the inputs at revision 2026-11-17.4. In the second sentence joint records count, by the
 author's ruling of 18:25 HST; the typing the inputs file names for it, as proposed and NOT RULED, is the
 family reading of pass 113 (EveryRecordIsNeededForATestedFamily), not the typings of passes 110, 111 or
 112. NOTHING ELSE that this header calls a candidate, a reading, a ruling or a hypothesis was installed:
 "every word of a context is a process", "a protocol maintains what its fragments keep" and the bill as a
 sum are the author's rulings and not inputs; SufficientSupportIsUsed, the clause "within capacity", and
 this seat's two conditions (the empty set of records is sufficient for no distinction; a positive lower
 bound on the costs of single distinctions) are this seat's and not ruled. The new text has no declared Lean
 form; definition nodes are the builder seat's. So everything here stands as before, each theorem on its
 named hypotheses or on its supplied world, and the Lean forms this seat typed for the new text are
 candidates: the inputs file marks their fidelity as proposed, not certified. A supplied world that breaks
 either new sentence is not a world of the inputs at revision 2026-11-17.4, whatever this header says of an
 earlier revision.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-17 12:47 HST: "Let's push on a bit before we make the next bundle". Pass 108
 typed his ruling of 11:41 HST (RULING_a_record_pins_its_side_2026-11-17) as: a listed distinction that
 reads true still reads true after a closed word that keeps no record. That is enough for a hold, which
 has an admitted reverse. It says nothing of a word with no reverse that turns a side from false to true.
 This file names that half.
 Consulted before writing (2026-11-17, 12:49 to 12:51 HST):
 - Paper 1 Supplement v9.28: 1674-1676 (the per-realignment floor as a named hypothesis, P4), 7310 (C3:
   "you cannot almost-move something; either the substrate has paid the realignment cost or it has
   not"), with 1896-1929 as read for pass 107.
 - Paper 5 Supplement v7.33 (sandbox copy fetched through the Google Drive connector for pass 107):
   1426-1441 (the record functor "retains every distinction booked by the class transition and forgets
   held data that produce no committed record"; the closed-world kernel dichotomy), 1809-1823 (the
   global-phase kernel theorem), 3049-3057 (K3, whose last clause is common-phase record-nullity).
 - Codebank: apf/class_transition.py, check_T_coherent_free_spend_permanent ("free requires no
   completion with no drive"; "does not establish ... that an inverse is excluded").
 - The author's rulings: RULING_C_for_what_is_recorded_2026-11-15 ("The held family is the distinctions
   that read true; its class is the list of records that family keeps."); the ruling record of
   2026-11-16 on narrow ("It is charged on a way that makes a record."); his picture as recorded there,
   third row ("Making or releasing a record, a reading included", booked "At least epsilon, once.").
 - Existing Lean: Def_APFPaper5_K2_HeldFamilyPinned and Thm_APFPaper5_K2_no_hold_on_the_recorded_side
   (pass 108); Def_APFPaper1_NarrowFloorOnWords (pass 107); the released Def_APFPaper5_K2_RecordedClass.
standing: DEFINITIONS ONLY. NOT RULED. `NoFreeGain` is this seat's reading of how the author's rulings
 combine: by the ruling of 2026-11-15 a state holds the distinctions that read true, with their records;
 so a word after which a distinction newly reads true has made the state hold a record it did not hold;
 by the narrow floor that is charged; by "A process that keeps no record costs nothing" a word that
 keeps no record cannot do it. None of the three definitions is an input.
fidelity:
 (a) "Makes a record" has two typings on words, as "held" had in pass 107. By the word: its fragments
     keep a record. By the state: the state comes to hold a record it did not hold. In the supplied
     worlds a record fragment runs where its distinction already reads true and leaves the state; so
     there a word that keeps a record re-reads what the state already holds. `NoFreeGain` is the typing
     by the state.
 (b) `listed` is the list of distinctions of each context, as a finite set. It is supplied.
 (c) Closed words only, as in passes 107 and 108. Nothing is said of a mark on which the occupant is in
     raw form.
not_claimed: that either definition holds of the physical data; that the author means them. No lane. No
 claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
restated: 2026-11-17, for bundle v51. The author ruled at 13:09 HST: "i agree with no free gain"
 (RULING_no_free_gain_2026-11-17). So `NoFreeGain` is his ruling, and with his ruling of 11:41 HST that a
 record pins its side, `RecordedSideStill` stands under his rulings. Where this header says NOT RULED of
 either, read: ruled, carried as a named hypothesis, not an input. Nothing else in this header is changed.
 Every byte after this comment is the byte of the file as first written.
-/
import Definitions.Def_APFPaper5_K2_HeldFamilyPinned

set_option autoImplicit false
namespace APFPaper5.K2
open APFPaper1.Continuation APFPaper1.NarrowOnWords

universe uC uF uX uR uK uD
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
  {Dn : Context → Type uD}

/-- No free gain: no closed word that keeps no record, with keeping taken fragment by fragment, runs from
a raw possibility where a listed distinction reads false to one where it reads true. -/
def NoFreeGain (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g)) : Prop :=
  ∀ (g : Context) (W : Word Frag g g) (x y : Raw g) (d : Dn g),
    keptByFragments keptFrag g W = ∅ → Executes step W x y → d ∈ listed g →
      reads g d x = false → reads g d y = false

/-- The recorded side is still: no closed word that keeps no record changes how any listed distinction
reads. -/
def RecordedSideStill (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g)) : Prop :=
  ∀ (g : Context) (W : Word Frag g g) (x y : Raw g) (d : Dn g),
    keptByFragments keptFrag g W = ∅ → Executes step W x y → d ∈ listed g →
      reads g d y = reads g d x

/-- The cost form: the floor of each context is positive, and a closed word that changes how a listed
distinction reads bills at least the floor of its context. -/
def ChangingARecordedSideCostsTheFloor
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (eps : Context → NNReal) : Prop :=
  (∀ g, 0 < eps g) ∧
    ∀ (g : Context) (W : Word Frag g g) (x y : Raw g) (d : Dn g), Executes step W x y →
      d ∈ listed g → reads g d y ≠ reads g d x → eps g ≤ calibration g (resource g ⟨g, W⟩)

end APFPaper5.K2


