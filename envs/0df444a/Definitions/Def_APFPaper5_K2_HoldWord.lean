-- Prove2me | Definitions.Def_APFPaper5_K2_HoldWord
-- name    : APFPaper5_K2_HoldWord
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:26:53.705036+00:00
-- url     : https://prove2.me/theorems/92facaf7-cf58-4cfe-a7a8-69e44eb87e81
-- title:
--   Admitted record-free hold words with record-free inverse words
-- statement:
--   Definitions use supplied admission, execution and keeping relations. A hold word is admitted at every raw possibility, executes as a map satisfying IsHold, keeps no record, and has an everywhere-admitted record-free word executing a two-sided inverse map. These universal admission and inverse conditions are explicit premises. No nonempty physical hold or zero bill is established.
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
--   Definitions.Def_APFPaper5_K2_HoldWord; USB pullbacks v58 batch B, SHA-256 4d6f7c93c7839946996d0f62d29faf05350ca96a1c7531a98916f4d2ef6eaabf. Definitions.Def_APFPaper5_K2_HoldWord; USB pullbacks v58 batch B; SHA-256 4d6f7c93c7839946996d0f62d29faf05350ca96a1c7531a98916f4d2ef6eaabf

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not bundled, not built in the ledger repo, not built on the build
 machine)
name: APFPaper5_K2_HoldWord
title: A hold, in the K layer: a closed word of the foundation's words that is admitted, runs as a hold as defined, keeps no record, and has an admitted reverse
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 9ad956c087b6b50bf4c30ec73ff7e2c329334ee5dec13dc1bc01ed920a468f0c), kept in Old/ as
 Def_APFPaper5_K2_HoldWord_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED BYTES
 ARE NOT RELEASED.
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
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
revision of this file: SECOND. The first, of pass 95, typed the ruling of 18:54 HST alone and is kept as
 Old/Def_APFPaper5_K2_HoldWord_pass95_pre-ruling-1924_2026-11-16.lean. Its IsHoldWord is RunsAsHoldAdmitted
 here, unchanged. This file governs.
rulings: the author, 2026-11-16.
 18:54 HST, "Yes": no third clause on the definition of a hold; "a hold" in K-layer claims means an
 admitted word that runs as one (RULING_no_third_clause_a_hold_is_an_admitted_word_that_runs_as_one_2026-11-16).
 19:24 HST, "Should a hold in the K layer also have to keep no record and have an admitted reverse, as
 Paper 5 asks? Yes" (RULING_a_hold_keeps_no_record_and_has_an_admitted_reverse_2026-11-16).
source: Paper 5 Supplement v7.33:396-440 (the process in the channel and its reverse are admissible
 represented processes); 628-637 (physical reversal is load bearing for the reversible record-free
 coherent loops of Q4); 1656 (the reverses of coherent loops "are admitted in the same record-free
 component"); 1660-1684 and 1950-1962 (reversal is the inverse; reversal admitted without
 reversal-as-inverse gives a monoid and not a loop group). Def_APFPaper5_K2_Hold (IsHold);
 Def_APFPaper5_K2_HoldScore (ExecutesAs); Def_APFPaper5_K2_ClosedBoundary (when a word is defined is
 SUPPLIED there; the canonical choice is Cont); the builder seat's Def_APFPaper1_ContinuationWords.
standing: DEFINITIONS, this seat's typing of the two rulings. Four choices are this seat's and are flagged.
 (1) "Admitted" is typed against a SUPPLIED predicate Defd, canonical choice Cont, and is asked at every
 raw possibility of the boundary. (2) "Keeps no record" is typed against a SUPPLIED rule for what a word
 keeps. By the author's ruling of 19:45 HST a word keeps what its fragments keep and nothing else
 (Def_APFPaper1_KeptByFragments, keepsFW); the theorems that need a rule take that one. This sentence
 replaces one that named the declared "maintained" as the canonical choice; the copy with that sentence is
 kept as Old/Def_APFPaper5_K2_HoldWord_pre-reheading_2026-11-16.lean. The code is unchanged. (3) "A reverse"
 is typed as the inverse: a word that runs as a map undoing the hold's map on either side. That is Paper
 5's reversal-as-inverse. (4) The reverse is asked to keep no record too. That is Paper 5's "the same
 record-free component". The author's sentence said "an admitted reverse"; if the reverse may keep
 records, drop the clause KeepsNoRecord from IsAdmittedReverse.
definitions:
 - RunsAsHoldAdmitted: the closed word is defined at every raw possibility of its boundary, and it runs as
   a map that is a hold of the listed family against the table.
 - KeepsNoRecord: the closed word keeps no record.
 - IsAdmittedReverse: a second closed word, admitted at every raw possibility, keeping no record, such that
   the two run as maps that undo each other in either order.
 - IsHoldWord: a hold, in the K layer. RunsAsHoldAdmitted, KeepsNoRecord, and some word is its admitted
   reverse.
not claimed: that any word of the foundation's own data other than the empty word is a hold. That a hold
 bills nothing: the definition has no clause on the bill beyond admission. No lane. No claim that the
 transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper5_K2_Hold

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2

universe uI uD uC uF uW uR
variable {ι : Type uI}
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uW}
  {Record : Context → Type uR}

/-- The closed word is admitted at every raw possibility of its boundary and runs as a map that is a hold
as defined. -/
def RunsAsHoldAdmitted (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context} (W : Word Frag a a)
    {D : Type uD} (reads : D → Raw a → Bool) (dist : ι → D) (G : ι → ι → ℝ)
    (sigma : Equiv.Perm ι) (flip : ι → Bool) : Prop :=
  (∀ x : Raw a, Defd a x ⟨a, W⟩) ∧
    ∃ h : Raw a → Raw a, ExecutesAs step W h ∧ IsHold reads dist G h sigma flip

/-- The closed word keeps no record. -/
def KeepsNoRecord (keeps : (g : Context) → WordFrom Frag g → Record g → Prop) {a : Context}
    (W : Word Frag a a) : Prop :=
  ∀ r : Record a, ¬ keeps a ⟨a, W⟩ r

/-- `W'` is an admitted reverse of `W`: admitted at every raw possibility, keeping no record, and the two
run as maps that undo each other in either order. -/
def IsAdmittedReverse (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (keeps : (g : Context) → WordFrom Frag g → Record g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
    (W W' : Word Frag a a) : Prop :=
  (∀ x : Raw a, Defd a x ⟨a, W'⟩) ∧ KeepsNoRecord keeps W' ∧
    ∃ h h' : Raw a → Raw a, ExecutesAs step W h ∧ ExecutesAs step W' h' ∧
      (∀ x : Raw a, h' (h x) = x) ∧ (∀ x : Raw a, h (h' x) = x)

/-- A hold, in the K layer: a closed word that is admitted and runs as a hold as defined, keeps no record,
and has an admitted reverse. -/
def IsHoldWord (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (keeps : (g : Context) → WordFrom Frag g → Record g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context} (W : Word Frag a a)
    {D : Type uD} (reads : D → Raw a → Bool) (dist : ι → D) (G : ι → ι → ℝ)
    (sigma : Equiv.Perm ι) (flip : ι → Bool) : Prop :=
  RunsAsHoldAdmitted Defd step W reads dist G sigma flip ∧ KeepsNoRecord keeps W ∧
    ∃ W' : Word Frag a a, IsAdmittedReverse Defd keeps step W W'

end APFPaper5.K2


