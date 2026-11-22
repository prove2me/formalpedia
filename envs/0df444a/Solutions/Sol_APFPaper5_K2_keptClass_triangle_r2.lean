-- Prove2me | solution 1 for APFPaper5.K2.keptClass_triangle_r2
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:58:59.989502+00:00
-- url     : https://prove2.me/submissions/906cb1bd-5a07-4d9d-9c77-e010779ad0c8

/-
CUT 2026-11-17 by the seat that wrote this file, on the author's word of 03:12 HST, "then let's bolt k2 to spine"
(RULING_K2s_recorded_side_goes_on_the_spine_2026-11-17), read as covering the cut on the precedent of K1 (his "Yes" of 2026-11-16 11:20 HST).
Only this block is new. The original header below it is unchanged. The code is unchanged except as this
block says. Where the original header differs from this block, this block governs. Pre-cut copy:
Old/Thm_APFPaper5_K2_recorded_classes_pre-cut_2026-11-17.lean, sha256
7b838b50b1566bc7bd9006c2d2840d9424bf5e9bb2adceae18b87e8d3e911c2b (the file released on 2026-11-15 and reported
uploaded).
 - MOVED OUT, unchanged: the definitions heldFamily and recordedClass, to
   Definitions/Def_APFPaper5_K2_RecordedClass, which this file imports.
 - Import lines: Def_APFPaper5_K2_StateClass and Thm_APFPaper5_K2_state_class_candidates REMOVED;
   Def_APFPaper5_K2_RecordedClass and Thm_APFPaper5_K2_kept_class_cost added. So this file no longer stands
   on the two candidates the author did not choose. Where the original header's source line names
   Def_APFPaper5_K2_StateClass and Thm_APFPaper5_K2_state_class_candidates, read the two new files.
 - Left here, unchanged: the five theorems.
 - Still a DRAFT at this hash: not gated, not reviewed, not released, not built in the ledger repo, not
   built on the build machine.
 - Unchanged: no lane; no claim that the transfer is forced, that the carrier gap is closed or narrowed, or
   that Born is derived.

APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_recorded_classes
title: What is recorded: the class of a state is the list of records its held family keeps; its cost is the ledger's; any three such classes obey the record ledger's bound, so a turned mark is not among them
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 53030f0793d2dcf1c1a5b721092611637f10ff0d836f35d133a6a793e315d602), kept in Old/ as
 Thm_APFPaper5_K2_recorded_classes_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE
 RESTATED BYTES ARE NOT RELEASED.
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
source: Def_APFPaper5_K2_StateClass (keptClass, recordForm); Thm_APFPaper5_K2_state_class_candidates
 (keptClass_cost); Thm_APFPaper5_K1_record_tables_and_turns (atomTable_triangle, turnTable). Paper 1
 Supplement v9.28:1829-1843 (a structural alignment: a carrier and the finite family of distinctions each
 reading 1 on it).
consumes_inputs: none.
definitions:
 - heldFamily: among listed distinctions, those that read true on the state.
 - recordedClass: the list of records the held family keeps.
theorems:
 - (mem_heldFamily) a distinction is in the held family exactly when it is listed and reads true.
 - (recordedClass_cost) the weighted overlap of the recorded class with itself is the cost of the records the
   held family keeps.
 - (keptClass_triangle, recorded_states_triangle) for costs that are never negative, the classes of any three
   held families, and so of any three states, obey the record ledger's bound.
 - (no_three_recorded_classes_have_turnTable) so no three recorded classes have the table of a mark, its
   turn and its double turn, for any turn strictly between none and the quarter turn.
reading: "records are never in superposition" is, as typed, that a recorded class is a list of records. A
 turned mark is then not a recorded class. Nothing here says what it is.
not claimed: anything about what a state holds that is not recorded; any action of a hold or a test on
 recorded classes. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed,
 or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_RecordedClass
import Theorems.Thm_APFPaper5_K2_ind_mul_self
import Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
import Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_triangle
import Theorems.Thm_APFPaper5_K1_atomTable_le_diag
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_triangle
import Theorems.Thm_APFPaper5_K1_turnTable_symm
import Theorems.Thm_APFPaper5_K1_turnTable_breaks_triangle
import Theorems.Thm_APFPaper5_K1_no_record_ledger_has_turnTable
import Theorems.Thm_APFPaper5_K1_no_three_distinctions_have_turnTable
import Theorems.Thm_APFPaper5_K1_turnTable_half_form
import Theorems.Thm_APFPaper5_K1_turnTable_half_nonneg
import Theorems.Thm_APFPaper5_K1_turnTable_half_faithful
import Theorems.Thm_APFPaper5_K1_ownTable_eq
import Theorems.Thm_APFPaper5_K1_turnClass_negative
import Theorems.Thm_APFPaper5_K1_turnTable_on_classes

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uX uD uW
variable {X : Type uX} {D : Type uD} {W : Type uW}

theorem mem_heldFamily_p2mProof (reads : D → X → Bool) (S : Finset D) (x : X) (d : D) :
    d ∈ heldFamily reads S x ↔ d ∈ S ∧ reads d x = true :=
  Finset.mem_filter

/-- The cost of what is recorded of a state is the cost of the records its held family keeps. -/
theorem recordedClass_cost_p2mProof [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool)
    (reads : D → X → Bool) (S : Finset D) (x : X) :
    recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S x) =
      keptCost w keeps (heldFamily reads S x) :=
  APFPaper5.K2.keptClass_cost_r2 w keeps (heldFamily reads S x)

/-- The classes of any three held families obey the record ledger's bound. -/
theorem keptClass_triangle_p2mProof [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset D → W → Bool) (S T U : Finset D) :
    recordForm w (keptClass keeps S) (keptClass keeps T) +
        recordForm w (keptClass keeps S) (keptClass keeps U) -
        recordForm w (keptClass keeps T) (keptClass keeps U) ≤
      recordForm w (keptClass keeps S) (keptClass keeps S) :=
  atomTable_triangle w hw (fun (F : Finset D) (a : W) => keeps F a) S T U

/-- So do the recorded classes of any three states. -/
theorem recorded_states_triangle_p2mProof [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset D → W → Bool) (reads : D → X → Bool) (S : Finset D) (x y z : X) :
    recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S y) +
        recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S z) -
        recordForm w (recordedClass keeps reads S y) (recordedClass keeps reads S z) ≤
      recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S x) :=
  keptClass_triangle_p2mProof w hw keeps _ _ _

/-- No three recorded classes have the table of a mark, its turn and its double turn. -/
theorem no_three_recorded_classes_have_turnTable_p2mProof [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset D → W → Bool) (F : Fin 3 → Finset D) (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    ¬ ∀ i j, recordForm w (keptClass keeps (F i)) (keptClass keeps (F j)) = turnTable t i j :=
  no_record_ledger_has_turnTable w hw (fun (i : Fin 3) (a : W) => keeps (F i) a) t h0 h1

end APFPaper5.K2


universe apfNative_uD apfNative_uW
theorem solution :
∀ {D : Type apfNative_uD} {W : Type apfNative_uW} [inst : Fintype.{apfNative_uW} W] (w : W → Real)
  (hw :
    ∀ (a : W),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w a))
  (keeps : Finset.{apfNative_uD} D → W → Bool) (S T U : Finset.{apfNative_uD} D),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps T))
        (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps U)))
      (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w
        (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps T)
        (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps U)))
    (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
      (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)) := by
  exact @APFPaper5.K2.keptClass_triangle_p2mProof
