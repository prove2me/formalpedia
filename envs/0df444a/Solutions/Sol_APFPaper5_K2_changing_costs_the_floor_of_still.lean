-- Prove2me | solution 1 for APFPaper5.K2.changing_costs_the_floor_of_still
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:54:40.252253+00:00
-- url     : https://prove2.me/submissions/4495c7fb-3766-4fb2-aea9-55f203a363bb

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper5_K2_a_free_process_changes_nothing_recorded
title: The recorded side is still exactly when a record pins its side and there is no free gain; then a process that keeps no record keeps what is recorded of every state, leaves every state where it is when the list tells states apart, and any change of what is recorded is made by a word that keeps a record and bills at least the floor
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 61268e079b502e61175050261d79aa76046b44c76fa0d76b13e59b6847b3187a), kept in Old/ as
 Thm_APFPaper5_K2_a_free_process_changes_nothing_recorded_pre-restating_v57_2026-11-21.lean. No declaration
 is changed. THE RESTATED BYTES ARE NOT RELEASED.
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
 in bundle v51 (sha256 d60ca09a824d4a3d087f3b5bc124a1037a6235d728dcff77dfdd9b4da9034d1e), kept in Old/ as
 Thm_APFPaper5_K2_a_free_process_changes_nothing_recorded_pre-restating_v52_2026-11-17.lean. No declaration
 is changed. THE RESTATED BYTES ARE NOT RELEASED.
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
source: as for Def_APFPaper5_K2_RecordedSideStill, where the papers, the codebank, the rulings and the
 existing Lean consulted before writing are listed.
standing: ORDINARY MATHEMATICS ON SUPPLIED DATA, UNDER NAMED HYPOTHESES. `HeldFamilyPinned` is the
 author's ruled reading of the narrow floor (2026-11-17 11:41 HST). `NoFreeGain` and `RecordedSideStill`
 are NOT RULED: they are this seat's reading of how his rulings combine. None is a declared input.
consumes_inputs: none as hypotheses of the declared forms. `FreeOnWords` is this seat's candidate form of
 the last sentence of B06 and appears as a hypothesis of one theorem.
statement:
 - (recordedSideStill_iff) the recorded side is still exactly when a record pins its side and there is
   no free gain.
 - (noFreeGain_of_free_reverses, recordedSideStill_of_free_reverses) where every closed word that keeps
   no record can be run back by one that keeps none, pinning alone gives both. That is why pass 108
   needed nothing more for a hold.
 - (recordedSideStill_of_the_floor) with the sentence in its form on words, the floor charged on
   changing a recorded side gives a still recorded side.
 - (changing_costs_the_floor_of_still, changing_costs_the_floor_iff_still) with the floor by records, a
   still recorded side gives that floor; so with the sentence and the floor by records the two are one
   statement.
 - (free_word_keeps_the_held_family, free_word_keeps_the_recorded_class) on a still recorded side a
   closed word that keeps no record keeps K2's held family of the state it runs from, and so what is
   recorded of it.
 - (free_word_fixes_the_state) if the list tells raw possibilities apart, such a word runs from a raw
   possibility to itself and nowhere else.
 - (change_of_what_is_recorded_needs_a_record, change_of_what_is_recorded_costs_the_floor) on a still
   recorded side a closed word that changes the held family of a state keeps a record, and with the
   floor by records it bills at least the floor.
reading: with pinning and no free gain, what is recorded of a state changes only through a word that
 keeps a record, at no less than the floor. On the recorded side a process that keeps no record is the
 process that does nothing.
not_claimed: `NoFreeGain` itself; that the list tells raw possibilities apart (a hypothesis here);
 anything about a mark on which the occupant is in raw form; anything about words that are not closed.
 No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
 is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
restated: 2026-11-17, for bundle v51. The author ruled at 13:09 HST: "i agree with no free gain"
 (RULING_no_free_gain_2026-11-17). So `NoFreeGain` is his ruling, and with his ruling of 11:41 HST that a
 record pins its side, `RecordedSideStill` stands under his rulings. Where this header says NOT RULED of
 either, read: ruled, carried as a named hypothesis, not an input. Nothing else in this header is changed.
 Every byte after this comment is the byte of the file as first written.
-/
import Definitions.Def_APFPaper5_K2_RecordedSideStill
import Theorems.Thm_APFPaper5_K2_heldFamilyPinned_iff
import Theorems.Thm_APFPaper5_K2_heldFamilyPinned_of_the_floor_by_sides
import Theorems.Thm_APFPaper5_K2_holdWord_keeps_every_listed_side
import Theorems.Thm_APFPaper5_K2_holdWord_keeps_the_held_family
import Theorems.Thm_APFPaper5_K2_holdWord_keeps_the_recorded_class
import Theorems.Thm_APFPaper5_K2_holdWord_does_nothing_on_the_recorded_side
import Theorems.Thm_APFPaper5_K2_holdWord_rearrangement_trivial_on_the_recorded_side
import Theorems.Thm_APFPaper5_K2_no_hold_but_doing_nothing_on_the_recorded_side

set_option autoImplicit false
open APFPaper1.Continuation APFPaper1.NarrowOnWords

namespace APFPaper5.K2

universe uC uF uX uR uK uD uW
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
  {Dn : Context → Type uD}

/-- The recorded side is still exactly when a record pins its side and there is no free gain. -/
theorem recordedSideStill_iff_p2mProof (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g)) :
    RecordedSideStill step keptFrag reads listed ↔
      HeldFamilyPinned step keptFrag reads listed ∧ NoFreeGain step keptFrag reads listed := by
  constructor
  · intro hS
    refine ⟨(heldFamilyPinned_iff step keptFrag reads listed).mpr ?_, ?_⟩
    · intro g W x y d hk hex hd ht
      rw [hS g W x y d hk hex hd, ht]
    · intro g W x y d hk hex hd hf
      rw [hS g W x y d hk hex hd, hf]
  · rintro ⟨hP, hN⟩ g W x y d hk hex hd
    have hP' := (heldFamilyPinned_iff step keptFrag reads listed).mp hP
    cases hb : reads g d x with
    | true => exact hP' g W x y d hk hex hd hb
    | false => exact hN g W x y d hk hex hd hb

/-- Where every closed word that keeps no record can be run back by one that keeps none, pinning gives
no free gain. -/
theorem noFreeGain_of_free_reverses_p2mProof (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed)
    (hrev : ∀ (g : Context) (W : Word Frag g g) (x y : Raw g),
      keptByFragments keptFrag g W = ∅ → Executes step W x y →
        ∃ W' : Word Frag g g, keptByFragments keptFrag g W' = ∅ ∧ Executes step W' y x) :
    NoFreeGain step keptFrag reads listed := by
  intro g W x y d hk hex hd hf
  have hP' := (heldFamilyPinned_iff step keptFrag reads listed).mp hP
  cases hc : reads g d y with
  | false => rfl
  | true =>
    obtain ⟨W', hk', hex'⟩ := hrev g W x y hk hex
    have h2 := hP' g W' y x d hk' hex' hd hc
    rw [hf] at h2
    exact absurd h2 (by decide)

/-- And so the recorded side is still. -/
theorem recordedSideStill_of_free_reverses_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed)
    (hrev : ∀ (g : Context) (W : Word Frag g g) (x y : Raw g),
      keptByFragments keptFrag g W = ∅ → Executes step W x y →
        ∃ W' : Word Frag g g, keptByFragments keptFrag g W' = ∅ ∧ Executes step W' y x) :
    RecordedSideStill step keptFrag reads listed :=
  (recordedSideStill_iff_p2mProof step keptFrag reads listed).mpr
    ⟨hP, noFreeGain_of_free_reverses_p2mProof step keptFrag reads listed hP hrev⟩

/-- With the sentence in its form on words, the floor charged on changing a recorded side gives a still
recorded side. -/
theorem recordedSideStill_of_the_floor_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (eps : Context → NNReal) (hfree : APFB06.FreeOnWords resource calibration keptFrag)
    (hC : ChangingARecordedSideCostsTheFloor step resource calibration reads listed eps) :
    RecordedSideStill step keptFrag reads listed := by
  intro g W x y d hk hex hd
  by_contra hne
  have h1 := hC.2 g W x y d hex hd hne
  rw [hfree g ⟨g, W⟩ hk] at h1
  exact absurd h1 (not_le.mpr (hC.1 g))

/-- With the floor by records, a still recorded side gives the floor on changing a recorded side. -/
theorem changing_costs_the_floor_of_still_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (eps : Context → NNReal) (hM : MakingARecordCostsTheFloor resource calibration keptFrag eps)
    (hS : RecordedSideStill step keptFrag reads listed) :
    ChangingARecordedSideCostsTheFloor step resource calibration reads listed eps :=
  ⟨hM.1, fun g W x y d hex hd hne => hM.2 g W (fun hk => hne (hS g W x y d hk hex hd))⟩

/-- So with the sentence and the floor by records, the two are one statement. -/
theorem changing_costs_the_floor_iff_still_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (eps : Context → NNReal) (hfree : APFB06.FreeOnWords resource calibration keptFrag)
    (hM : MakingARecordCostsTheFloor resource calibration keptFrag eps) :
    ChangingARecordedSideCostsTheFloor step resource calibration reads listed eps ↔
      RecordedSideStill step keptFrag reads listed :=
  ⟨recordedSideStill_of_the_floor_p2mProof step resource calibration keptFrag reads listed eps hfree,
    changing_costs_the_floor_of_still_p2mProof step resource calibration keptFrag reads listed eps hM⟩

/-- On a still recorded side a closed word that keeps no record keeps K2's held family of the state it
runs from. -/
theorem free_word_keeps_the_held_family_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hS : RecordedSideStill step keptFrag reads listed) (g : Context) (W : Word Frag g g)
    (x y : Raw g) (hk : keptByFragments keptFrag g W = ∅) (hex : Executes step W x y) :
    heldFamily (reads g) (listed g) y = heldFamily (reads g) (listed g) x := by
  ext d
  rw [APFPaper5.K2.mem_heldFamily_r2, APFPaper5.K2.mem_heldFamily_r2]
  constructor
  · rintro ⟨hd, ht⟩
    refine ⟨hd, ?_⟩
    rw [← hS g W x y d hk hex hd]
    exact ht
  · rintro ⟨hd, ht⟩
    refine ⟨hd, ?_⟩
    rw [hS g W x y d hk hex hd]
    exact ht

/-- And so what is recorded of it. -/
theorem free_word_keeps_the_recorded_class_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hS : RecordedSideStill step keptFrag reads listed) (g : Context) (W : Word Frag g g)
    (x y : Raw g) (hk : keptByFragments keptFrag g W = ∅) (hex : Executes step W x y)
    {Wr : Type uW} (keeps : Finset (Dn g) → Wr → Bool) :
    recordedClass keeps (reads g) (listed g) y = recordedClass keeps (reads g) (listed g) x := by
  unfold recordedClass
  rw [free_word_keeps_the_held_family_p2mProof step keptFrag reads listed hS g W x y hk hex]

/-- If the list tells raw possibilities apart, a closed word that keeps no record runs from a raw
possibility to itself and nowhere else. -/
theorem free_word_fixes_the_state_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hS : RecordedSideStill step keptFrag reads listed) (g : Context)
    (hsep : ∀ x y : Raw g, (∀ d ∈ listed g, reads g d y = reads g d x) → y = x)
    (W : Word Frag g g) (x y : Raw g) (hk : keptByFragments keptFrag g W = ∅)
    (hex : Executes step W x y) : y = x :=
  hsep x y (fun d hd => hS g W x y d hk hex hd)

/-- On a still recorded side a closed word that changes the held family of a state keeps a record. -/
theorem change_of_what_is_recorded_needs_a_record_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hS : RecordedSideStill step keptFrag reads listed) (g : Context) (W : Word Frag g g)
    (x y : Raw g) (hex : Executes step W x y)
    (hne : heldFamily (reads g) (listed g) y ≠ heldFamily (reads g) (listed g) x) :
    keptByFragments keptFrag g W ≠ ∅ :=
  fun hk => hne (free_word_keeps_the_held_family_p2mProof step keptFrag reads listed hS g W x y hk hex)

/-- And with the floor by records it bills at least the floor. -/
theorem change_of_what_is_recorded_costs_the_floor_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (eps : Context → NNReal) (hM : MakingARecordCostsTheFloor resource calibration keptFrag eps)
    (hS : RecordedSideStill step keptFrag reads listed) (g : Context) (W : Word Frag g g)
    (x y : Raw g) (hex : Executes step W x y)
    (hne : heldFamily (reads g) (listed g) y ≠ heldFamily (reads g) (listed g) x) :
    eps g ≤ calibration g (resource g ⟨g, W⟩) :=
  hM.2 g W (change_of_what_is_recorded_needs_a_record_p2mProof step keptFrag reads listed hS g W x y hex hne)

end APFPaper5.K2


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uK apfNative_uD
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {Rec : Context → Type apfNative_uK}
  [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)] {Dn : Context → Type apfNative_uD}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g))
  (eps : Context → NNReal)
  (hM :
    @APFPaper1.NarrowOnWords.MakingARecordCostsTheFloor.{apfNative_uC, apfNative_uF, apfNative_uR, apfNative_uK} Context
      Frag R Rec inst resource calibration keptFrag eps)
  (hS :
    @APFPaper5.K2.RecordedSideStill.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
      Raw Rec inst Dn step keptFrag reads listed),
  @APFPaper5.K2.ChangingARecordedSideCostsTheFloor.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR,
        apfNative_uD}
    Context Frag Raw R Dn step resource calibration reads listed eps := by
  exact @APFPaper5.K2.changing_costs_the_floor_of_still_p2mProof
