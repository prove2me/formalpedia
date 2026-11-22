-- Prove2me | solution 1 for APFPaper5.K2.holdWord_keeps_the_recorded_class
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T19:19:09.982136+00:00
-- url     : https://prove2.me/submissions/ad074b2e-006f-4cc7-a0d6-d89daec50676

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper5_K2_no_hold_on_the_recorded_side
title: Where a record pins its side, a hold in the K layer keeps the held family and the recorded class of every state; where the list tells states apart it leaves every state where it is; and with B02's second sentence its rearrangement is the identity with no turn-over
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 4823bc0fbdfc6a37dcd774c4e053bf3fd97fed12b7faca98a118d9b3a8057a1c), kept in Old/ as
 Thm_APFPaper5_K2_no_hold_on_the_recorded_side_pre-restating_v57_2026-11-21.lean. No declaration is changed.
 THE RESTATED BYTES ARE NOT RELEASED.
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
 in bundle v51 (sha256 2da769da54bd194ee45d458f89c6fa8ddbb70eb03fd9f92800a398ee4012a547), kept in Old/ as
 Thm_APFPaper5_K2_no_hold_on_the_recorded_side_pre-restating_v52_2026-11-17.lean. No declaration is changed.
 THE RESTATED BYTES ARE NOT RELEASED.
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
source: the author, 2026-11-17 11:41 HST: "A and all you can that's open"
 (RULING_a_record_pins_its_side_2026-11-17), on TEE_UP_does_a_record_pin_its_side_2026-11-17, which said
 of option A: "If A, this seat would, on your word only: record the ruling; type the corollary on K2's
 own held family (no hold but doing nothing on the recorded side, under pinning)". This file is that
 corollary. Consulted: as listed in Def_APFPaper1_NarrowFloorOnWords (pass 107) and in the tee-up;
 the released Def_APFPaper5_K2_RecordedClass and Thm_APFPaper5_K2_recorded_classes (heldFamily,
 recordedClass, mem_heldFamily); Def_APFPaper5_K2_HoldWord; pass 94's isHold_changes_no_reading_iff;
 pass 107's Thm_APFPaper1_narrow_floor_on_words. Nothing further was opened.
standing: ORDINARY MATHEMATICS ON SUPPLIED DATA, UNDER A NAMED HYPOTHESIS. `HeldFamilyPinned` is the
 author's ruled reading of the narrow floor. It is not one of the eight declared inputs and does not
 follow from them. It is a hypothesis of every theorem here that uses it.
consumes_inputs: B02's second sentence, in its encoded form APFB02.EveryCombinationHeld, as a hypothesis
 of two theorems. No other declared form.
statement: in a context a, for a hold word W in the K layer (Def_APFPaper5_K2_HoldWord, keeping taken
 fragment by fragment) of a family whose members are listed:
 - (heldFamilyPinned_iff) pinning says: a listed distinction that reads true still reads true after any
   closed word that keeps no record.
 - (heldFamilyPinned_of_the_floor_by_sides) with "A process that keeps no record costs nothing" in its
   form on words, the floor charged on turning over a member of a state's held family gives pinning.
 - (holdWord_keeps_every_listed_side) under pinning, the hold leaves every member of its family on its
   side, at every raw possibility. The admitted reverse carries the sides that read false.
 - (holdWord_keeps_the_held_family, holdWord_keeps_the_recorded_class) if the family is the whole list,
   the hold keeps K2's held family of every raw possibility, and so what is recorded of it.
 - (holdWord_does_nothing_on_the_recorded_side) if moreover the list tells raw possibilities apart, the
   hold leaves every raw possibility where it is.
 - (holdWord_rearrangement_trivial_on_the_recorded_side) with B02's second sentence and each
   distinction listed once, the rearrangement of the hold is the identity with no turn-over.
 - (no_hold_but_doing_nothing_on_the_recorded_side) all of it in one statement.
reading: on the recorded side, under the ruling, a hold is doing nothing. "Doing nothing" is: it runs as
 the map that leaves every raw possibility where it is, and its rearrangement is the identity with no
 turn-over. It is not shown to be the empty word.
not_claimed: pinning itself; that the list tells raw possibilities apart (B02's reading of 2026-11-14 says
 so; it is a hypothesis here); anything about a mark on which the occupant is in raw form, or about any
 hold that is not on the recorded side; anything about words that are not closed. No lane. No claim that
 the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_HeldFamilyPinned
import Definitions.Def_APFPaper5_K2_HoldWord
import Theorems.Thm_APFPaper5_K2_executesAs_unique
import Theorems.Thm_APFPaper5_K2_rearrangement_unique
import Theorems.Thm_APFPaper5_K2_mem_heldFamily_r2

set_option autoImplicit false
namespace APFPaper1.NarrowOnWords
open APFPaper1.Continuation
universe uC uF uX uR uK uD
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
  {Dn : Context → Type uD}
/-- With the sentence, the floor typed by sides gives: a held side is pinned. -/
theorem pinned_of_sides (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (heldAt : (g : Context) → Raw g → Dn g → Prop)
    (eps : Context → NNReal) (hfree : APFB06.FreeOnWords resource calibration keptFrag)
    (hS : TurningAHeldSideCostsTheFloor step resource calibration reads heldAt eps) :
    HeldSidesPinned step keptFrag reads heldAt := by
  intro g W x y d hk hex hheld
  by_contra hne
  have h1 := hS.2 g W x y d hex hheld hne
  rw [hfree g ⟨g, W⟩ hk] at h1
  exact absurd h1 (not_le.mpr (hS.1 g))
end APFPaper1.NarrowOnWords
namespace APFPaper5.K2
open APFPaper1.Continuation
universe uI uD uC uF uW uR uK uX
variable {ι : Type uI}
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uW}
  {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
omit [∀ g, DecidableEq (Rec g)] in
/-- A set with no member is empty. -/
theorem finset_eq_empty_of_no_member {α : Type uK} (S : Finset α) (h : ∀ r : α, r ∉ S) : S = ∅ :=
  Finset.ext (fun r => ⟨fun hr => absurd hr (h r), fun hr => absurd hr (by simp)⟩)

/-- The clause "keeps no record", with keeping taken fragment by fragment. -/
theorem keepsNoRecord_keepsFW_iff (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    {a : Context} (W : Word Frag a a) :
    KeepsNoRecord (keepsFW keptFrag) W ↔ keptByFragments keptFrag a W = ∅ := by
  constructor
  · intro h
    exact finset_eq_empty_of_no_member _ h
  · intro h r hr
    have h0 : r ∈ keptByFragments keptFrag a W := hr
    rw [h] at h0
    simp at h0

/-- Where every combination of sides is held and the list names each distinction once, a hold leaves every
listed reading of every state as it was exactly when its rearrangement is the identity with no
turn-overs. -/
theorem isHold_changes_no_reading_iff {X : Type uX} {D : Type uD} (reads : D → X → Bool)
    (hall : APFB02.EveryCombinationHeld reads) (dist : ι → D) (hinj : Function.Injective dist)
    (G : ι → ι → ℝ) (h : X → X) (sigma : Equiv.Perm ι) (flip : ι → Bool)
    (hh : IsHold reads dist G h sigma flip) :
    (∀ (i : ι) (x : X), reads (dist i) (h x) = reads (dist i) x) ↔
      (sigma = Equiv.refl ι ∧ flip = fun _ => false) := by
  constructor
  · intro hsame
    have r0 : RearrangesFamily reads dist h id (fun _ => false) := by
      intro i x
      rw [hsame i x]
      exact (Bool.false_xor (reads (dist i) x)).symm
    obtain ⟨hs, hf⟩ := rearrangement_unique reads hall dist hinj h (sigma : ι → ι) id flip
      (fun _ => false) hh.1 r0
    exact ⟨Equiv.ext (fun i => congrFun hs i), hf⟩
  · rintro ⟨hs, hf⟩ i x
    have e := hh.1 i x
    rw [hs, hf] at e
    rw [e]
    exact Bool.false_xor (reads (dist i) x)
end APFPaper5.K2

set_option autoImplicit false
open APFPaper1.Continuation APFPaper1.NarrowOnWords

namespace APFPaper5.K2

universe uI uC uF uX uR uK uD uW
variable {ι : Type uI}
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
  {Dn : Context → Type uD}

/-- Pinning says: a listed distinction that reads true still reads true after any closed word that keeps
no record. -/
theorem heldFamilyPinned_iff_p2mProof (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g)) :
    HeldFamilyPinned step keptFrag reads listed ↔
      ∀ (g : Context) (W : Word Frag g g) (x y : Raw g) (d : Dn g),
        keptByFragments keptFrag g W = ∅ → Executes step W x y → d ∈ listed g →
          reads g d x = true → reads g d y = true := by
  constructor
  · intro hP g W x y d hk hex hd ht
    have h1 := hP g W x y d hk hex ((APFPaper5.K2.mem_heldFamily_r2 (reads g) (listed g) x d).mpr ⟨hd, ht⟩)
    rw [h1]
    exact ht
  · intro h g W x y d hk hex hmem
    obtain ⟨hd, ht⟩ := (APFPaper5.K2.mem_heldFamily_r2 (reads g) (listed g) x d).mp hmem
    rw [h g W x y d hk hex hd ht, ht]

/-- With the sentence in its form on words, the floor charged on turning over a member of a state's held
family gives pinning. -/
theorem heldFamilyPinned_of_the_floor_by_sides_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (eps : Context → NNReal) (hfree : APFB06.FreeOnWords resource calibration keptFrag)
    (hS : TurningAHeldSideCostsTheFloor step resource calibration reads
      (fun g x d => d ∈ heldFamily (reads g) (listed g) x) eps) :
    HeldFamilyPinned step keptFrag reads listed :=
  pinned_of_sides step resource calibration keptFrag reads
    (fun g x d => d ∈ heldFamily (reads g) (listed g) x) eps hfree hS

/-- Under pinning, a hold in the K layer leaves every member of its family on its side, at every raw
possibility. The hold pins the sides that read true; its admitted reverse pins the sides that read true
after it. -/
theorem holdWord_keeps_every_listed_side_p2mProof
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed) {a : Context} (W : Word Frag a a)
    (dist : ι → Dn a) (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (flip : ι → Bool)
    (hW : IsHoldWord Defd (keepsFW keptFrag) step W (reads a) dist G sigma flip)
    (hlisted : ∀ i, dist i ∈ listed a) (h : Raw a → Raw a) (hex : ExecutesAs step W h)
    (x : Raw a) (i : ι) : reads a (dist i) (h x) = reads a (dist i) x := by
  have hP' := (heldFamilyPinned_iff_p2mProof step keptFrag reads listed).mp hP
  obtain ⟨W', _, hk', h1, h1', hex1, hex1', hinv1, _⟩ := hW.2.2
  have hh : h1 = h := executesAs_unique step W h1 h hex1 hex
  subst hh
  cases hb : reads a (dist i) x with
  | true =>
    exact hP' a W x (h1 x) (dist i) ((keepsNoRecord_keepsFW_iff keptFrag W).mp hW.2.1)
      ((hex x (h1 x)).mpr rfl) (hlisted i) hb
  | false =>
    cases hc : reads a (dist i) (h1 x) with
    | false => rfl
    | true =>
      have h2 := hP' a W' (h1 x) (h1' (h1 x)) (dist i)
        ((keepsNoRecord_keepsFW_iff keptFrag W').mp hk')
        ((hex1' (h1 x) (h1' (h1 x))).mpr rfl) (hlisted i) hc
      rw [hinv1 x, hb] at h2
      exact absurd h2 (by decide)

/-- If the family is the whole list, the hold keeps K2's held family of every raw possibility. -/
theorem holdWord_keeps_the_held_family_p2mProof
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed) {a : Context} (W : Word Frag a a)
    (dist : ι → Dn a) (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (flip : ι → Bool)
    (hW : IsHoldWord Defd (keepsFW keptFrag) step W (reads a) dist G sigma flip)
    (hlisted : ∀ i, dist i ∈ listed a) (hcover : ∀ d ∈ listed a, ∃ i, dist i = d)
    (h : Raw a → Raw a) (hex : ExecutesAs step W h) (x : Raw a) :
    heldFamily (reads a) (listed a) (h x) = heldFamily (reads a) (listed a) x := by
  ext d
  rw [APFPaper5.K2.mem_heldFamily_r2, APFPaper5.K2.mem_heldFamily_r2]
  constructor
  · rintro ⟨hd, ht⟩
    obtain ⟨i, rfl⟩ := hcover d hd
    refine ⟨hd, ?_⟩
    rw [← holdWord_keeps_every_listed_side_p2mProof Defd step keptFrag reads listed hP W dist G sigma flip
      hW hlisted h hex x i]
    exact ht
  · rintro ⟨hd, ht⟩
    obtain ⟨i, rfl⟩ := hcover d hd
    refine ⟨hd, ?_⟩
    rw [holdWord_keeps_every_listed_side_p2mProof Defd step keptFrag reads listed hP W dist G sigma flip
      hW hlisted h hex x i]
    exact ht

/-- And so it keeps what is recorded of every raw possibility. -/
theorem holdWord_keeps_the_recorded_class_p2mProof
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed) {a : Context} (W : Word Frag a a)
    (dist : ι → Dn a) (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (flip : ι → Bool)
    (hW : IsHoldWord Defd (keepsFW keptFrag) step W (reads a) dist G sigma flip)
    (hlisted : ∀ i, dist i ∈ listed a) (hcover : ∀ d ∈ listed a, ∃ i, dist i = d)
    {Wr : Type uW} (keeps : Finset (Dn a) → Wr → Bool)
    (h : Raw a → Raw a) (hex : ExecutesAs step W h) (x : Raw a) :
    recordedClass keeps (reads a) (listed a) (h x) = recordedClass keeps (reads a) (listed a) x := by
  unfold recordedClass
  rw [holdWord_keeps_the_held_family_p2mProof Defd step keptFrag reads listed hP W dist G sigma flip hW
    hlisted hcover h hex x]

/-- If moreover the list tells raw possibilities apart, the hold leaves every raw possibility where it
is. -/
theorem holdWord_does_nothing_on_the_recorded_side_p2mProof
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed) {a : Context} (W : Word Frag a a)
    (dist : ι → Dn a) (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (flip : ι → Bool)
    (hW : IsHoldWord Defd (keepsFW keptFrag) step W (reads a) dist G sigma flip)
    (hlisted : ∀ i, dist i ∈ listed a) (hcover : ∀ d ∈ listed a, ∃ i, dist i = d)
    (hsep : ∀ x y : Raw a, (∀ d ∈ listed a, reads a d y = reads a d x) → y = x)
    (h : Raw a → Raw a) (hex : ExecutesAs step W h) (x : Raw a) : h x = x :=
  hsep x (h x) (fun d hd => by
    obtain ⟨i, rfl⟩ := hcover d hd
    exact holdWord_keeps_every_listed_side_p2mProof Defd step keptFrag reads listed hP W dist G sigma flip
      hW hlisted h hex x i)

/-- With B02's second sentence and each distinction listed once, the rearrangement of the hold is the
identity with no turn-over. -/
theorem holdWord_rearrangement_trivial_on_the_recorded_side_p2mProof
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed) {a : Context} (W : Word Frag a a)
    (dist : ι → Dn a) (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (flip : ι → Bool)
    (hW : IsHoldWord Defd (keepsFW keptFrag) step W (reads a) dist G sigma flip)
    (hlisted : ∀ i, dist i ∈ listed a)
    (hcomb : APFB02.EveryCombinationHeld (reads a)) (hinj : Function.Injective dist) :
    sigma = Equiv.refl ι ∧ flip = fun _ => false := by
  obtain ⟨h, hex, hhold⟩ := hW.1.2
  exact (isHold_changes_no_reading_iff (reads a) hcomb dist hinj G h sigma flip hhold).mp
    (fun i x => holdWord_keeps_every_listed_side_p2mProof Defd step keptFrag reads listed hP W dist G sigma
      flip hW hlisted h hex x i)

/-- On the recorded side, under pinning, a hold is doing nothing: its rearrangement is the identity with
no turn-over, and it runs as the map that leaves every raw possibility where it is. -/
theorem no_hold_but_doing_nothing_on_the_recorded_side_p2mProof
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hP : HeldFamilyPinned step keptFrag reads listed) {a : Context} (W : Word Frag a a)
    (dist : ι → Dn a) (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (flip : ι → Bool)
    (hW : IsHoldWord Defd (keepsFW keptFrag) step W (reads a) dist G sigma flip)
    (hlisted : ∀ i, dist i ∈ listed a) (hcover : ∀ d ∈ listed a, ∃ i, dist i = d)
    (hsep : ∀ x y : Raw a, (∀ d ∈ listed a, reads a d y = reads a d x) → y = x)
    (hcomb : APFB02.EveryCombinationHeld (reads a)) (hinj : Function.Injective dist) :
    sigma = Equiv.refl ι ∧ (flip = fun _ => false) ∧
      ∀ h : Raw a → Raw a, ExecutesAs step W h → ∀ x : Raw a, h x = x := by
  obtain ⟨hs, hf⟩ := holdWord_rearrangement_trivial_on_the_recorded_side_p2mProof Defd step keptFrag reads
    listed hP W dist G sigma flip hW hlisted hcomb hinj
  exact ⟨hs, hf, fun h hex x => holdWord_does_nothing_on_the_recorded_side_p2mProof Defd step keptFrag reads
    listed hP W dist G sigma flip hW hlisted hcover hsep h hex x⟩

end APFPaper5.K2


universe apfNative_uI apfNative_uC apfNative_uF apfNative_uX apfNative_uK apfNative_uD apfNative_uW
theorem solution :
∀ {ι : Type apfNative_uI} {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF}
  {Raw : Context → Type apfNative_uX} {Rec : Context → Type apfNative_uK}
  [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)] {Dn : Context → Type apfNative_uD}
  (Defd : (g : Context) → Raw g → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Prop)
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g))
  (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset.{apfNative_uD} (Dn g))
  (hP :
    @APFPaper5.K2.HeldFamilyPinned.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK, apfNative_uD} Context Frag
      Raw Rec inst Dn step keptFrag reads listed)
  {a : Context} (W : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a) (dist : ι → Dn a)
  (G : ι → ι → Real) (sigma : Equiv.Perm.{apfNative_uI + 1} ι) (flip : ι → Bool)
  (hW :
    @APFPaper5.K2.IsHoldWord.{apfNative_uI, apfNative_uD, apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uK} ι
      Context Frag Raw Rec Defd
      (@APFPaper1.Continuation.keepsFW.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst keptFrag) step a
      W (Dn a) (reads a) dist G sigma flip)
  (hlisted :
    ∀ (i : ι),
      @Membership.mem.{apfNative_uD, apfNative_uD} (Dn a) (Finset.{apfNative_uD} (Dn a))
        (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn a)) (Dn a)
          (@Finset.instSetLike.{apfNative_uD} (Dn a)))
        (listed a) (dist i))
  (hcover :
    ∀ (d : Dn a),
      @Membership.mem.{apfNative_uD, apfNative_uD} (Dn a) (Finset.{apfNative_uD} (Dn a))
          (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} (Dn a)) (Dn a)
            (@Finset.instSetLike.{apfNative_uD} (Dn a)))
          (listed a) d →
        @Exists.{apfNative_uI + 1} ι fun (i : ι) => @Eq.{apfNative_uD + 1} (Dn a) (dist i) d)
  {Wr : Type apfNative_uW} (keeps : Finset.{apfNative_uD} (Dn a) → Wr → Bool) (h : Raw a → Raw a)
  (hex : @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw step a W h) (x : Raw a),
  @Eq.{apfNative_uW + 1} (Wr → Real)
    (@APFPaper5.K2.recordedClass.{apfNative_uX, apfNative_uD, apfNative_uW} (Raw a) (Dn a) Wr keeps (reads a) (listed a)
      (h x))
    (@APFPaper5.K2.recordedClass.{apfNative_uX, apfNative_uD, apfNative_uW} (Raw a) (Dn a) Wr keeps (reads a) (listed a)
      x) := by
  exact @APFPaper5.K2.holdWord_keeps_the_recorded_class_p2mProof
