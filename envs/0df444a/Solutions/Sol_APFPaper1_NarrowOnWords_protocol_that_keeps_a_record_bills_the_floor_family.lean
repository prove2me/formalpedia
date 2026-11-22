-- Prove2me | solution 1 for APFPaper1.NarrowOnWords.protocol_that_keeps_a_record_bills_the_floor_family
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T20:41:10.033399+00:00
-- url     : https://prove2.me/submissions/fac81d90-c6c0-4d3a-b9aa-e0636c691c13

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper5_K2_a_protocol_that_changes_what_is_recorded_bills_the_floor
title: The two sentences added to B06 at inputs revision 2026-11-17.4, joined: with B05's declared form and "Holding nothing costs nothing", a protocol that changes what is recorded of a state bills at least the floor
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 a9192af9c0dfda4211fbfbf5992d17b9ea179c52f9d4b2114aeda1734eca268f), kept in Old/ as
 Thm_APFPaper5_K2_a_protocol_that_changes_what_is_recorded_bills_the_floor_pre-restating_v57_2026-11-21.lean.
 No declaration is changed. THE RESTATED BYTES ARE NOT RELEASED.
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
source: the author, 2026-11-17 20:04 HST: "yes, thats perect", in answer to "Shall I push those two now and
 then build v52 with them aboard?" The first of the two: the join of the two sentences.
 The sentences, in B06's current wording since revision 2026-11-17.4 (installed 19:11 HST): "A process that
 keeps no record changes nothing that is recorded. Every record a protocol keeps is the record of some
 tested distinction or family of tested distinctions, and is used for it."
 Consulted before typing. Paper 1 Supplement v9.28: Remark "Per-transition reading" (1674): the relation
 of the per-distinction floor to its per-realignment counterpart is "hypothesis-to-hypothesis, not
 derivation"; Definition of realignment cost, protocol axiom P4 (1899): "Per-realignment floor
 (hypothesis)". Codebank: class_transition.py check_T_realignment_floor_is_epsilon_star ("Reading
 identification"; "It does not derive the identification"; grade P_structural_reading);
 cost_energy_identity.py check_T_realignment_cost_is_transition_energy; core.py:1851 (the ledger books
 "transition commitments and per-activation charges only"). Existing Lean: both halves are on file.
 Thm_APFPaper5_K2_a_free_process_changes_nothing_recorded (pass 109):
 change_of_what_is_recorded_needs_a_record, and change_of_what_is_recorded_costs_the_floor under the
 floor by records taken as a hypothesis on all words. Thm_APFPaper1_the_sentence_on_records_with_joint_
 records (pass 113): bill_ge_floor_of_keeping_a_record_family, on source data.
 Thm_APFPaper1_keeping_a_record_costs_the_floor_under_the_ruling (pass 111): the same for protocols on
 words, under the earlier typing. The join was not typed.
consumes_inputs: as hypotheses, in the forms this seat has typed and no node declares:
 - B06's first new sentence, as APFPaper5.K2.RecordedSideStill (closed words, listed distinctions);
 - B06's second new sentence, as APFPaper1.Source.EveryRecordIsNeededForATestedFamily (the family
   reading; NOT RULED as the typing);
 - B05's declared form (APFB05.MarginalFloor); "Holding nothing costs nothing" (HoldingNothingFree).
 Three conditions are NOT inputs:
 - a protocol maintains what its fragments keep: the author's ruling of 2026-11-17 09:14 HST, a ruling
   and not an input;
 - NothingSufficesWithoutARecord: the empty set of records is sufficient for no distinction. This
   seat's. NOT RULED;
 - a uniform positive lower bound on the costs of single distinctions. This seat's. NOT RULED. With
   finitely many distinctions it follows from B03's declared form (uniform_singleton_cost_of_finite).
statement:
 - (NarrowOnWords.protocol_that_keeps_a_record_bills_the_floor_family) pass 111's theorem for protocols
   on words, under the family reading: a protocol whose fragments keep a record bills at least eps.
 - (protocol_that_changes_what_is_recorded_bills_the_floor) a closed word that is a protocol, and after
   which the held family of a state is not what it was, bills at least eps.
 - (protocol_that_changes_a_reading_bills_the_floor) the same for a single listed distinction that
   reads otherwise after the word.
what it shows: on the recorded side and for protocols, the per-realignment floor that the Supplement
 states as a hypothesis follows from the inputs at revision 2026-11-17.4 with the three conditions above.
not claimed:
 - That the typed forms are the declared forms; the builder seat declares forms. That the two unruled
   conditions hold.
 - Anything for a process that is not a protocol, for a process between two contexts, or for what is not
   recorded. That the floor eps here is the Supplement's epsilon_min: the identification is a reading
   there, and is not made here.
 - That some protocol changes what is recorded. No supplied world on file has one: in the readings
   world no word moves a state.
 - That Paper 5's K2 or K3 is discharged. Anything about orientation, the carriers or Born.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_RecordedSideStill
import Theorems.Thm_APFPaper5_K2_change_of_what_is_recorded_needs_a_record
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper1.Source
section
variable {D P R Record : Type*}
variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
/-- Holding nothing is free: some protocol keeps no record and bills nothing. -/
def HoldingNothingFree_p2mProofCtx : Prop :=
  ∃ p0 : P, maintained p0 = ∅ ∧ (calibration (wholeResource p0) : ℝ) = 0

/-- The empty set of records is sufficient for no distinction. NOT RULED. -/
def NothingSufficesWithoutARecord_p2mProofCtx : Prop :=
  ∀ (p : P) (d : D), ¬ sufficient p ∅ d

/-- The author's sentence of 2026-11-17 16:03 HST with his ruling of 18:25 HST that joint records count,
typed: every record a protocol maintains is kept for some nonempty family of tested distinctions,
within capacity, that the protocol serves, and no protocol that maintains only its other records serves that
family. NOT RULED as the typing. -/
def EveryRecordIsNeededForATestedFamily_p2mProofCtx (tested : D → Prop) (C : ℝ) : Prop :=
  ∀ (p : P) (r : Record), r ∈ maintained p → ∃ S : Finset D, S.Nonempty ∧ (∀ d ∈ S, tested d) ∧
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S ∧
    (∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ∧
    ∀ q : P, maintained q ⊆ maintained p \ {r} →
      ¬ ∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma

/-- What pass 111 uses of the sentence: a protocol that maintains a record serves some tested
distinction that is within capacity alone. -/
def EveryKeeperServesATestedDistinction_p2mProofCtx (tested : D → Prop) (C : ℝ) : Prop :=
  ∀ p : P, (maintained p).Nonempty → ∃ d : D, tested d ∧
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C {d} ∧
    ∃ sigma : Set Record, sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma
end
end APFPaper1.Source

namespace APFPaper1.Source
theorem familyCost_le_bill {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) (p : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
      (calibration (wholeResource p) : ℝ) :=
  csInf_le ⟨0, by rintro c ⟨q, _, rfl⟩; exact NNReal.coe_nonneg _⟩ ⟨p, hp, rfl⟩
end APFPaper1.Source

set_option autoImplicit false
namespace APFPaper1.Source
section
variable {D P R Record : Type*}
variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
/-- The family of no distinctions costs nothing. -/
theorem familyCost_empty_eq_zero (h : HoldingNothingFree_p2mProofCtx wholeResource calibration maintained) :
    familyCost wholeResource calibration maintained sufficient usesToRealize (∅ : Finset D) = 0 := by
  obtain ⟨p0, _, hb⟩ := h
  apply le_antisymm
  · have h1 : familyCost wholeResource calibration maintained sufficient usesToRealize
        (∅ : Finset D) ≤ (calibration (wholeResource p0) : ℝ) :=
      csInf_le ⟨0, by rintro c ⟨q, _, rfl⟩; exact NNReal.coe_nonneg _⟩
        ⟨p0, fun d hd => by simp at hd, rfl⟩
    rw [hb] at h1
    exact h1
  · exact familyCost_nonneg wholeResource calibration maintained sufficient usesToRealize ∅

/-- With the declared B05 and holding nothing free: a tested distinction that is support-novel over
nothing, and within capacity alone, costs at least eps. -/
theorem individual_floor_of_holding_nothing_free [DecidableEq D] (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (hfree : HoldingNothingFree_p2mProofCtx wholeResource calibration maintained) (hC : 0 ≤ C)
    (d : D) (ht : tested d)
    (hd : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C {d})
    (hnov : supportNovel wholeResource calibration maintained sufficient usesToRealize ∅ d) :
    eps ≤ familyCost wholeResource calibration maintained sufficient usesToRealize {d} := by
  obtain ⟨_, hfl⟩ := hB05 ()
  have h0 := familyCost_empty_eq_zero wholeResource calibration maintained sufficient usesToRealize
    hfree
  have hadm0 : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (∅ : Finset D) := by
    obtain ⟨p0, _, _⟩ := hfree
    exact ⟨⟨p0, fun e he => by simp at he⟩, by rw [h0]; exact hC⟩
  have hd' : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (insert d ∅) := by
    simpa using hd
  have hgap := hfl ∅ d ht hadm0 hd' hnov
  have hins : (insert d (∅ : Finset D)) = {d} := by simp
  rw [hins, h0, sub_zero] at hgap
  exact hgap

/-- The family reading gives it. -/
theorem keeper_serves_of_family (tested : D → Prop) (C : ℝ)
    (h : EveryRecordIsNeededForATestedFamily_p2mProofCtx wholeResource calibration maintained sufficient
      usesToRealize tested C) :
    EveryKeeperServesATestedDistinction_p2mProofCtx wholeResource calibration maintained sufficient
      usesToRealize tested C := by
  rintro p ⟨r, hr⟩
  obtain ⟨S, ⟨e, he⟩, ht, hadm, hserve, _⟩ := h p r hr
  refine ⟨e, ht e he, ⟨⟨p, fun d hd => ?_⟩, ?_⟩, hserve e he⟩
  · rw [Finset.mem_singleton.mp hd]
    exact hserve e he
  · exact le_trans (familyCost_mono wholeResource calibration maintained sufficient
      usesToRealize (Finset.singleton_subset_iff.mpr he) hadm.1) hadm.2

/-- Pass 111's first theorem under the weaker hypothesis: every distinction is support-novel over the
empty family. -/
theorem supportNovel_empty_of_keeper_serves (tested : D → Prop) (C : ℝ)
    (hfree : HoldingNothingFree_p2mProofCtx wholeResource calibration maintained)
    (hK : EveryKeeperServesATestedDistinction_p2mProofCtx wholeResource calibration maintained sufficient
      usesToRealize tested C)
    (hnon : NothingSufficesWithoutARecord_p2mProofCtx (P := P) sufficient)
    (hunif : ∃ eta : ℝ, 0 < eta ∧ ∀ d : D,
      eta ≤ familyCost wholeResource calibration maintained sufficient usesToRealize {d})
    (d : D) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize ∅ d := by
  have h0 := familyCost_empty_eq_zero wholeResource calibration maintained sufficient usesToRealize
    hfree
  obtain ⟨eta, hpos, hle⟩ := hunif
  refine ⟨eta / 2, half_pos hpos, ?_⟩
  intro q _ hbill
  rintro ⟨sigma, hsub, hsuff⟩
  rw [h0, zero_add] at hbill
  by_cases hm : (maintained q).Nonempty
  · obtain ⟨e, _, _, s, hs, hsf, hu⟩ := hK q hm
    have hserve : ∀ e' ∈ ({e} : Finset D), ∃ s' : Set Record,
        s' ⊆ maintained q ∧ sufficient q s' e' ∧ usesToRealize q e' s' := by
      intro e' he'
      rw [Finset.mem_singleton.mp he']
      exact ⟨s, hs, hsf, hu⟩
    have h1 := familyCost_le_bill wholeResource calibration maintained sufficient usesToRealize {e}
      q hserve
    have h2 := hle e
    linarith
  · have hempty : maintained q = ∅ := Set.not_nonempty_iff_eq_empty.mp hm
    rw [hempty] at hsub
    have hsig : sigma = ∅ := Set.subset_empty_iff.mp hsub
    rw [hsig] at hsuff
    exact hnon q d hsuff

/-- Pass 111's second theorem under the weaker hypothesis: every protocol that maintains a record bills
at least eps. -/
theorem bill_ge_floor_of_keeper_serves [DecidableEq D] (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (hfree : HoldingNothingFree_p2mProofCtx wholeResource calibration maintained) (hC : 0 ≤ C)
    (hK : EveryKeeperServesATestedDistinction_p2mProofCtx wholeResource calibration maintained sufficient
      usesToRealize tested C)
    (hnon : NothingSufficesWithoutARecord_p2mProofCtx (P := P) sufficient)
    (hunif : ∃ eta : ℝ, 0 < eta ∧ ∀ d : D,
      eta ≤ familyCost wholeResource calibration maintained sufficient usesToRealize {d})
    (p : P) (hne : (maintained p).Nonempty) :
    eps ≤ (calibration (wholeResource p) : ℝ) := by
  obtain ⟨d, ht, hd, sigma, hsub, hsuff, hu⟩ := hK p hne
  have hnov := supportNovel_empty_of_keeper_serves wholeResource calibration maintained sufficient
    usesToRealize tested C hfree hK hnon hunif d
  have hfl := individual_floor_of_holding_nothing_free wholeResource calibration maintained
    sufficient usesToRealize tested C eps hB05 hfree hC d ht hd hnov
  have hserve : ∀ e ∈ ({d} : Finset D), ∃ s : Set Record,
      s ⊆ maintained p ∧ sufficient p s e ∧ usesToRealize p e s := by
    intro e he
    rw [Finset.mem_singleton.mp he]
    exact ⟨sigma, hsub, hsuff, hu⟩
  exact le_trans hfl (familyCost_le_bill wholeResource calibration maintained sufficient
    usesToRealize {d} p hserve)

/-- The floor on keeping a record under the family reading. -/
theorem bill_ge_floor_of_keeping_a_record_family [DecidableEq D] (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (hfree : HoldingNothingFree_p2mProofCtx wholeResource calibration maintained) (hC : 0 ≤ C)
    (hF : EveryRecordIsNeededForATestedFamily_p2mProofCtx wholeResource calibration maintained sufficient
      usesToRealize tested C)
    (hnon : NothingSufficesWithoutARecord_p2mProofCtx (P := P) sufficient)
    (hunif : ∃ eta : ℝ, 0 < eta ∧ ∀ d : D,
      eta ≤ familyCost wholeResource calibration maintained sufficient usesToRealize {d})
    (p : P) (hne : (maintained p).Nonempty) :
    eps ≤ (calibration (wholeResource p) : ℝ) :=
  bill_ge_floor_of_keeper_serves wholeResource calibration maintained sufficient usesToRealize tested
    C eps hB05 hfree hC
    (keeper_serves_of_family wholeResource calibration maintained sufficient usesToRealize tested C
      hF)
    hnon hunif p hne
end
end APFPaper1.Source

set_option autoImplicit false

open APFPaper1.Continuation APFPaper1.Source

namespace APFPaper1.NarrowOnWords

universe uC uF uK
variable {Context : Type uC} {Frag : Context → Context → Type uF}
  {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]

/-- The floor on keeping a record, for protocols on words, under the family reading: where a protocol
maintains what its fragments keep, every protocol whose fragments keep a record bills at least eps. -/
theorem protocol_that_keeps_a_record_bills_the_floor_family_p2mProof (g : Context)
    {R D : Type*} [DecidableEq D]
    (protocols : Set (WordFrom Frag g))
    (resource : WordFrom Frag g → R) (calibration : R → NNReal)
    (maintained : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g))
    (sufficient : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g) → D → Prop)
    (usesToRealize : {p : WordFrom Frag g // p ∈ protocols} → D → Set (Rec g) → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (tested : D → Prop) (C eps : ℝ)
    (hmaint : ∀ p : {p : WordFrom Frag g // p ∈ protocols},
      maintained p = (↑(keptByFragments keptFrag g p.val.2) : Set (Rec g)))
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D)
      (P := fun _ => {p : WordFrom Frag g // p ∈ protocols})
      (R := fun _ => R) (Record := fun _ => Rec g) (fun _ p => resource p.val)
      (fun _ => calibration) (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize)
      (fun _ => tested) (fun _ => C) (fun _ => eps))
    (hfree : HoldingNothingFree_p2mProofCtx
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained)
    (hC : 0 ≤ C)
    (hF : EveryRecordIsNeededForATestedFamily_p2mProofCtx
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
      sufficient usesToRealize tested C)
    (hnon : NothingSufficesWithoutARecord_p2mProofCtx
      (P := {p : WordFrom Frag g // p ∈ protocols}) sufficient)
    (hunif : ∃ eta : ℝ, 0 < eta ∧ ∀ d : D, eta ≤ familyCost
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
      sufficient usesToRealize {d})
    (p : {p : WordFrom Frag g // p ∈ protocols})
    (hk : keptByFragments keptFrag g p.val.2 ≠ ∅) :
    eps ≤ (calibration (resource p.val) : ℝ) := by
  have hne : (maintained p).Nonempty := by
    rw [hmaint p]
    exact Finset.coe_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr hk)
  exact bill_ge_floor_of_keeping_a_record_family
    (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
    sufficient usesToRealize tested C eps hB05 hfree hC hF hnon hunif p hne

end APFPaper1.NarrowOnWords

namespace APFPaper5.K2

open APFPaper1.NarrowOnWords

universe uC uF uX uK uD
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)] {Dn : Context → Type uD}

/-- The two sentences joined. With the recorded side still, the family reading of the sentence on
records, B05's declared form, holding nothing free and the three conditions: a closed word that is a
protocol, and after which the held family of a state is not what it was, bills at least eps. -/
theorem protocol_that_changes_what_is_recorded_bills_the_floor_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hS : RecordedSideStill step keptFrag reads listed)
    (g : Context) {R D : Type*} [DecidableEq D]
    (protocols : Set (WordFrom Frag g))
    (resource : WordFrom Frag g → R) (calibration : R → NNReal)
    (maintained : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g))
    (sufficient : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g) → D → Prop)
    (usesToRealize : {p : WordFrom Frag g // p ∈ protocols} → D → Set (Rec g) → Prop)
    (tested : D → Prop) (C eps : ℝ)
    (hmaint : ∀ p : {p : WordFrom Frag g // p ∈ protocols},
      maintained p = (↑(keptByFragments keptFrag g p.val.2) : Set (Rec g)))
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D)
      (P := fun _ => {p : WordFrom Frag g // p ∈ protocols})
      (R := fun _ => R) (Record := fun _ => Rec g) (fun _ p => resource p.val)
      (fun _ => calibration) (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize)
      (fun _ => tested) (fun _ => C) (fun _ => eps))
    (hfree : HoldingNothingFree_p2mProofCtx
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained)
    (hC : 0 ≤ C)
    (hF : EveryRecordIsNeededForATestedFamily_p2mProofCtx
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
      sufficient usesToRealize tested C)
    (hnon : NothingSufficesWithoutARecord_p2mProofCtx
      (P := {p : WordFrom Frag g // p ∈ protocols}) sufficient)
    (hunif : ∃ eta : ℝ, 0 < eta ∧ ∀ d : D, eta ≤ familyCost
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
      sufficient usesToRealize {d})
    (W : Word Frag g g) (hp : (⟨g, W⟩ : WordFrom Frag g) ∈ protocols) (x y : Raw g)
    (hex : Executes step W x y)
    (hne : heldFamily (reads g) (listed g) y ≠ heldFamily (reads g) (listed g) x) :
    eps ≤ (calibration (resource ⟨g, W⟩) : ℝ) :=
  protocol_that_keeps_a_record_bills_the_floor_family_p2mProof g protocols resource calibration maintained
    sufficient usesToRealize keptFrag tested C eps hmaint hB05 hfree hC hF hnon hunif
    ⟨⟨g, W⟩, hp⟩
    (change_of_what_is_recorded_needs_a_record step keptFrag reads listed hS g W x y hex hne)

/-- The same for one listed distinction: a closed word that is a protocol, and after which a listed
distinction reads otherwise than before, bills at least eps. -/
theorem protocol_that_changes_a_reading_bills_the_floor_p2mProof
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool) (listed : (g : Context) → Finset (Dn g))
    (hS : RecordedSideStill step keptFrag reads listed)
    (g : Context) {R D : Type*} [DecidableEq D]
    (protocols : Set (WordFrom Frag g))
    (resource : WordFrom Frag g → R) (calibration : R → NNReal)
    (maintained : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g))
    (sufficient : {p : WordFrom Frag g // p ∈ protocols} → Set (Rec g) → D → Prop)
    (usesToRealize : {p : WordFrom Frag g // p ∈ protocols} → D → Set (Rec g) → Prop)
    (tested : D → Prop) (C eps : ℝ)
    (hmaint : ∀ p : {p : WordFrom Frag g // p ∈ protocols},
      maintained p = (↑(keptByFragments keptFrag g p.val.2) : Set (Rec g)))
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D)
      (P := fun _ => {p : WordFrom Frag g // p ∈ protocols})
      (R := fun _ => R) (Record := fun _ => Rec g) (fun _ p => resource p.val)
      (fun _ => calibration) (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize)
      (fun _ => tested) (fun _ => C) (fun _ => eps))
    (hfree : HoldingNothingFree_p2mProofCtx
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained)
    (hC : 0 ≤ C)
    (hF : EveryRecordIsNeededForATestedFamily_p2mProofCtx
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
      sufficient usesToRealize tested C)
    (hnon : NothingSufficesWithoutARecord_p2mProofCtx
      (P := {p : WordFrom Frag g // p ∈ protocols}) sufficient)
    (hunif : ∃ eta : ℝ, 0 < eta ∧ ∀ d : D, eta ≤ familyCost
      (fun p : {p : WordFrom Frag g // p ∈ protocols} => resource p.val) calibration maintained
      sufficient usesToRealize {d})
    (W : Word Frag g g) (hp : (⟨g, W⟩ : WordFrom Frag g) ∈ protocols) (x y : Raw g)
    (hex : Executes step W x y) (d : Dn g) (hd : d ∈ listed g)
    (hne : reads g d y ≠ reads g d x) :
    eps ≤ (calibration (resource ⟨g, W⟩) : ℝ) :=
  protocol_that_keeps_a_record_bills_the_floor_family_p2mProof g protocols resource calibration maintained
    sufficient usesToRealize keptFrag tested C eps hmaint hB05 hfree hC hF hnon hunif
    ⟨⟨g, W⟩, hp⟩
    (fun hk => hne (hS g W x y d hk hex hd))

end APFPaper5.K2


universe apfNative_uC apfNative_uF apfNative_uK apfNative_u_1 apfNative_u_2
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Rec : Context → Type apfNative_uK}
  [inst : (g : Context) → DecidableEq.{apfNative_uK + 1} (Rec g)] (g : Context) {R : Type apfNative_u_1}
  {D : Type apfNative_u_2} [inst_1 : DecidableEq.{apfNative_u_2 + 1} D]
  (protocols :
    Set.{max apfNative_uF apfNative_uC} (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
  (resource : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R)
  (calibration : R → NNReal)
  (maintained :
    (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p) →
      Set.{apfNative_uK} (Rec g))
  (sufficient :
    (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p) →
      Set.{apfNative_uK} (Rec g) → D → Prop)
  (usesToRealize :
    (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p) →
      D → Set.{apfNative_uK} (Rec g) → Prop)
  (keptFrag : (g h k : Context) → Frag h k → Finset.{apfNative_uK} (Rec g)) (tested : D → Prop) (C eps : Real)
  (hmaint :
    ∀
      (p :
        @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
          @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (Set.{max apfNative_uF apfNative_uC}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            (@Set.instMembership.{max apfNative_uC apfNative_uF}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            protocols p),
      @Eq.{apfNative_uK + 1} (Set.{apfNative_uK} (Rec g)) (maintained p)
        (@SetLike.coe.{apfNative_uK, apfNative_uK} (Finset.{apfNative_uK} (Rec g)) (Rec g)
          (@Finset.instSetLike.{apfNative_uK} (Rec g))
          (@APFPaper1.Continuation.keptByFragments.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst
            keptFrag g g
            (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
              (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h)
              (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                  @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                    (Set.{max apfNative_uF apfNative_uC}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    (@Set.instMembership.{max apfNative_uC apfNative_uF}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    protocols p)
                p))
            (@Sigma.snd.{apfNative_uC, max apfNative_uC apfNative_uF} Context
              (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h)
              (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                  @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                    (Set.{max apfNative_uF apfNative_uC}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    (@Set.instMembership.{max apfNative_uC apfNative_uF}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                    protocols p)
                p)))))
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_u_1, apfNative_uK} Unit
      (fun (x : Unit) => D)
      (fun (x : Unit) =>
        @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
          @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (Set.{max apfNative_uF apfNative_uC}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            (@Set.instMembership.{max apfNative_uC apfNative_uF}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
            protocols p)
      (fun (x : Unit) => R) (fun (x : Unit) => Rec g) (fun (g : Unit) => inst_1)
      (fun (x : Unit)
          (p :
            @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
              fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p) =>
        resource
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p))
      (fun (x : Unit) => calibration) (fun (x : Unit) => maintained) (fun (x : Unit) => sufficient)
      (fun (x : Unit) => usesToRealize) (fun (x : Unit) => tested) (fun (x : Unit) => C) fun (x : Unit) => eps)
  (hfree :
    @APFPaper1.Source.HoldingNothingFree_p2mProofCtx.{max apfNative_uC apfNative_uF, apfNative_u_1, apfNative_uK}
      (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p)
      R (Rec g)
      (fun
          (p :
            @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
              fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p) =>
        resource
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p))
      calibration maintained)
  (hC : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
  (hF :
    @APFPaper1.Source.EveryRecordIsNeededForATestedFamily_p2mProofCtx.{apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_u_1,
          apfNative_uK}
      D
      (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p)
      R (Rec g)
      (fun
          (p :
            @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
              (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
              fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p) =>
        resource
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p))
      calibration maintained sufficient usesToRealize tested C)
  (hnon :
    @APFPaper1.Source.NothingSufficesWithoutARecord_p2mProofCtx.{apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_uK} D
      (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
        @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
          (Set.{max apfNative_uF apfNative_uC}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          (@Set.instMembership.{max apfNative_uC apfNative_uF}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
          protocols p)
      (Rec g) sufficient)
  (hunif :
    @Exists.{1} Real fun (eta : Real) =>
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eta)
        (∀ (d : D),
          @LE.le.{0} Real Real.instLE eta
            (@APFPaper1.Source.familyCost.{apfNative_u_2, max apfNative_uC apfNative_uF, apfNative_u_1, apfNative_uK} D
              (@Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                  (Set.{max apfNative_uF apfNative_uC}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                  (@Set.instMembership.{max apfNative_uC apfNative_uF}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                  protocols p)
              R (Rec g)
              (fun
                  (p :
                    @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                      fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                      @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                        (Set.{max apfNative_uF apfNative_uC}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        (@Set.instMembership.{max apfNative_uC apfNative_uF}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        protocols p) =>
                resource
                  (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                    (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
                      @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                        (Set.{max apfNative_uF apfNative_uC}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        (@Set.instMembership.{max apfNative_uC apfNative_uF}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                        protocols p)
                    p))
              calibration maintained sufficient usesToRealize
              (@Singleton.singleton.{apfNative_u_2, apfNative_u_2} D (Finset.{apfNative_u_2} D)
                (@Finset.instSingleton.{apfNative_u_2} D) d))))
  (p :
    @Subtype.{max (apfNative_uC + 1) (apfNative_uF + 1)}
      (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
      fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
      @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
        (Set.{max apfNative_uF apfNative_uC}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
        (@Set.instMembership.{max apfNative_uC apfNative_uF}
          (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
        protocols p)
  (hk :
    @Ne.{apfNative_uK + 1} (Finset.{apfNative_uK} (Rec g))
      (@APFPaper1.Continuation.keptByFragments.{apfNative_uC, apfNative_uF, apfNative_uK} Context Frag Rec inst keptFrag
        g g
        (@Sigma.fst.{apfNative_uC, max apfNative_uC apfNative_uF} Context
          (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h)
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p))
        (@Sigma.snd.{apfNative_uC, max apfNative_uC apfNative_uF} Context
          (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h)
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p)))
      (@EmptyCollection.emptyCollection.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
        (@Finset.instEmptyCollection.{apfNative_uK} (Rec g)))),
  @LE.le.{0} Real Real.instLE eps
    (NNReal.toReal
      (calibration
        (resource
          (@Subtype.val.{max (apfNative_uC + 1) (apfNative_uF + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g) =>
              @Membership.mem.{max apfNative_uC apfNative_uF, max apfNative_uC apfNative_uF}
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
                (Set.{max apfNative_uF apfNative_uC}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                (@Set.instMembership.{max apfNative_uC apfNative_uF}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g))
                protocols p)
            p)))) := by
  exact @APFPaper1.NarrowOnWords.protocol_that_keeps_a_record_bills_the_floor_family_p2mProof
