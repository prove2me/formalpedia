-- Prove2me | solution 1 for APFPaper5.K2.stillHeldAfter_of_isHold
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T16:06:22.695606+00:00
-- url     : https://prove2.me/submissions/7a5ab462-3b22-4647-89d9-9a7fd8c7d4ca

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not bundled, not built in the ledger repo, not built on the build
 machine)
name: APFPaper5_K2_hold_as_defined
title: For a hold as defined: doing nothing is a hold and holds compose; a hold draws nothing; with B02's second sentence it leaves B02 true, and that is exactly what its rearrangement being one-to-one says; and it keeps K1's ledger
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 49e587a036278b3ad157345486209b67be4286471def0481ad69143e16aa9854), kept in Old/ as
 Thm_APFPaper5_K2_hold_as_defined_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED
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
ruling: the author, 2026-11-16 15:09 HST, call 8 of the afternoon tee-up
 (RULING_calls_5_to_12_as_advised_2026-11-16). Def_APFPaper5_K2_Hold.
source: CONSULTED FIRST. Paper 5 Supplement v7.33:396-420 (the score with a process in the channel;
 orientation closure), 3042-3048 (K2). The builder seat's Def_APFB02_HoldOnDistinctions (NothingDrawn,
 StillHeldAfter: the two hold readings ruled 2026-11-14 11:33 HST) and Def_APFB02_EachTakesBothSides
 (EveryCombinationHeld: B02's second sentence, in the inputs since revision 2026-11-14.1). This seat's
 Thm_APFPaper5_K2_hold_score (rearrangesFamily_id, rearrangesFamily_comp, nothingDrawn_of_rearranges),
 Thm_APFPaper5_K2_holds_keep_table (keepsTable_id, keepsTable_comp, hold_keeping_table_package) and
 Thm_APFPaper5_K2_hold_words (rearrangement_unique). Codebank: apf/hold_cost_dominance.py (the hold as a
 co-present coherent survey with zero booking until the single commit) and
 apf/commutative_no_unresolved_hold.py (in a commutative algebra the off-diagonal hold content of a state
 is invisible to every observable of the algebra). The codebank's hold is a maintained unresolved hold of
 alternatives; nothing in the codebank types a hold as a rearrangement of distinctions, and nothing here
 identifies the two.
consumes_inputs: B02's second sentence, in stillHeldAfter_of_rearranges_perm and stillHeldAfter_of_isHold,
 as the hypothesis EveryCombinationHeld. The other theorems use no declared input.
theorems:
 - (isHold_id, isHold_comp) doing nothing is a hold; two holds one after the other are a hold, with the two
   rearrangements composed.
 - (nothingDrawn_of_isHold) a hold of all the distinctions of a region draws nothing: the first reading of
   2026-11-14.
 - (stillHeldAfter_of_rearranges_perm, stillHeldAfter_of_isHold) where every combination of sides is held,
   a rearrangement by a permutation leaves every combination of sides held: the second reading of
   2026-11-14, now a theorem from B02's second sentence.
 - (injective_of_rearranges_stillHeldAfter) conversely, a rearrangement that leaves every combination of
   sides held is one-to-one. So on a finite list, "B02 is still true after a hold" and "the rearrangement
   is a permutation" say the same.
 - (isHold_keeps_ledger) for a symmetric table with a faithful nonnegative diagonal, a hold satisfies
   HoldKeepsLedger: it keeps K1's form, its score is K1's form with the inverse on the test side,
   reversing the two ends with the inverse in the channel gives the same score, and it keeps the cost of
   every class.
not claimed:
 - That any word of any world runs as a hold, other than the empty word. That the holds of this seat's
   moving and shared worlds keep K1's table: by inspection they should, and it is not typed.
 - That the reverse of a hold is an admitted word.
 - Anything about what is not recorded, about tests, or about K3.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_Hold
import Definitions.Def_APFB02_EachTakesBothSides
import Definitions.Def_APFB02_HoldOnDistinctions
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_id
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
import Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
import Theorems.Thm_APFPaper5_K2_exists_rearranges_of_nothingDrawn
import Theorems.Thm_APFPaper5_K2_heldAfter_id
import Theorems.Thm_APFPaper5_K2_heldAfter_comp
import Theorems.Thm_APFPaper5_K2_heldAfter_add
import Theorems.Thm_APFPaper5_K2_heldAfter_smul
import Theorems.Thm_APFPaper5_K2_heldAfter_markClass
import Theorems.Thm_APFPaper5_K2_holdScore_id
import Theorems.Thm_APFPaper5_K2_holdScore_marks
import Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
import Theorems.Thm_APFPaper5_K2_holdScore_eq_sum
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
import Theorems.Thm_APFPaper5_K2_keeps_of_reverse_is_inverse
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_iff_keeps
import Theorems.Thm_APFPaper5_K2_tableForm_heldAfter_of_keeps
import Theorems.Thm_APFPaper5_K2_ends_reversed_of_keeps
import Theorems.Thm_APFPaper5_K2_keepsTable_diag
import Theorems.Thm_APFPaper5_K2_not_keepsTable_of_diag_ne
import Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
import Theorems.Thm_APFPaper5_K2_source_hold_score_marks
import Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed
import Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
import Theorems.Thm_APFPaper5_K2_keepsTable_id
import Theorems.Thm_APFPaper5_K2_keepsTable_comp
import Theorems.Thm_APFPaper5_K2_keepsTable_symm
import Theorems.Thm_APFPaper5_K2_hold_keeps_cost
import Theorems.Thm_APFPaper5_K2_holdScoreNull_before
import Theorems.Thm_APFPaper5_K2_holdScoreNull_after_of_keeps
import Theorems.Thm_APFPaper5_K2_holdScoreNull_reverse_of_keeps
import Theorems.Thm_APFPaper5_K2_hold_keeping_table_package
import Theorems.Thm_APFPaper5_K2_source_counted_hold_package
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uX uD
variable {ι : Type uI}

/-! ### Doing nothing, and one hold after another -/

/-- Doing nothing is a hold. -/
theorem isHold_id_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D)
    (G : ι → ι → ℝ) : IsHold reads dist G id (Equiv.refl ι) (fun _ => false) :=
  ⟨rearrangesFamily_id reads dist, keepsTable_id G⟩

/-- Two holds, one after the other, are a hold, with the two rearrangements composed. -/
theorem isHold_comp_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D)
    (G : ι → ι → ℝ) (h₁ h₂ : X → X) (s₁ s₂ : Equiv.Perm ι) (f₁ f₂ : ι → Bool)
    (hh₁ : IsHold reads dist G h₁ s₁ f₁) (hh₂ : IsHold reads dist G h₂ s₂ f₂) :
    IsHold reads dist G (h₂ ∘ h₁) (s₂.trans s₁) (fun i => xor (f₂ i) (f₁ (s₂ i))) :=
  ⟨rearrangesFamily_comp reads dist h₁ h₂ s₁ s₂ f₁ f₂ hh₁.1 hh₂.1,
    keepsTable_comp G s₁ s₂ hh₁.2 hh₂.2⟩

/-! ### The two readings of 2026-11-14 -/

/-- A hold of all the distinctions of a region draws nothing. -/
theorem nothingDrawn_of_isHold_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (G : D → D → ℝ)
    (h : X → X) (sigma : Equiv.Perm D) (flip : D → Bool)
    (hh : IsHold reads id G h sigma flip) : APFB02.NothingDrawn reads h :=
  nothingDrawn_of_rearranges reads h (sigma : D → D) flip hh.1

/-- Where every combination of sides is held, a rearrangement by a permutation leaves every combination
of sides held. -/
theorem stillHeldAfter_of_rearranges_perm_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool)
    (h : X → X) (sigma : Equiv.Perm D) (flip : D → Bool)
    (r : RearrangesFamily reads id h (sigma : D → D) flip)
    (hall : APFB02.EveryCombinationHeld reads) : APFB02.StillHeldAfter reads h := by
  classical
  unfold APFB02.StillHeldAfter APFB02.EveryCombinationHeld
  intro S v
  obtain ⟨x, hx⟩ := hall (S.image sigma) (fun d => xor (flip (sigma.symm d)) (v (sigma.symm d)))
  refine ⟨x, fun e he => ?_⟩
  show reads e (h x) = v e
  have h1 : reads e (h x) = xor (flip e) (reads (sigma e) x) := r e x
  have h2 := hx (sigma e) (Finset.mem_image_of_mem sigma he)
  rw [Equiv.symm_apply_apply] at h2
  rw [h1, h2]
  generalize flip e = a
  generalize v e = b
  cases a <;> cases b <;> rfl

/-- So, with B02's second sentence, a hold of all the distinctions of a region leaves B02's second
sentence true. -/
theorem stillHeldAfter_of_isHold_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (G : D → D → ℝ)
    (h : X → X) (sigma : Equiv.Perm D) (flip : D → Bool)
    (hh : IsHold reads id G h sigma flip) (hall : APFB02.EveryCombinationHeld reads) :
    APFB02.StillHeldAfter reads h :=
  stillHeldAfter_of_rearranges_perm_p2mProof reads h sigma flip hh.1 hall

/-- Conversely: a rearrangement that leaves every combination of sides held is one-to-one. -/
theorem injective_of_rearranges_stillHeldAfter_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool)
    (h : X → X) (sigma : D → D) (flip : D → Bool) (r : RearrangesFamily reads id h sigma flip)
    (hstill : APFB02.StillHeldAfter reads h) : Function.Injective sigma := by
  classical
  intro a b hab
  by_contra hne
  obtain ⟨x, hx⟩ := hstill {a, b} (fun d => if d = a then false else !(xor (flip a) (flip b)))
  have hba : b ≠ a := fun e => hne e.symm
  have ha : reads a (h x) = false := by
    have h0 := hx a (by simp)
    simpa [APFB02.readsAfter] using h0
  have hb : reads b (h x) = !(xor (flip a) (flip b)) := by
    have h0 := hx b (by simp)
    simpa [APFB02.readsAfter, hba] using h0
  have ra : reads a (h x) = xor (flip a) (reads (sigma a) x) := r a x
  have rb : reads b (h x) = xor (flip b) (reads (sigma b) x) := r b x
  rw [← hab] at rb
  rw [ra] at ha
  rw [rb] at hb
  generalize flip a = fa at ha hb
  generalize flip b = fb at ha hb
  generalize reads (sigma a) x = c at ha hb
  cases fa <;> cases fb <;> cases c <;> simp at ha hb

/-! ### What a hold keeps -/

section
variable [Fintype ι]

/-- For a symmetric table with a faithful nonnegative diagonal, a hold keeps K1's ledger. -/
theorem isHold_keeps_ledger_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D)
    (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i)
    (hf : FaithfulNonnegDiagonal (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G)
      (LinearEquiv.refl ℝ (ι → ℝ)))
    (h : X → X) (sigma : Equiv.Perm ι) (flip : ι → Bool) (hh : IsHold reads dist G h sigma flip) :
    HoldKeepsLedger G sigma :=
  hold_keeping_table_package G hG hf sigma hh.2

end

end APFPaper5.K2


universe apfNative_uX apfNative_uD
theorem solution :
∀ {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (G : D → D → Real) (h : X → X)
  (sigma : Equiv.Perm.{apfNative_uD + 1} D) (flip : D → Bool)
  (hh :
    @APFPaper5.K2.IsHold.{apfNative_uD, apfNative_uX, apfNative_uD} D X D reads (@id.{apfNative_uD + 1} D) G h sigma
      flip)
  (hall : @APFB02.EveryCombinationHeld.{apfNative_uX, apfNative_uD} X D reads),
  @APFB02.StillHeldAfter.{apfNative_uX, apfNative_uD} X D reads h := by
  exact @APFPaper5.K2.stillHeldAfter_of_isHold_p2mProof
