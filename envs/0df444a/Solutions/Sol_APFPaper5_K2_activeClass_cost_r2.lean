-- Prove2me | solution 1 for APFPaper5.K2.activeClass_cost_r2
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:58:24.896013+00:00
-- url     : https://prove2.me/submissions/06a967fe-fde1-4308-aadd-987a9ea6269b

/-
CUT 2026-11-17 by the seat that wrote this file, on the author's word of 03:12 HST, "then let's bolt k2 to spine"
(RULING_K2s_recorded_side_goes_on_the_spine_2026-11-17), read as covering the cut on the precedent of K1 (his "Yes" of 2026-11-16 11:20 HST).
Only this block is new. The original header below it is unchanged. The code is unchanged except as this
block says. Where the original header differs from this block, this block governs. Pre-cut copy:
Old/Thm_APFPaper5_K2_state_class_candidates_pre-cut_2026-11-17.lean, sha256
72423d5f7c1afb45e6a16aeca09a021c2de8dc1cacc91a639ea111660cfd570c (the file released on 2026-11-15 and reported
uploaded).
 - MOVED OUT, unchanged: ind_mul_self, keptClass_cost and keptClass_union_of_disjoint, to
   Theorems/Thm_APFPaper5_K2_kept_class_cost. They are about the ruled candidate C. This file imports that
   one, so everything the original header lists is still in scope here.
 - Import line added: Thm_APFPaper5_K2_kept_class_cost.
 - Left here, unchanged: nine theorems. Two say that K1's table is an overlap of record lists; four are on
   candidate A and two on candidate B, which the author did NOT choose; one is a fact about truth values.
   This file is a reference record. It is not part of what goes on the spine.
 - Still a DRAFT at this hash: not gated, not reviewed, not released, not built in the ledger repo, not
   built on the build machine.
 - Unchanged: no lane; no claim that the transfer is forced, that the carrier gap is closed or narrowed, or
   that Born is derived.

APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_state_class_candidates
title: What each candidate for "what a state holds" costs: under holds, under a turn-over, and in the cost it gives what is held
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 e3447355703d07a13854a5f7a023cfa63673c711744b404a35e9a1627c00ee9f), kept in Old/ as
 Thm_APFPaper5_K2_state_class_candidates_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE
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
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: TEE_UP_K2_what_a_state_holds_2026-11-15; Def_APFPaper5_K2_StateClass (the three candidates); Def_APFPaper5_K2_HoldScore (RearrangesFamily, heldAfter); the builder seat's
 Def_APFPaper5_K1_MarkTable and Def_APFPaper5_K1_PartyScore.
standing: EVIDENCE put to the author before the ruling of 2026-11-15 13:54 HST, which took C for what is
 recorded (RULING_C_for_what_is_recorded_2026-11-15). A and B were not chosen. Every statement is ordinary
 mathematics on the typed candidates and is unchanged by the ruling.
consumes_inputs: none.
theorems:
 - (atomTable_eq_recordForm, tableForm_atomTable_eq_recordForm) K1's table is the weighted overlap of the
   distinctions' record lists, and K1's form of two classes of distinctions is the weighted overlap of the
   classes of records they stand for.
 - Candidate A.
   (activeClass_after_hold_of_no_turn) under a hold that turns nothing over, what the state holds after the
   hold is what the hold makes of what it held.
   (activeClass_after_turn) on a distinction the hold turns over, it is one minus that. Not linear.
   (activeClass_cost) the cost K1's form gives the class is, record by record, the record's cost times the
   square of the number of true distinctions listed against it.
   (shared_record_counts_four) two distinctions listed against one record of cost 1, both true: the class
   costs 4. The family keeps one record of cost 1.
 - Candidate B.
   (sideClass_after_hold) under any hold, turn-overs included, the class after the hold is what the hold
   makes of the class before, with a change of sign on each distinction turned over. Linear.
   (opposite_sides_cancel) two distinctions listed against one record of cost 1, on opposite sides: the class
   is not zero and costs 0.
 - Candidate C.
   (keptClass_cost) the weighted overlap of the class with itself is the cost of the records the family
   keeps: the ledger's cost of what is held, exactly.
   (keptClass_union_of_disjoint) for a keeping rule that keeps a record for a union exactly when it keeps
   it for one of the two, and two families that keep no record in common, the class of the union is the
   sum of the two classes.
not claimed: that A or B is what a state holds. Anything about what a state holds that is not recorded. That
 a turn-over is or is not to be seen. Anything about tests. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_StateClass_r2
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_ind_mul_self
import Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uX uD uW
variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}

theorem ind_xor_true (b : Bool) : ind (xor true b) = 1 - ind b := by
  cases b <;> simp [ind]

/-! ### K1's table is an overlap of record lists -/

theorem atomTable_eq_recordForm_p2mProof [Fintype W] (w : W → ℝ) (mark : ι → W → Bool) (i j : ι) :
    atomTable w mark i j = recordForm w (partyClass mark i) (partyClass mark j) := rfl

theorem tableForm_atomTable_eq_recordForm_p2mProof [Fintype ι] [Fintype W] (w : W → ℝ)
    (mark : ι → W → Bool) (x y : ι → ℝ) :
    tableForm (atomTable w mark) x y = recordForm w (markLift mark x) (markLift mark y) := by
  have h1 : ∀ a, w a * ((∑ i, x i * ind (mark i a)) * (∑ j, y j * ind (mark j a))) =
      ∑ i, ∑ j, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j := by
    intro a
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have h2 : ∀ i j, x i * (∑ a, w a * (ind (mark i a) * ind (mark j a))) * y j =
      ∑ a, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j := by
    intro i j
    rw [Finset.mul_sum, Finset.sum_mul]
  show (∑ i, ∑ j, x i * (∑ a, w a * (ind (mark i a) * ind (mark j a))) * y j) =
    ∑ a, w a * ((∑ i, x i * ind (mark i a)) * (∑ j, y j * ind (mark j a)))
  simp only [h1, h2]
  calc (∑ i, ∑ j, ∑ a, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j)
      = ∑ i, ∑ a, ∑ j, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ a, ∑ i, ∑ j, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j := Finset.sum_comm

/-! ### Candidate A: the distinctions that read true, added up -/

theorem activeClass_after_hold_of_no_turn_p2mProof (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
    (hno : ∀ i, flip i = false) (x : X) :
    activeClass reads dist (h x) = heldAfter sigma (activeClass reads dist x) := by
  funext i
  show ind (reads (dist i) (h x)) = ind (reads (dist (sigma i)) x)
  rw [r i x, hno i, Bool.false_xor]

theorem activeClass_after_turn_p2mProof (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
    (i : ι) (hi : flip i = true) (x : X) :
    activeClass reads dist (h x) i = 1 - heldAfter sigma (activeClass reads dist x) i := by
  show ind (reads (dist i) (h x)) = 1 - ind (reads (dist (sigma i)) x)
  rw [r i x, hi, ind_xor_true]

/-- The cost K1's form gives the class: record by record, the record's cost times the square of the number
of true distinctions listed against it. -/
theorem activeClass_cost_p2mProof [Fintype ι] [Fintype W] (w : W → ℝ) (mark : ι → W → Bool)
    (reads : D → X → Bool) (dist : ι → D) (x : X) :
    tableForm (atomTable w mark) (activeClass reads dist x) (activeClass reads dist x) =
      ∑ a, w a * ((∑ i, ind (reads (dist i) x) * ind (mark i a)) *
        (∑ i, ind (reads (dist i) x) * ind (mark i a))) :=
  tableForm_atomTable_eq_recordForm_p2mProof w mark _ _

/-- Two distinctions listed against one record of cost 1, both true: the class costs 4. -/
theorem shared_record_counts_four_p2mProof :
    tableForm (atomTable (fun _ : Unit => (1 : ℝ)) (fun (_ : Bool) (_ : Unit) => true))
      (fun _ => 1) (fun _ => 1) = 4 := by
  rw [tableForm_atomTable_eq_recordForm_p2mProof]
  simp [recordForm, markLift, ind]
  norm_num

/-! ### Candidate B: the side of each distinction -/

theorem sideClass_after_hold_p2mProof (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
    (i : ι) (x : X) :
    sideClass reads dist (h x) i =
      (if flip i then (-1 : ℝ) else 1) * heldAfter sigma (sideClass reads dist x) i := by
  show (if reads (dist i) (h x) then (1 : ℝ) else -1) =
    (if flip i then (-1 : ℝ) else 1) * (if reads (dist (sigma i)) x then (1 : ℝ) else -1)
  rw [r i x]
  cases flip i <;> cases reads (dist (sigma i)) x <;> simp

/-- Two distinctions listed against one record of cost 1, on opposite sides: the class is not zero and
costs 0. -/
theorem opposite_sides_cancel_p2mProof :
    tableForm (atomTable (fun _ : Unit => (1 : ℝ)) (fun (_ : Bool) (_ : Unit) => true))
      (fun b : Bool => if b then 1 else -1) (fun b : Bool => if b then 1 else -1) = 0 := by
  rw [tableForm_atomTable_eq_recordForm_p2mProof]
  simp [recordForm, markLift, ind]

end APFPaper5.K2


universe apfNative_uI apfNative_uX apfNative_uD apfNative_uW
theorem solution :
∀ {ι : Type apfNative_uI} {X : Type apfNative_uX} {D : Type apfNative_uD} {W : Type apfNative_uW}
  [inst : Fintype.{apfNative_uI} ι] [inst_1 : Fintype.{apfNative_uW} W] (w : W → Real) (mark : ι → W → Bool)
  (reads : D → X → Bool) (dist : ι → D) (x : X),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_uI} ι inst
      (@APFPaper5.K1.atomTable.{apfNative_uI, apfNative_uW} ι W inst_1 w mark)
      (@APFPaper5.K2.activeClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist x)
      (@APFPaper5.K2.activeClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist x))
    (@Finset.sum.{apfNative_uW, 0} W Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uW} W inst_1) fun (a : W) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (w a)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Finset.sum.{apfNative_uI, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uI} ι inst)
            fun (i : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K1.ind (reads (dist i) x))
              (APFPaper5.K1.ind (mark i a)))
          (@Finset.sum.{apfNative_uI, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uI} ι inst)
            fun (i : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K1.ind (reads (dist i) x))
              (APFPaper5.K1.ind (mark i a))))) := by
  exact @APFPaper5.K2.activeClass_cost_p2mProof
