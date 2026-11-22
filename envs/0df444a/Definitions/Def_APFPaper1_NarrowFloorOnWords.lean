-- Prove2me | Definitions.Def_APFPaper1_NarrowFloorOnWords
-- name    : APFPaper1_NarrowFloorOnWords
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T02:48:21.439936+00:00
-- url     : https://prove2.me/theorems/209cfb35-4e17-43cc-b823-e9fbf498efd6
-- title:
--   Record floors, side-change floors and pinning on words
-- statement:
--   Three distinct predicates on supplied typed words, execution, record sets, readings and calibrated bills: record-making floor, held-side-change floor, and no-record pinning. Their truth and physical identification are not asserted. No release operation is represented by the accumulating record ledger.
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
--   Definitions.Def_APFPaper1_NarrowFloorOnWords; USB pullbacks v58 batch A, SHA-256 133f542d84cb02e83cd9aeb5a14ffe67e43423a7f956a4d65ed1786f39a21cd5. Definitions.Def_APFPaper1_NarrowFloorOnWords; USB pullbacks v58 batch A; SHA-256 133f542d84cb02e83cd9aeb5a14ffe67e43423a7f956a4d65ed1786f39a21cd5

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper1_NarrowFloorOnWords
title: The narrow floor on the foundation's words, typed two ways: by the records a word makes, and by the held sides a word turns over; and the statement that a held side is pinned
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 88641c36b0d461ec75b837f01065fc3a1cdebc2792bc8c0b5b0ad5a7fe9733d0), kept in Old/ as
 Def_APFPaper1_NarrowFloorOnWords_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED
 BYTES ARE NOT RELEASED.
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
 in bundle v51 (sha256 4406821e4fbf6ae12cfcd57764c378bf0076e2006d2aa4169de5eeb8ef3da469), kept in Old/ as
 Def_APFPaper1_NarrowFloorOnWords_pre-restating_v52_2026-11-17.lean. No declaration is changed. THE RESTATED
 BYTES ARE NOT RELEASED.
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
source: the author, 2026-11-16 10:16 HST: "Yes, narrow it is"
 (RULING_narrow_it_is_and_carrying_is_held_not_booked_2026-11-16: "The per-realignment floor is read
 narrowly. It is charged on a way that makes a record. It is not charged on every way between two
 different alignments."). The author, 2026-11-17 09:35 HST: "Find the papers you need on Google Drive.
 Proceed as indicated", to this seat's question "Shall I type the narrow floor on words next, to see
 which holds it leaves?".
 Consulted before writing (2026-11-17, 09:36 to 09:50 HST):
 - Paper 1 Supplement v9.28: 1896-1899 (P1 to P4; P4 "for every admissible protocol connecting distinct
   admissible alignments"), 1903-1913, 1915-1917 (connectivity not asserted), 1919 ("Holding a
   structural alignment costs nothing once it is instantiated; moving between two admissible alignments
   is what gets charged"), 1921-1929 (the four calibrations; (iv), at 1927: "an admissible operation either
   preserves the recorded sector at zero realignment cost or pays additional admissibility cost to erase
   or rewrite it").
 - Paper 5 Supplement v7.33, fetched whole through the Google Drive connector (file id
   17661-ouv4M3i8dpyhOFF0t5AWQCJoqoo). Lines 1 to 1973 were read in full; lines 1974 to 4212 were
   searched ("record-free", "record-null", "class transition", "hold", "K2", "realignment") and the
   passages found were read. Passages that bear on this file: 629-637 (physical reversal load bearing only for "the reversible
   record-free coherent loops used in Q4"), 1264-1272 ("A closed loop returns to the same completed
   boundary, so it moves no state. The positive cost floor bills it anyway." ... "We do not have that
   argument."), 1418-1431 (a held profile "contains no irreversible selected-branch record"; the record
   functor "retains every distinction booked by the class transition"), 1453, 1513, 1656 (record-free
   component, record-free closure), 1754-1763 (a detectable reversal is "represented and charged, so the
   loop does not remain in the original uncharged coherent identity class"), 1819-1823, 1919-1922
   ("Paper 37's class transition books a positive floor and creates a permanent record"), 3325-3333
   ("sign and phase moves are free for pricing. They are not record-free").
 - Codebank: apf/core.py:333-350 (check_L_epsilon_star: "Read at the transition level it is the
   per-realignment floor eps_min(Gamma)"; the identification is a named reading); apf/class_transition.py
   :27, 193-210 ("non-refund accounting does not exclude an inverse"); apf/gapless_serial_floor.py:141-149
   ("Bennett cycle books 2^K*eps despite returning (per-transition)"); apf/operational_completeness.py
   :404-424 ("a record-free class strips to the vacuum"); apf/anchor_support_algebra.py:74-84 (moves
   "PRICING-FREE and they are NOT RECORD-FREE").
 - Existing Lean: Thm_APFPaper1_the_narrow_floor (pass 77: NarrowFloor on supplied ways, with "what is
   held" supplied; Alignment, carried; WorldConnHeld); Def_APFB06_FreeOnWords (pass 105);
   Def_APFPaper1_KeptByFragments; Def_APFPaper5_K2_HoldWord; the builder seat's
   Def_APFPaper1_ContinuationWords and Def_APF_B06_DeclaredInput (OriginalAlignment).
standing: DEFINITIONS ONLY. The narrow floor is an ADOPTED READING of P4 of the Paper 1 Supplement, which
 is a named hypothesis of that Supplement. It is not one of the eight declared inputs. Neither typing
 below is an input, and neither is ruled as the typing the author means.
fidelity:
 (a) Pass 77 typed the narrow floor on supplied ways, with "what is held" a supplied map. Here the ways
     are the closed words of a context, and the cost of a way is the calibrated resource of the whole
     word. Closed words only: the per-realignment floor of the Supplement is said within one context.
 (b) BY RECORDS: what is held is the records held so far, and a word adds the records its fragments keep.
     A way changes what is held exactly when it makes a record. This is the ruling record's wording.
 (c) BY SIDES: what is held is a family of distinctions, each read on its side, as in the Supplement's
     alignment. Which distinction is held at which raw possibility is SUPPLIED DATA (`heldAt`). The words
     carry no datum of it. A way that turns a held side over ends where that side is not held as it was.
     This is the word form of pass 77's `turning_a_held_side_over_costs_the_floor`; it is not derived
     from that theorem.
 (d) `HeldSidesPinned` asks nothing of a bill. It is a statement about the words of a context alone.
 (e) A word that releases a record is not in the word data: the records a word keeps only accumulate.
     "Making or releasing a record" is typed here as "keeps a record".
not_claimed: that either typing holds of the physical data; that the author means one of them; that
 `heldAt` is determined by the declared inputs. No lane. No claim that the transfer is forced, that the
 carrier gap is closed or narrowed, or that Born is derived.
restated: 2026-11-17, for bundle v51. Written before the author's rulings of 11:41 HST (a record pins its
 side), 13:09 HST (no free gain) and 16:03 HST (every record a protocol keeps is some tested distinction's
 and used for it). Under the first two, on the recorded side a process that keeps no record changes
 nothing that is recorded (passes 108 and 109). So what this header leaves open about holds on the
 recorded side is settled there under his rulings. It is not settled by the inputs. Under the third, the
 narrow floor typed by records is a theorem of B05 for protocols (pass 111). Nothing else in this header
 is changed. Every byte after this comment is the byte of the file as first written.
-/
import Definitions.Def_APFB06_FreeOnWords

set_option autoImplicit false
namespace APFPaper1.NarrowOnWords
open APFPaper1.Continuation

universe uC uF uX uR uK uD
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]
  {Dn : Context → Type uD}

/-- The narrow floor on words, typed by records: the floor of each context is positive, and a closed word
that keeps a record, with keeping taken fragment by fragment, bills at least the floor of its context. -/
def MakingARecordCostsTheFloor (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g)) (eps : Context → NNReal) : Prop :=
  (∀ g, 0 < eps g) ∧
    ∀ (g : Context) (W : Word Frag g g), keptByFragments keptFrag g W ≠ ∅ →
      eps g ≤ calibration g (resource g ⟨g, W⟩)

/-- The narrow floor on words, typed by sides: the floor of each context is positive, and a closed word
that runs from a raw possibility where a distinction is held to one where that distinction reads on its
other side bills at least the floor of its context. `heldAt g x d` says that at the raw possibility `x`
of the context `g` the distinction `d` is held; it is supplied. -/
def TurningAHeldSideCostsTheFloor
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (reads : (g : Context) → Dn g → Raw g → Bool)
    (heldAt : (g : Context) → Raw g → Dn g → Prop) (eps : Context → NNReal) : Prop :=
  (∀ g, 0 < eps g) ∧
    ∀ (g : Context) (W : Word Frag g g) (x y : Raw g) (d : Dn g), Executes step W x y →
      heldAt g x d → reads g d y ≠ reads g d x → eps g ≤ calibration g (resource g ⟨g, W⟩)

/-- A held side is pinned: no closed word that keeps no record runs from a raw possibility where a
distinction is held to one where that distinction reads on its other side. Nothing is said of a bill. -/
def HeldSidesPinned (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g))
    (reads : (g : Context) → Dn g → Raw g → Bool)
    (heldAt : (g : Context) → Raw g → Dn g → Prop) : Prop :=
  ∀ (g : Context) (W : Word Frag g g) (x y : Raw g) (d : Dn g),
    keptByFragments keptFrag g W = ∅ → Executes step W x y → heldAt g x d →
      reads g d y = reads g d x

end APFPaper1.NarrowOnWords


