-- Prove2me | Definitions.Def_APFB06_FreeOnWords
-- name    : APFB06_FreeOnWords
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T02:47:40.999793+00:00
-- url     : https://prove2.me/theorems/816f4141-d54f-42d4-96b4-93a87b36aab7
-- title:
--   A named zero-cost condition on record-free words
-- statement:
--   FreeOnWords is the explicit hypothesis that every word whose assigned fragments keep no records has zero calibrated bill. Protocol membership and the equality of maintained records with the supplied fragment ledger remain explicit. This is reference vocabulary, not a certified encoding of current B06.
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
--   Definitions.Def_APFB06_FreeOnWords; USB pullbacks v58 batch A, SHA-256 8adb618f89c2408f2ee30ecdb685f14bfc193b4cb369aaed8df5c2036ac8d99d. Definitions.Def_APFB06_FreeOnWords; USB pullbacks v58 batch A; SHA-256 8adb618f89c2408f2ee30ecdb685f14bfc193b4cb369aaed8df5c2036ac8d99d

/-
RE-HEADED A SECOND TIME 2026-11-17 11:46 HST by the seat that wrote this file. Only this block is new. The
block of 07:29 HST below it, the original header and all code are unchanged. Where they differ from this
block, this block governs. Pre-edit copy: Old/Def_APFB06_FreeOnWords_pre-second-reheading_2026-11-17.lean,
sha256 952c0d942ce9735f923756de77ee2fdc1408eb927690ae685374819ede74e6fa.
 - THE AUTHOR, 2026-11-17 09:14 HST: "Yes that's correct", in answer to this seat's "When a protocol is read
   as a word, are the records it maintains exactly the records its fragments keep?"
   (RULING_a_protocol_maintains_what_its_fragments_keep_2026-11-17). So where the block of 07:29 HST or the
   original header says that this reading is not ruled, read: RULED BY THE AUTHOR. In Lean it is
   APFB06.MaintainedIsKeptByFragments. It is said of a protocol read as a word. That a protocol is a word
   of its context is the builder seat's whole-word reading of B06, and is not ruled by this.
 - Still not ruled: that what a fragment keeps is the Supplement's ledger support of the fragment.
 - THE AUTHOR, 2026-11-17 11:41 HST: "A and all you can that's open", on
   TEE_UP_does_a_record_pin_its_side_2026-11-17 (RULING_a_record_pins_its_side_2026-11-17): a record pins its
   side. Nothing in this file assumes it or uses it.
 - Unchanged: FreeOnWords is this seat's candidate and not the declared form; no lane; no claim that the
   transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
---- block of 07:29 HST follows ----
RE-HEADED 2026-11-17 07:29 HST by the seat that wrote this file. Only this block is new. The original
header below it and all code are unchanged. Where the original header differs from this block, this block
governs. Pre-edit copy: Old/Def_APFB06_FreeOnWords_pre-reheading_2026-11-17.lean,
sha256 f959c1c2a8abbad04089642238c2e4a8457aef85ae7c512b4a99dfd999735762.
 - THE AUTHOR, 2026-11-17 07:28 HST: "Yes, every word of a context is a process", in answer to this seat's
   "Is every word of a context a process, so that the sentence covers it?"
   (RULING_every_word_of_a_context_is_a_process_2026-11-17). Read as: the sentence "A process that keeps no
   record costs nothing" speaks of every word of every context.
 - So where the original header says that this is NOT ruled, or lists "that every word of a context is a
   process" under what is not claimed, read: RULED BY THE AUTHOR. FreeOnWords has the scope he gives the
   sentence. It is still this seat's candidate and not the declared form, and it is still a HYPOTHESIS of
   every theorem that names it.
 - Still not ruled: that what a fragment keeps is the Supplement's ledger support of the fragment; that the
   records B05 speaks of a protocol maintaining are the records its fragments keep.
 - FOUNDATION_INPUTS is not edited by the ruling. Its terms for the sentence read as they did at revision
   2026-11-17.2.
 - Unchanged: no lane; no claim that the transfer is forced, that the carrier gap is closed or narrowed, or
   that Born is derived.
---- original header (2026-11-17, pass 105) follows ----
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-17; not
 gated, not reviewed, not released, not bundled, not built in the ledger repo, not built on the build
 machine)
name: APFB06_FreeOnWords
title: A candidate form, on the foundation's words, of "A process that keeps no record costs nothing", and the reading that joins it to what a protocol maintains
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 097b2946d1cecc90719a50132d0751ea736cc2afbd4688de9e3e8b92a0ba20e7), kept in Old/ as
 Def_APFB06_FreeOnWords_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED BYTES ARE
 NOT RELEASED.
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
 in bundle v51 (sha256 4c020507ce39d087e6cb3f1a35b92e0935eb8bbc476285bbb05f936e379d668b), kept in Old/ as
 Def_APFB06_FreeOnWords_pre-restating_v52_2026-11-17.lean. No declaration is changed. THE RESTATED BYTES ARE
 NOT RELEASED.
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
asked: the author, 2026-11-17 07:01 HST: "Yes, start on 3", where 3 was this seat's "join the new sentence
 to the foundation's word data, by proposing 'what a fragment keeps' as data and tying the protocol form to
 the word form".
the sentence: FOUNDATION_INPUTS revision 2026-11-17.2, B06, amendment_20261117: "A process that keeps no
 record costs nothing." Its terms there: "A process: a protocol or any finite part of one; a finite
 continuation in the sense of the Paper 1 Supplement. ... Keeps: a process keeps what its parts keep and
 nothing else ... Costs: its calibrated bill, the valuation of its whole resource load." Its scope there:
 "Every context and every regime. Every process of a context, a whole protocol or a part of one, of any
 length." Open there for the declared form: "What each fragment of a process keeps is not among the
 foundation's word data; it has to be added as data in a definition node. How the form on protocols and
 the form on words are joined."
source: CONSULTED FIRST, before any Lean was typed.
 Paper 1 Supplement v9.28: 1225-1232 (a finite admissible continuation "may be a finite test, interaction,
 perturbation, composition, record-writing operation, maintenance operation, or finite process fragment";
 C1, the trivial continuation belongs to Cont(x) for every x; C3, prefix restriction); 1240 (the combined
 load is the load of the concatenation, not the sum of the two loads); 2197-2214 (a protocol carries a
 resource load in a resource monoid; the calibration is monotone and takes 0 to 0); 2624-2625 (the support
 assignment of a protocol: the maintained records it uses); 2889-2891 (the empty family is realized by the
 empty protocol at zero cost); 3188-3202 (continuation word; a fragment is typed by its input and output
 contexts "and by the finite ledger support required to execute it ... a finite continuation move with a
 domain, codomain, and cost support"); 3209 (arrows are "finite admissible continuation fragments carrying
 specified ledger support"); 3301 (W-her, hypothesized and not derived); 6819 ("each arrow carries a cost
 type and a budget constraint").
 Codebank: operational_completeness.py:1392 (check_T_ledger_rent_excluded: the ledger books a commitment at
 a transition, or a per-activation charge "when and only when an interface activates on held content"; no
 standing rent); hold_cost_dominance.py:36-56 (the hold: "zero booking until the single commit"; the
 marginal column is two-valued, 0 or at least epsilon); core.py:1851; held_holonomy and its helpers
 (record-free loops enter there as named physical premises).
 Existing Lean. The builder seat's Def_APFPaper1_ContinuationWords: Word, WordFrom ("the process type of
 context g"), Cont, with the resource of EVERY word of a context as supplied data; its fragment typing is
 the input and output contexts only. Its Thm_APFB06_amendedB06_whole_word_reading: B06 with processes :=
 words, protocols a set of words, and the whole resource of a protocol := the resource of that word. Its
 Def_APF_B05_DeclaredInput_r2: what a protocol maintains is supplied on protocols. This seat's
 Def_APFPaper1_KeptByFragments (the author's ruling of 2026-11-16 19:45 HST),
 Thm_APFPaper5_K2_the_three_closure_facts_derived (its hypothesis hfree is the statement defined here) and
 Thm_APFPaper1_keeping_nothing_costs_nothing (KeepingNothingFree, on protocols).
standing: CANDIDATES, typed by this seat. Neither is the declared form, which is the builder seat's to
 write, and neither is ruled by the author. What each fragment keeps (keptFrag) is NEW DATA: it is not in
 the foundation's word data. That it is the Supplement's "ledger support" of a fragment is a reading this
 seat has not put to the author. Its first index is the context whose ledger is read: a word that changes
 context is billed in the context it starts in (the author's ruling of 2026-11-12), so what a later
 fragment keeps has to be said in that context's records. That choice of shape is this seat's.
definitions:
 - FreeOnWords: every word of every context that keeps no record, with keeping taken fragment by fragment,
   has calibrated bill zero. It quantifies over EVERY word of a context, the builder seat's process type,
   and not only over the words that are protocols or lie inside one.
 - MaintainedIsKeptByFragments: for a protocol read as a word, the records it maintains are the records its
   fragments keep.
not claimed: that every word of a context is a process in the author's sense; that any fragment keeps no
 record; that a bill is the sum of the costs of the records kept. No lane. No claim that the transfer is
 forced, that the carrier gap is closed or narrowed, or that Born is derived.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper1_KeptByFragments

set_option autoImplicit false
namespace APFB06
open APFPaper1.Continuation

universe uC uF uR uK
variable {Context : Type uC} {Frag : Context → Context → Type uF} {R : Context → Type uR}
  {Rec : Context → Type uK} [∀ g, DecidableEq (Rec g)]

/-- A candidate form of "A process that keeps no record costs nothing" on the foundation's words: every
word of every context that keeps no record, with keeping taken fragment by fragment, has calibrated bill
zero. `keptFrag g h k f` is what the fragment `f` from `h` to `k` keeps, as records of the context `g`
whose ledger is being read. -/
def FreeOnWords (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g)) : Prop :=
  ∀ (g : Context) (w : WordFrom Frag g), keptByFragments keptFrag g w.2 = ∅ →
    calibration g (resource g w) = 0

/-- The reading that joins the two forms: a protocol, read as a word, maintains exactly the records its
fragments keep. -/
def MaintainedIsKeptByFragments (protocols : (g : Context) → Set (WordFrom Frag g))
    (maintained : (g : Context) → {p : WordFrom Frag g // p ∈ protocols g} → Set (Rec g))
    (keptFrag : (g h k : Context) → Frag h k → Finset (Rec g)) : Prop :=
  ∀ (g : Context) (p : {p : WordFrom Frag g // p ∈ protocols g}),
    maintained g p = (↑(keptByFragments keptFrag g p.val.2) : Set (Rec g))

end APFB06


