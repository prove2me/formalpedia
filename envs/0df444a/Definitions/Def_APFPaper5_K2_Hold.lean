-- Prove2me | Definitions.Def_APFPaper5_K2_Hold
-- name    : APFPaper5_K2_Hold
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:26:07.102546+00:00
-- url     : https://prove2.me/theorems/b02cd54a-1cd4-4835-92fd-22d27d26d29d
-- title:
--   A hold as a permutation of listed readings preserving a supplied table
-- statement:
--   IsHold is the conjunction of rearranging listed Boolean readings by a supplied permutation and flips, and preserving a supplied real table. It describes a map on states. It does not supply a word executing that map, admission, cost, an admitted reverse, or an action on unrecorded held data. The codebank's unresolved coherent hold is not identified with this predicate.
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
--   Definitions.Def_APFPaper5_K2_Hold; USB pullbacks v58 batch B, SHA-256 1d10b2559e0c09cf9508f6956952a85f1cf5d70ba9aa97d83d8750a7c7454127. Definitions.Def_APFPaper5_K2_Hold; USB pullbacks v58 batch B; SHA-256 1d10b2559e0c09cf9508f6956952a85f1cf5d70ba9aa97d83d8750a7c7454127

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not bundled, not built in the ledger repo, not built on the build
 machine)
name: APFPaper5_K2_Hold
title: A hold, as defined: a map of states that rearranges the listed distinctions by a permutation of the list, each on one side or the other, and keeps K1's table
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 2633906a689b8c3ef3085bd5e744985510afed5fce75267df63921b990496c13), kept in Old/ as
 Def_APFPaper5_K2_Hold_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE RESTATED BYTES ARE
 NOT RELEASED.
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
ruling: the author, 2026-11-16 15:09 HST, "5-12 as advised", call 8 of TEE_UP_open_decisions_2026-11-16
 (RULING_calls_5_to_12_as_advised_2026-11-16): K2's two hold readings become definitions of a hold: a hold
 draws nothing, and a hold keeps K1's table. Before it: 2026-11-13 15:43 HST, "Under a hold, distinctions
 aren't drawn or erased, just rearranged."; 2026-11-14 11:33 HST, "They are correct", on NothingDrawn and
 StillHeldAfter (RULING_hold_readings_2026-11-14, seat 01WrrBvu); 2026-11-15 13:23 HST, "yes, hold keeps
 table" (RULING_hold_keeps_table_2026-11-15).
source: Def_APFPaper5_K2_HoldScore (RearrangesFamily, KeepsTable); the builder seat's
 Def_APFB02_HoldOnDistinctions (NothingDrawn, StillHeldAfter). Paper 5 Supplement v7.33:396-420.
standing: A DEFINITION, this seat's typing of the ruling. Two clauses. The first is "draws nothing" with
 its witness written out, as in RearrangesFamily, and with the rearrangement a PERMUTATION of the list.
 The permutation is this seat's choice and is flagged: it is what the theorems that use an inverse already
 take, and Thm_APFPaper5_K2_hold_as_defined shows it is the same as the third adopted reading, "B02 is
 still true after a hold", once B02's second sentence holds. The second clause is KeepsTable.
definition:
 - IsHold reads dist G h sigma flip: after the map h of states, each listed distinction reads what the
   listed distinction sigma of it read before, on one side or the other; sigma is a permutation of the
   list; and the table G has the same entry on two distinctions and on the two they are rearranged from.
codebank: its hold is a different thing and is NOT identified with this one. apf/hold_cost_dominance.py:
 "the hold: co-present coherent survey, zero booking until the single commit".
 apf/commutative_no_unresolved_hold.py (check_L_commutative_no_unresolved_hold): in a commutative algebra
 "the off-diagonal 'hold' content" of a state "is invisible to the whole algebra". This definition says
 only what a hold does to the listed distinctions and to K1's table: the recorded side. It has no clause
 on what a hold bills, and none on what is held unrecorded.
not claimed: that this is all a hold is. That any word of any world runs as a hold, other than the empty
 word. That the table is K1's ruled score: G is a parameter. Anything about a side: a side does not enter
 the table. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper5_K2_HoldScore
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false

namespace APFPaper5.K2

universe uI uX uD
variable {ι : Type uI}

/-- A hold of a listed family, against a table: a map of states that rearranges the listed distinctions by
a permutation of the list, each on one side or the other, and keeps the table. -/
def IsHold {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D) (G : ι → ι → ℝ)
    (h : X → X) (sigma : Equiv.Perm ι) (flip : ι → Bool) : Prop :=
  RearrangesFamily reads dist h (sigma : ι → ι) flip ∧ KeepsTable G (sigma : ι → ι)

end APFPaper5.K2


