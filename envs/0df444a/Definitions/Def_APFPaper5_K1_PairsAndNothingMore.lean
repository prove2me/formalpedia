-- Prove2me | Definitions.Def_APFPaper5_K1_PairsAndNothingMore
-- name    : APFPaper5_K1_PairsAndNothingMore
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-22T02:47:32.96072+00:00
-- url     : https://prove2.me/theorems/f1f5098b-96dd-45a5-999e-618cd3783ef8
-- title:
--   The pairs-only identity for a supplied plane cost
-- statement:
--   The named three-way inclusion-exclusion identity is a predicate on an arbitrary real-valued function of two real coordinates. Nonnegativity, homogeneity, physical realization and truth of the predicate are not supplied by this definition.
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
--   Definitions.Def_APFPaper5_K1_PairsAndNothingMore; USB pullbacks v58 batch A, SHA-256 06811cb7f3a31eb4bf2ca3a215c924f5d5ae56a892691b097d0300f2f972f187. Definitions.Def_APFPaper5_K1_PairsAndNothingMore; USB pullbacks v58 batch A; SHA-256 06811cb7f3a31eb4bf2ca3a215c924f5d5ae56a892691b097d0300f2f972f187

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-19; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper5_K1_PairsAndNothingMore
title: Pairs and nothing more, as a named clause on a cost of combinations in the plane of two marks
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 75f49239301973a6daceb41e563bd3065839130834d60853631fe4e3da124ecf), kept in Old/ as
 Def_APFPaper5_K1_PairsAndNothingMore_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE
 RESTATED BYTES ARE NOT RELEASED.
 Changed in this header: the revision named on the inputs_revision line, which was 2026-11-18.3, and this
 entry. Nothing else.
 WHAT HAPPENED: since revision 2026-11-18.3, which this header named until now, one revision of
 FOUNDATION_INPUTS was installed. Revision 2026-11-20.2, installed 2026-11-20 at 12:36 HST (sha256
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
 HOW TO READ THE REST OF THIS HEADER: it named revision 2026-11-18.3 and is left as written, any earlier
 entries "restated" below included. Where it names revision 2026-11-18.3 or an earlier one as the revision
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
 worded above and for no typing of it. THE NEW SENTENCES OF B06 HAVE NO CERTIFIED LEAN FORM: the forms the
 inputs file names for the reduced B06 are drafts of the two seats, marked PROPOSED_NOT_CERTIFIED, and the
 Lean that derives the declared forms of B03 and B05 is a draft and is not gated. NOTHING in this entry says
 that a theorem of this file follows from the inputs at revision 2026-11-20.2, or that a supplied world of
 this file is a world of them: each theorem stands as before, on its named hypotheses or on its supplied
 world, and a supplied world that breaks a sentence of the inputs at revision 2026-11-20.2 is not a world of
 the inputs at that revision, whatever this header says of an earlier one. The gate policy says of the move
 to this revision: "immutable; dependency compatibility must be established separately; no stale-basis
 waiver". This entry establishes no such compatibility. Proposed revision 2026-11-20.3 (one further note on
 each of B07a and B07b) is NOT installed.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-19 09:43 HST: "yes", to "Where ways that keep no record meet, is what is counted
 made up of the ways one at a time and two at a time, with nothing further for three or more together, yes
 or no?" (RULING_where_ways_that_keep_no_record_meet_what_is_counted_is_the_ways_one_at_a_time_and_two_at_a_time_2026-11-19).
 The builder seat's Def_APFPaper5_K1_CrossForm and Thm_APFPaper5_K1_plane_cost_quadratic (2026-11-12): a
 supplied cost q of combinations, a combination being a pair of real coefficients. Paper 5 Supplement
 v7.33:246-298 ("parallelogram-complete"; "mark quadratic ledger completion as a named regime condition").
 This seat's pass 144 (the same clause on whole-number counts of collections).
standing: a NAMED CLAUSE. It is a predicate on a supplied cost and asserts nothing. It is this seat's typing
 of the ruling on the builder seat's plane. Two choices are this seat's and are flagged. (1) The ruling is
 said of ways that keep no record; here it is typed of combinations, on the K layer's reading that a record
 is the cost of a combination. That the ways of the ruling are the combinations of this plane is not
 claimed. (2) "Nothing further for three or more together" is typed for three; for a cost that adds in
 this way the same holds for any number, by pass 144's theorem that such a count is fixed by ones and twos.
statement: PairsAndNothingMore q says that the cost of three combinations together is the costs of the
 three pairs less the costs of the three alone.
no structure, no class, no Prop-valued field.
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K1

/-- Pairs and nothing more: the cost of three combinations together is fixed by the costs of the three
pairs and of the three alone. -/
def PairsAndNothingMore (q : ℝ → ℝ → ℝ) : Prop :=
  ∀ a1 a2 b1 b2 d1 d2 : ℝ,
    q (a1 + b1 + d1) (a2 + b2 + d2) =
      q (a1 + b1) (a2 + b2) + q (a1 + d1) (a2 + d2) + q (b1 + d1) (b2 + d2)
        - q a1 a2 - q b1 b2 - q d1 d2

end APFPaper5.K1


