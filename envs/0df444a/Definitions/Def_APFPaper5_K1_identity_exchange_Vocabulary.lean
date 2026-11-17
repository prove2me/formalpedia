-- Prove2me | Definitions.Def_APFPaper5_K1_identity_exchange_Vocabulary
-- name    : APFPaper5_K1_identity_exchange_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:38:08.43681+00:00
-- url     : https://prove2.me/theorems/b401edde-7855-4a1b-b4ed-6c63ccddf0fa
-- title:
--   Model vocabulary — Conditional K1 algebra with identity exchange
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Given finite source data, nonnegative weights and SourceCounted, the party table has the displayed algebraic properties under identity role exchange. Mark classes and the exchange are supplied constructions; original physical readouts and full Paper 5 K1 coverage are not established.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_identity_exchange; Pullbacks v39, SHA-256 5c26600eda7b721f5defddee45946b97673ab369046eb093a904b83070e50125. Theorems.Thm_APFPaper5_K1_identity_exchange; pullbacks v39; SHA-256 5c26600eda7b721f5defddee45946b97673ab369046eb093a904b83070e50125

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_identity_exchange
title: A recorded distinction is the same thing held and read, so every typed hypothesis of K1 holds for the ruled score of a counted family, with the identity as exchange and a zero orientation part
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 09:39 HST: "It is the same", in answer to this seat's question "is a recorded
 distinction the same thing held and read, so that the exchange of the two roles is the identity?"
 (TEE_UP_K1_ordered_score_2026-11-15, option A). RULING_recorded_distinction_held_and_read_2026-11-15.
 Paper 5 Supplement v7.33:312-334 (the scalar ledger does not determine the ordered score), 353-382 (the
 ordered-score theorem; the alternating part "may be nonzero"), 3038-3041 (K1), 70 and 3101-3104 (the ledger
 does not depend on Held orientation). The builder seat's Def_APFPaper5_K1_OrderedScore (the typed
 hypotheses), Thm_APFPaper5_K1_bilinearization and Thm_APFPaper5_K1_record_book_table.
standing:
 - The identification is the author's ruling. It is carried here in two places and nowhere else: one
   vector, markClass, is the class of a distinction held and of the same distinction read; and the exchange
   of the two roles is the identity map.
 - The score is the author's ruling B and "counted" is the author's ruling A, as typed in
   Def_APFPaper5_K1_SourcePartyScore.
consumes_inputs: none. No declared input is used as a hypothesis and none is proved.
theorems:
 - (tableForm_markClass, table_linearizes) the form of a table reproduces the table on the classes of the
   marks: the first typed hypothesis of K1.
 - (nondegenerate_of_faithful_identity) with the identity as exchange, a faithful diagonal gives a
   nondegenerate pairing, so there is no radical to quotient by.
 - (orientationForm_zero_of_symm, ledgerForm_eq_of_symm) for a symmetric table the orientation part is zero
   and the ledger form is the form itself.
 - (sourcePartyScore_symm) the ruled score of two distinctions is the same in either order.
 - (source_counted_family_meets_all_of_K1_with_identity_exchange) all of the above for the ruled score of a
   counted family on any source data of the declared forms, for any cost of records that is never negative.
not claimed:
 - An ordered score with a nonzero orientation part. Under the ruling K1 hands K3 no orientation.
 - That the score is separately additive under a coarse-graining of classes, or the construction of the
   classes from a score table by linearization. The classes here are the combinations of the counted
   distinctions, taken as given.
 - That a region's distinctions are counted, or what a record costs.
 - Anything about a hold, a turn, reversal or K3. No lane. No claim that the transfer is forced, that the
   carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_sourceNeeds_mono
import Theorems.Thm_APFPaper5_K1_source_own_record_of_alone_not_rest
import Theorems.Thm_APFPaper5_K1_source_party_score_meets_K1
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_K1
import Theorems.Thm_APFPaper5_K1_leastBill_nonneg
import Theorems.Thm_APFPaper5_K1_leastBill_le_bill
import Theorems.Thm_APFPaper5_K1_le_leastBill
import Theorems.Thm_APFPaper5_K1_leastBill_pos_iff
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_K1_leastBill
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_sourceNeeds
import Theorems.Thm_APFPaper5_K1_cost_le_leastBill
import Theorems.Thm_APFPaper5_K1_leastBill_eq_cost_of_kept_alone
import Theorems.Thm_APFPaper5_K1_ledgerPartyScore_eq_source
import Theorems.Thm_APFPaper5_K1_counted_iff_sourceCounted
import Theorems.Thm_APFPaper5_K1_sourceCounted_leastBill_of_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_source_counted_pair_meets_K1
import Theorems.Thm_APFPaper5_K1_exchanged_eq_ledger_add_orientation
import Theorems.Thm_APFPaper5_K1_ledgerForm_posDef
import Theorems.Thm_APFPaper5_K1_diagonal_parallelogram
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

section Table

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The class of a mark among the combinations of marks: coefficient 1 at that mark, 0 elsewhere. The
same vector serves for the mark held and for the mark read. -/
def markClass (i : ι) : ι → ℝ := fun k => if k = i then 1 else 0











end Table

section Source

variable {D P R Record : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
  [Fintype Record]





end Source

end APFPaper5.K1


