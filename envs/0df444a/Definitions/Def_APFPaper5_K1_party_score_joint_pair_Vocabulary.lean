-- Prove2me | Definitions.Def_APFPaper5_K1_party_score_joint_pair_Vocabulary
-- name    : APFPaper5_K1_party_score_joint_pair_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:12:22.636468+00:00
-- url     : https://prove2.me/theorems/eb10585e-d877-456f-9abb-ebb199a15048
-- title:
--   Model vocabulary — A joint book with faithful party score
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The three-record example has family costs 0,1,1,3, a faithful party score and a degenerate shared-cost table. It is a book with no asserted states, continuations or satisfaction of all eight forms.
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
--   Theorems.Thm_APFPaper5_K1_party_score_joint_pair; Pullbacks v39, SHA-256 29586b17fa1fd9cde9073a56d5b1c3cff8d1799cfa78be60d8eff0203e3af4f7. Theorems.Thm_APFPaper5_K1_party_score_joint_pair; pullbacks v39; SHA-256 29586b17fa1fd9cde9073a56d5b1c3cff8d1799cfa78be60d8eff0203e3af4f7

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_party_score_joint_pair
title: The premises of the party-score K1 statement hold together with a joint record present: in the book of two own records and one joint record, costing 1, 1 and 3 together, the party score meets K1's typed conditions and the table of shared costs does not
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 22:13 HST: "B" (RULING_K1_score_with_joint_records_2026-11-14).
 Def_APFPaper5_K1_PartyScore, Thm_APFPaper5_K1_party_score, Thm_APFPaper5_K1_joint_pair_two_tables.
standing: A WORKED INSTANCE. It shows the statement partyScore_book_meets_K1 is not empty where a joint
 record is present, and that there the two candidate tables part ways. It is a book, not a world: no
 states, continuations or alignments, and the eight are not checked on it.
what this file says: with record 2 marked joint, the general keeping rule gives the joint-rule costs of
 pass 38 (0, 1, 1, 3: the numbers of this seat's residue world and of the codebank's parity pair); the
 party score meets K1's typed conditions; the table of shared costs of the same book is not faithful.
what this file does NOT say: that the residue world carries this book. No lane. No claim that the transfer
 is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_partyTo_book_iff
import Theorems.Thm_APFPaper5_K1_partyScore_book
import Theorems.Thm_APFPaper5_K1_partyScore_book_meets_K1
import Theorems.Thm_APFPaper5_K1_partyScore_book_faithful_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_eq_partyScore_of_no_joint
import Definitions.Def_APFPaper5_K1_joint_pair_two_tables_Vocabulary
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_empty
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_zero
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_one
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_univ
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_sharedCost_table_not_faithful

set_option autoImplicit false

namespace APFPaper5.K1.JointPair

/-- Record 2 is the joint record; records 0 and 1 are each one distinction's own. -/
def joint (a : Fin 3) : Bool := decide (a.val = 2)











end APFPaper5.K1.JointPair


