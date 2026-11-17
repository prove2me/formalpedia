-- Prove2me | Definitions.Def_APFPaper5_K1_same_costs_two_books_Vocabulary
-- name    : APFPaper5_K1_same_costs_two_books_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:24:11.328756+00:00
-- url     : https://prove2.me/theorems/8ef2b387-2ea2-4934-a762-97b628dcbf59
-- title:
--   Model vocabulary — Equal family costs can give different party tables
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Two supplied books give the same family cost function but different faithful-diagonal verdicts. The signed book uses a negative real weight and therefore is not a RecordLedger with nonnegative record costs. No physical negative record cost is asserted.
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
--   Theorems.Thm_APFPaper5_K1_same_costs_two_books; Pullbacks v39, SHA-256 c028ca542f16a5cf9503d762edd30a7b8af3654ae3dc30e9a36ef928c9a508c5. Theorems.Thm_APFPaper5_K1_same_costs_two_books; pullbacks v39; SHA-256 c028ca542f16a5cf9503d762edd30a7b8af3654ae3dc30e9a36ef928c9a508c5

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_same_costs_two_books
title: Two books with the same listing and the same cost for every family: in one a joint record of cost 1 and the party score meets K1's typed conditions; in the other a shared record of cost -1 and the party score is not faithful
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 05:07 HST: "1 Confirmed, please proceed" (item 5 of this seat's list of
 05:00 HST). Def_APFPaper5_K1_PartyScore, Thm_APFPaper5_K1_party_score_joint_pair.
standing: A WORKED INSTANCE on books (keeping rules with record costs), not on a record ledger and not a
 world. It shows that "no record costs less than nothing" cannot be derived from anything said about
 family costs: the two books cost every family the same (0, 1, 1 and 3 together) and differ on it. On a
 record ledger the question does not arise, because a record's cost is typed nonnegative there, as the
 declared calibration is. The second book is therefore NOT a record ledger.
what this file says: book one is the joint pair of pass 39 (own records 1 and 1, a joint record 1). Book
 two has the same listing with own records costing 2 and 2 and the common record costing -1, kept under
 the shared rule. Every family costs the same in both. The party score of book one meets K1's typed
 conditions. The party score of book two is 1 on the diagonal and -1 off it, and is not faithful.
what this file does NOT say: that a record may cost less than nothing. No lane. No claim that the transfer
 is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_party_score_joint_pair_Vocabulary
import Theorems.Thm_APFPaper5_K1_JointPair_keptCost_eq_jointRuleCost
import Theorems.Thm_APFPaper5_K1_JointPair_partyScore_meets_K1

set_option autoImplicit false

namespace APFPaper5.K1.JointPair

/-- Book two: own records cost 2, the common record costs -1. -/
def wSigned : Fin 3 → ℝ := fun a => if a.val = 2 then -1 else 2

/-- Book two has no joint record. -/
def noJoint : Fin 3 → Bool := fun _ => false















end APFPaper5.K1.JointPair


