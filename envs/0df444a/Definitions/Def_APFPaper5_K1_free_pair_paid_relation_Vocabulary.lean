-- Prove2me | Definitions.Def_APFPaper5_K1_free_pair_paid_relation_Vocabulary
-- name    : APFPaper5_K1_free_pair_paid_relation_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:14:31.717123+00:00
-- url     : https://prove2.me/theorems/116e0569-4418-4f20-be87-4c8821df2cd1
-- title:
--   Model vocabulary — A free pair with a paid relation and degenerate score
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The example satisfies B05 and the earlier LedgerCounted predicate; it does not satisfy the stronger Counted definition. The own records cost zero and the joint record costs one. No all-eight or physical-model claim follows.
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
--   Theorems.Thm_APFPaper5_K1_free_pair_paid_relation; Pullbacks v39, SHA-256 29f8413cb357e5c0baaae617a7eea68f063cef67e92267bf8269f6afe85f8162. Theorems.Thm_APFPaper5_K1_free_pair_paid_relation; pullbacks v39; SHA-256 29f8413cb357e5c0baaae617a7eea68f063cef67e92267bf8269f6afe85f8162

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_free_pair_paid_relation
title: A record ledger on which the declared B05 holds and a pair is counted, yet the party score is not faithful: two distinctions that each cost nothing alone and whose relation costs 1
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 05:07 HST: "1 Confirmed, please proceed" (item 5 of this seat's list of
 05:00 HST: derive the premises or build a countermodel). Def_APFPaper5_K1_LedgerPartyScore,
 Def_APFPaper5_K1_LedgerScore (LedgerCounted), Def_APF_B05_DeclaredInput_r2.
standing: A COUNTERMODEL, on a record ledger. It shows that the declared B05 together with "counted" does
 NOT give "each distinction, held alone, needs a record of positive cost that the others together do not
 need", and does not give K1's faithful diagonal for the party score, where a joint record is present.
 LIMIT: it is a record ledger with B05 and countedness checked. It has no states, sides or continuations,
 and B01 to B04, B06, B07a and B07b are NOT checked on it. It is not a world meeting the eight.
the ledger: three records. Records 0 and 1 are the two distinctions' own and cost nothing. Record 2 costs
 1. A protocol is the set of records it keeps. A set of records is sufficient for a distinction, in a
 protocol, when it holds the distinction's own record and, if the protocol also keeps the other's own
 record, record 2 as well. So each distinction can be served alone for nothing, and serving both takes
 record 2.
what this file says:
 - Costs: each distinction alone 0, the two together 1.
 - b05_holds: the declared B05 holds with floor 1 and capacity 1, every distinction tested. The floor is
   met at the one step where it applies: adding either distinction to the other adds 1.
 - pair_is_counted: the pair is a counted family.
 - party_score_not_faithful: both distinctions are party to the only record of positive cost, so the party
   score cannot tell them apart.
 - no_own_paid_record: neither distinction, held alone, needs a record of positive cost.
what this file does NOT say: that such a ledger is physical, or that the eight admit it. No lane. No claim
 that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1.FreePair

/-- The own record of a distinction. -/
def own : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 1

/-- The other distinction. -/
def other : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

/-- The ledger. -/
noncomputable def ledger : RecordLedger (Fin 2) (Finset (Fin 3)) (Fin 3) where
  cost := fun a => if a = 2 then 1 else 0
  kept := fun p => p
  sufficient := fun p sigma d => own d ∈ sigma ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ sigma)
  usesToRealize := fun _ _ _ => True





/-- The ledger's family cost. -/
noncomputable abbrev fc (S : Finset (Fin 2)) : ℝ := ledger.familyCost S

































end APFPaper5.K1.FreePair


