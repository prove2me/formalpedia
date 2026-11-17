-- Prove2me | Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
-- name    : APFPaper5_K1_counted_pair_with_relation_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:14:29.757663+00:00
-- url     : https://prove2.me/theorems/5ebb07b5-3e15-4cb2-9796-b8a42bb8b67f
-- title:
--   Model vocabulary — A paid pair with a joint record
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The supplied three-record ledger has costs 0,1,1,3, capacity 3 and floor 1. It satisfies the encoded B05 and stronger Counted predicate, with a joint record. Other declared forms and physical realization are not established.
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
--   Theorems.Thm_APFPaper5_K1_counted_pair_with_relation; Pullbacks v39, SHA-256 48803b7b623de995419686f2ee9303a33ebaa48a3fd1aae8458e4bccb7c112c5. Theorems.Thm_APFPaper5_K1_counted_pair_with_relation; pullbacks v39; SHA-256 48803b7b623de995419686f2ee9303a33ebaa48a3fd1aae8458e4bccb7c112c5

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_counted_pair_with_relation
title: A record ledger with a joint record on which the declared B05 holds and the pair is counted: two distinctions each with a record of its own costing 1 and a relation record costing 1 that only serving both takes; costs 1, 1 and 3 together
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 06:17 HST: "A" (RULING_counted_includes_own_record_2026-11-15).
 Def_APFPaper5_K1_Counted. The costs 1, 1 and 3 are those of this seat's residue world and of the
 codebank's parity pair (apf/delta_calculus.py line 1180).
standing: A WITNESS, on a record ledger. It shows that "counted" as ruled is met by a family with a joint
 record present, and that the declared B05 holds there. So the K1 statement for counted families is not
 empty where joint records are present.
 LIMIT: a record ledger with B05 and countedness checked. It has no states, sides or continuations; B01 to
 B04, B06, B07a and B07b are NOT checked on it. It is not a world meeting the eight, and it is not shown
 to be the residue world's ledger.
the ledger: three records, each costing 1. Records 0 and 1 are the two distinctions' own; record 2 is the
 relation's. A protocol is the set of records it keeps. A set of records is sufficient for a distinction,
 in a protocol, when it holds the distinction's own record and, if the protocol also keeps the other's own
 record, record 2 as well.
what this file says:
 - Costs: nothing 0, each distinction alone 1, the two together 3.
 - b05_holds: the declared B05 holds with floor 1 and capacity 3, every distinction tested.
 - relation_is_joint: the pair needs record 2 and neither distinction needs it alone.
 - pair_is_counted: the pair is counted, own-record clause included.
what this file does NOT say: that such a ledger is physical, or that the eight admit it. No lane. No claim
 that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1.PaidPair

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
  cost := fun _ => 1
  kept := fun p => p
  sufficient := fun p sigma d => own d ∈ sigma ∧ (own (other d) ∈ p → (2 : Fin 3) ∈ sigma)
  usesToRealize := fun _ _ _ => True





/-- The ledger's family cost. -/
noncomputable abbrev fc (S : Finset (Fin 2)) : ℝ := ledger.familyCost S











































end APFPaper5.K1.PaidPair


