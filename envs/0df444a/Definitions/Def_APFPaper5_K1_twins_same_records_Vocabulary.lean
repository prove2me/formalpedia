-- Prove2me | Definitions.Def_APFPaper5_K1_twins_same_records_Vocabulary
-- name    : APFPaper5_K1_twins_same_records_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:14:33.762195+00:00
-- url     : https://prove2.me/theorems/c5a9313c-2386-4f72-afcf-1ed44b3f6623
-- title:
--   Model vocabulary — The earlier counted predicate permits identical party records
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The Twins ledger satisfies B05, singleton floor and earlier LedgerCounted but has a degenerate party score. It fails the stronger Counted definition with own paid records. Other declared forms and physical realization are not checked.
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
--   Theorems.Thm_APFPaper5_K1_twins_same_records; Pullbacks v39, SHA-256 4947d29785facbbbf72c6ffafa3db80c95241039017a85b271de766684e47b02. Theorems.Thm_APFPaper5_K1_twins_same_records; pullbacks v39; SHA-256 4947d29785facbbbf72c6ffafa3db80c95241039017a85b271de766684e47b02

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_twins_same_records
title: A record ledger on which the declared B05 holds, a pair is counted and each distinction costs the floor when held alone, yet the party score is not faithful: the two distinctions are party to exactly the same records
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 05:56 HST: "Let's finish working on this can you tee it up", on the question
 whether "a counted distinction has a record of its own that costs something" is part of what counted
 means. This file tests the weaker clause "each counted distinction costs at least the floor when held
 alone" (the singleton floor of Paper 1 Supplement v9.28, thm:minimum-distinction-floor and def:MD).
standing: A COUNTERMODEL, on a record ledger. It shows that the declared B05, "counted" and a floor on each
 distinction held alone do NOT together give K1's faithful diagonal for the party score. With
 Thm_APFPaper5_K1_free_pair_paid_relation it leaves the own-record clause, or the exact condition, as what
 K1 needs where a joint record is present.
 LIMIT: a record ledger with B05, countedness and the singleton floor checked. It has no states, sides or
 continuations; B01 to B04, B06, B07a and B07b are NOT checked on it. It is not a world meeting the eight.
the ledger: two records, each costing 1. Four protocols: one keeps nothing; one serves distinction 0 and
 keeps record 0; one serves distinction 1 and keeps record 0; one serves both and keeps records 0 and 1.
 The two single protocols keep the same record and differ only in which distinction they serve.
what this file says:
 - Costs: nothing 0, each distinction alone 1, the two together 2.
 - b05_holds: the declared B05 holds with floor 1 and capacity 2, every distinction tested.
 - single_novel_over_empty, fc_single: each distinction is support-novel over the empty family and costs
   exactly the floor when held alone.
 - pair_is_counted: the pair is a counted family.
 - party_all: each distinction is party to both records. party_score_not_faithful: so the party score
   cannot tell them apart.
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

namespace APFPaper5.K1.Twins

/-- The protocols. -/
inductive Prot
  | idle
  | one (d : Fin 2)
  | both
  deriving DecidableEq

/-- What each protocol keeps. -/
def keptOf : Prot → Finset (Fin 2)
  | Prot.idle => ∅
  | Prot.one _ => {0}
  | Prot.both => Finset.univ

/-- The other distinction. -/
def other : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0



/-- The ledger. -/
noncomputable def ledger : RecordLedger (Fin 2) Prot (Fin 2) where
  cost := fun _ => 1
  kept := keptOf
  sufficient := fun p sigma d =>
    (p = Prot.one d ∨ p = Prot.both) ∧ sigma = (↑(keptOf p) : Set (Fin 2))
  usesToRealize := fun _ _ _ => True









/-- The ledger's family cost. -/
noncomputable abbrev fc (S : Finset (Fin 2)) : ℝ := ledger.familyCost S





































end APFPaper5.K1.Twins


