-- Prove2me | Definitions.Def_APFPaper5_K1_joint_pair_two_tables_Vocabulary
-- name    : APFPaper5_K1_joint_pair_two_tables_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:21:12.717602+00:00
-- url     : https://prove2.me/theorems/bf8ff090-b647-43e5-82cf-8938cdc692de
-- title:
--   Model vocabulary — Shared-cost and record tables for two keeping rules
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The same listing gives costs 0,2,2,3 under the shared rule and 0,1,1,3 under the joint rule. Its record table is faithful; the joint-rule shared-cost table is degenerate. These are supplied books, not physical worlds.
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
--   Theorems.Thm_APFPaper5_K1_joint_pair_two_tables; Pullbacks v39, SHA-256 f0957eb5dd11718bbec63d57b872fe7ef3cdcd79fec575e1c5875ac04817e583. Theorems.Thm_APFPaper5_K1_joint_pair_two_tables; pullbacks v39; SHA-256 f0957eb5dd11718bbec63d57b872fe7ef3cdcd79fec575e1c5875ac04817e583

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_joint_pair_two_tables
title: One book of three records under two rules for when a record is kept: the record-book table is the same under both and meets K1's typed conditions; the table of shared costs agrees with it under the shared rule and, under the joint rule, is not faithful
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:51 HST: "Tee up decision then finish it". Read as: lay out the call on
 joint records with its facts typed. Builder seat: atomTable, tableForm, record_book_table_satisfies_K1,
 sharedCost. Numbers: the joint-rule costs 1, 1 and 3 are those of this seat's residue world
 (Thm_APFB06_subadditivity_worlds, APFB06.ResidueWorldR2: cost_single_A, cost_single_B, cost_pair, a world
 meeting the eight) and of the codebank's parity pair
 (apf/delta_calculus.py line 1180: 3*EPS - EPS - EPS). The shared-rule costs 2, 2 and 3 are those of this
 seat's bridge witness (pass 26).
standing: A WORKED INSTANCE with two distinctions. It decides nothing about what K1's score IS. That is a
 call for the author (TEE_UP_K1_score_with_joint_records_2026-11-14). No input is consumed.
what this file says:
 - The book: one record of cost 1 for each distinction and one record of cost 1 that both are party to.
 - Shared rule (a record is kept when SOME distinction party to it is held): costs 0, 2, 2, 3. The table of
   shared costs IS the record-book table: 2 on the diagonal, 1 off it.
 - Joint rule (a record is kept when EVERY distinction party to it is held): costs 0, 1, 1, 3. The table of
   shared costs is 1 on the diagonal and -1 off it; its form vanishes on (1, 1); it is not faithful. The
   record-book table is unchanged. Its diagonal entry is what a distinction adds over the other, and its
   off-diagonal entry is the cost of the joint record, which is minus the shared cost.
 - The record-book table meets K1's typed conditions (the builder seat's theorem, applied).
what this file does NOT say:
 - That the record-book table is K1's score where a joint record is present. Not ruled.
 - That costs alone fix the book. They do not: costs fix only the difference between what two distinctions
   share and what joins them. The table here reads the records.
 - Anything for three or more distinctions (see Thm_APFPaper5_K1_three_pairwise_joint).
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K1.JointPair

/-- Every record costs 1. -/
def w : Fin 3 → ℝ := fun _ => 1

/-- Record 0 is distinction 0's own, record 1 is distinction 1's own, and both are party to record 2. -/
def mark (i : Fin 2) (a : Fin 3) : Bool := decide (a.val = i.val ∨ a.val = 2)

/-- Shared rule: a record is kept when some distinction party to it is held. -/
def somePartyHeld (a : Fin 3) (S : Finset (Fin 2)) : Bool := decide (∃ i ∈ S, mark i a = true)

/-- Joint rule: a record is kept when every distinction party to it is held. -/
def everyPartyHeld (a : Fin 3) (S : Finset (Fin 2)) : Bool := decide (∀ i, mark i a = true → i ∈ S)

noncomputable def sharedRuleCost (S : Finset (Fin 2)) : ℝ := ∑ a, w a * ind (somePartyHeld a S)

noncomputable def jointRuleCost (S : Finset (Fin 2)) : ℝ := ∑ a, w a * ind (everyPartyHeld a S)





/-! ### The costs under each rule -/

















/-! ### The record-book table: the same under both rules -/





/-! ### Shared rule: the table of shared costs is the record-book table -/



/-! ### Joint rule: the table of shared costs is not the record-book table, and is not faithful -/









end APFPaper5.K1.JointPair


