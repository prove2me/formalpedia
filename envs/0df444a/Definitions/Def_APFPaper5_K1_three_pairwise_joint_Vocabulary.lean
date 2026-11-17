-- Prove2me | Definitions.Def_APFPaper5_K1_three_pairwise_joint_Vocabulary
-- name    : APFPaper5_K1_three_pairwise_joint_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:55:54.745769+00:00
-- url     : https://prove2.me/theorems/1ebad461-4cb6-4b59-8b10-d95170ce0ca4
-- title:
--   Model vocabulary — Pairwise bounds do not imply a faithful triple table
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   For the supplied three-mark cost function, each pair satisfies the strict bound at c=3/5 while the full form is negative on the all-ones vector. A different supplied table with diagonal 3 and off-diagonal 1 is faithful. Admissibility of three related physical distinctions is not established.
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
--   Theorems.Thm_APFPaper5_K1_three_pairwise_joint; Pullbacks v39, SHA-256 6cf934a1a14b67ecd7e5fa43a27ca54befe0d9ccc87d8c78d771bfc7e553856b. Theorems.Thm_APFPaper5_K1_three_pairwise_joint; pullbacks v39; SHA-256 6cf934a1a14b67ecd7e5fa43a27ca54befe0d9ccc87d8c78d771bfc7e553856b

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_three_pairwise_joint
title: Three distinctions with a joint record on each pair: the pair bound on every pair does not give K1's conditions for the table of shared costs, at the floor that table's form is negative, and the record-book table meets K1's conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:51 HST: "Tee up decision then finish it". Builder seat: tableForm,
 sharedCost, IsBilinear, FaithfulNonnegDiagonal. This seat: dominant_table_meets_K1 (pass 37).
standing: WORKED INSTANCES on three marks, as tables and as a cost function. No input is consumed. No world
 meeting the eight is built here; whether three distinctions may each be related to the other two in one
 counted family is NOT settled (the unit rule of 21:15 HST as typed does not forbid it).
what this file says:
 - tripleCost c: each distinction costs 1 and each pair held together adds a joint record of cost c. Its
   table of shared costs is 1 on the diagonal and -c off it.
 - With c = 3/5 every pair meets the pair bound strictly, yet the form is negative on (1, 1, 1). So for
   three or more the pair bound on each pair is not enough.
 - With c = 1 (each joint record at the cost of a distinction, as in the residue world and the codebank's
   parity pair) the form on (1, 1, 1) is -3.
 - The record-book table for c = 1 (each distinction party to its own record and to two joint records: 3
   on the diagonal, 1 off it) meets K1's typed conditions.
what this file does NOT say:
 - That the record-book table is K1's score. Not ruled.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_dominant_table_Vocabulary
import Theorems.Thm_APFPaper5_K1_dominant_table_lower_bound
import Theorems.Thm_APFPaper5_K1_dominant_table_meets_K1
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
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace APFPaper5.K1.ThreePairwise

/-- The table with `d` for a mark with itself and `c` for two different marks. -/
def uniformTable (d c : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then d else c



/-- Each distinction costs 1; each pair held together adds a joint record of cost `c`. -/
noncomputable def tripleCost (c : ℝ) (S : Finset (Fin 3)) : ℝ := (S.card : ℝ) + c * (S.card.choose 2 : ℝ)











end APFPaper5.K1.ThreePairwise


