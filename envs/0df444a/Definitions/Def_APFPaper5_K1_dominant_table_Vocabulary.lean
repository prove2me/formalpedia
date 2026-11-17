-- Prove2me | Definitions.Def_APFPaper5_K1_dominant_table_Vocabulary
-- name    : APFPaper5_K1_dominant_table_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:20:28.664815+00:00
-- url     : https://prove2.me/theorems/e4392165-3b3f-4cc8-aec4-7ef9193cbd8b
-- title:
--   Model vocabulary — Strict diagonal dominance implies a faithful form
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The finite real table is supplied. Symmetry and strict diagonal dominance are explicit sufficient hypotheses, not derived Foundation laws or necessary conditions.
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
--   Theorems.Thm_APFPaper5_K1_dominant_table; Pullbacks v39, SHA-256 1f8186905d9da6a381e4c3158ed164dbb38e2f4e43389d17d2e10c923610fd80. Theorems.Thm_APFPaper5_K1_dominant_table; pullbacks v39; SHA-256 1f8186905d9da6a381e4c3158ed164dbb38e2f4e43389d17d2e10c923610fd80

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_dominant_table
title: For any number of marks, shared or joint: a symmetric table in which each mark's own entry exceeds the total size of its entries with all the others is bilinear with a nonnegative and faithful diagonal
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:44 HST: "Derive all items stil owed for k1". Item owed in
 MEMO_pullbacks_pass36_K1_finish_shared_and_joint_2026-11-14: three or more distinctions with joint
 records. Builder seat: tableForm, IsBilinear, FaithfulNonnegDiagonal, tableForm_isBilinear.
standing: A THEOREM about real tables (the classical statement that a symmetric, strictly diagonally
 dominant table with positive diagonal is positive definite). No input is consumed.
what this file says: read on a table of shared costs, where the diagonal entry is a distinction's own cost
 and an off-diagonal entry is what two distinctions save by sharing (positive) or add by a joint record
 (negative): if each distinction costs more than the sizes of all its savings and additions with the
 others put together, K1's typed conditions hold for the table. The signs do not matter.
what this file does NOT say:
 - That the condition is necessary. It is sufficient only. A table can meet K1's conditions without it;
   for two marks the exact condition is the pair bound of pass 36, which is weaker.
 - That the condition holds in any physical context or follows from the eight.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K1



variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The size of the entry of two different marks; nothing for a mark with itself. -/
def offSize (G : ι → ι → ℝ) (i j : ι) : ℝ := if i = j then 0 else |G i j|





end APFPaper5.K1


