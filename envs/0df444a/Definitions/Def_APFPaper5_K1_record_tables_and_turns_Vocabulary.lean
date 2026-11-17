-- Prove2me | Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
-- name    : APFPaper5_K1_record_tables_and_turns_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:22:34.917814+00:00
-- url     : https://prove2.me/theorems/acf37d26-6766-494c-99fd-6037a55fce3a
-- title:
--   Model vocabulary — Record-table bounds and a supplied turn table
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Nonnegative Boolean record tables obey the three-index bound. The supplied turnTable violates it for 0<x<1 but at x=1/2 is realized on real combinations of classes. Index 0 is the middle index, with neighbours 1 and 2. No physical turn or state realization is derived.
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
--   Theorems.Thm_APFPaper5_K1_record_tables_and_turns; Pullbacks v39, SHA-256 38d1144a58ac211ab5939a800f24a312157f10856ffeb5fdd016b73ec8af01e6. Theorems.Thm_APFPaper5_K1_record_tables_and_turns; pullbacks v39; SHA-256 38d1144a58ac211ab5939a800f24a312157f10856ffeb5fdd016b73ec8af01e6

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_record_tables_and_turns
title: Every table of a record ledger obeys a three-distinction bound; the table of a mark, its turn and its double turn breaks it for every turn strictly between none and the quarter turn; that table is on K1's classes all the same, as combinations that are not record lists
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 13:41 HST: "Let's take a harder look at C - quantum implications match?
 Gauge?" (NOTE_harder_look_at_C_quantum_and_gauge_2026-11-15). The builder seat's Def_APFPaper5_K1_MarkTable
 (atomTable: the table read off weights on the atoms of a record space), Thm_APFPaper5_K1_rank_three (the
 score between a mark and its turn is (1 + x) / 2) and its finding that a turn round obeys the rule for a
 turn taken twice (c to 2c^2 - 1) only for no turn or the quarter turn. This seat's
 Def_APFPaper5_K1_SourcePartyScore (the ruled score on source data).
standing: ordinary mathematics on the typed tables. The turn table is a SUPPLIED table of three numbers; that
 a physical turn has it is the builder seat's conditional result and standard quantum theory, not a result
 of this file.
consumes_inputs: none.
theorems:
 - (atomTable_triangle) for a record ledger with no negative cost and any three distinctions i, j, k: the
   score of i with j, plus the score of i with k, minus the score of j with k, is at most the score of i
   with itself. (atomTable_le_diag) the score of two is at most the score of either with itself.
 - (sourcePartyScore_triangle) the ruled score on source data of the declared forms obeys it.
 - (turnTable entries, turnTable_symm) the turn table: index 1 a mark, 0 the mark turned once, 2 the mark
   turned twice; unit diagonal; (1 + x) / 2 between neighbours; x * x between the ends.
 - (turnTable_breaks_triangle) for 0 < x < 1 the turn table breaks the bound at the middle index.
 - (no_record_ledger_has_turnTable, no_three_distinctions_have_turnTable) so no record ledger with no
   negative cost has the turn table, and no three distinctions have it as their ruled score.
 - (turnTable_half_form, turnTable_half_nonneg, turnTable_half_faithful) at x = 1/2 (3/4, 3/4, 1/4) the
   turn table is symmetric with a faithful nonnegative diagonal: it meets what K1 asks of a table.
 - (ownTable_eq, turnTable_on_classes) and it is the table of three CLASSES of a record ledger: three
   distinctions with one own record each, of costs 1, 7/16 and 3/14, and the combinations d0,
   3/4 d0 + d1, 3/4 d0 - 5/7 d1 + d2. (turnClass_negative) the third has a negative coefficient.
reading: a turn strictly between none and the quarter turn cannot carry a distinction to a distinction with
 the record ledger's score kept. The numbers a turn needs are in K1's space of classes, on combinations that
 are not lists of records.
not claimed: that any hold is such a turn. That the combinations are states, preparations or tests. Anything
 about which combinations exist. No lane. No claim that the transfer is forced, that the carrier gap is
 closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_MarkTable
import Definitions.Def_APFPaper5_K1_SourcePartyScore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

universe uI uW

/-! ### Every table of a record ledger obeys a three-distinction bound -/







/-! ### The table of a mark, its turn and its double turn -/

/-- Index 1 is a mark, 0 the mark turned once, 2 the mark turned twice. `x` is the number of the turn: the
score between neighbours is `(1 + x) / 2`, between the two ends `x * x`. -/
noncomputable def turnTable (x : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then 1 else if i = 0 ∨ j = 0 then (1 + x) / 2 else x * x

















/-! ### At x = 1/2 the turn table meets what K1 asks of a table -/







/-! ### The turn table on the classes of a record ledger -/

/-- Three records, one for each of three distinctions, of costs 1, 7/16 and 3/14. -/
noncomputable def ownCost : Fin 3 → ℝ := fun a => if a = 0 then 1 else if a = 1 then 7 / 16 else 3 / 14

/-- Each distinction is listed against its own record and no other. -/
def ownMark : Fin 3 → Fin 3 → Bool := fun i a => decide (i = a)

/-- Three combinations of the three distinctions: d0; 3/4 d0 + d1; 3/4 d0 - 5/7 d1 + d2. -/
noncomputable def turnClass (k : Fin 3) : Fin 3 → ℝ :=
  fun i =>
    if k = 0 then (if i = 0 then 1 else 0)
    else if k = 1 then (if i = 0 then 3 / 4 else if i = 1 then 1 else 0)
    else (if i = 0 then 3 / 4 else if i = 1 then -(5 / 7) else 1)







end APFPaper5.K1


