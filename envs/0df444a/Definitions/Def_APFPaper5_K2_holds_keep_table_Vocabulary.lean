-- Prove2me | Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
-- name    : APFPaper5_K2_holds_keep_table_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:30:46.070894+00:00
-- url     : https://prove2.me/theorems/d77d5815-2897-45a2-a196-e5700909c94c
-- title:
--   Model vocabulary — Consequences of a hold preserving its table
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   KeepsTable remains explicit, as do symmetry, faithful diagonal and SourceCounted where used. The author-adopted reading is not a derivation from installed inputs. Inverse permutations and null-combination closure do not establish admitted inverse words or full K2 closure.
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
--   Theorems.Thm_APFPaper5_K2_holds_keep_table; Pullbacks v39, SHA-256 504b1bcaf41d4218cb5bab47f8fe935a16187393f6044caef3b236d53fed36dd. Theorems.Thm_APFPaper5_K2_holds_keep_table; pullbacks v39; SHA-256 504b1bcaf41d4218cb5bab47f8fe935a16187393f6044caef3b236d53fed36dd

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_holds_keep_table
title: Holds keep K1's table: so a hold keeps the cost of every class, its reverse is its inverse, and the combinations of holds no score can see are closed under holds before, holds after and reversal
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 13:23 HST, "yes, hold keeps table", in answer to this seat's question "Does a
 hold keep K1's table, meaning two distinctions score the same as the two they are rearranged from?"
 (RULING_hold_keeps_table_2026-11-15). From that time KeepsTable is an ADOPTED READING of a hold. It remains
 a hypothesis of every Lean theorem that uses it, and FOUNDATION_INPUTS is unchanged.
source: Paper 5 Supplement v7.33:410-420 (orientation closure), 723-737 and 790-811 (the metric adjoint; a
 score family that is context saturated and adjoint saturated has a two-sided adjoint-stable null ideal),
 866-890 (the quotient is an involutive algebra). Def_APFPaper5_K2_HoldScore, Thm_APFPaper5_K2_hold_score.
 This seat's Thm_APFPaper5_K1_identity_exchange (the ruled score of a counted family: symmetric, with a
 faithful nonnegative diagonal).
consumes_inputs: none. No declared input is used as a hypothesis and none is proved.
definition: HoldKeepsLedger G sigma, five statements about a rearrangement and a table: the hold keeps K1's
 form; the score through it is K1's form with the inverse on the test side; reversing the two ends with the
 inverse in the channel gives the same score; the cost of what it makes of any class is not negative; and
 is zero only for the zero class.
theorems:
 - (keepsTable_id, keepsTable_comp, keepsTable_symm) doing nothing keeps the table; two holds that keep it,
   one after the other, keep it; the inverse of one that keeps it keeps it.
 - (hold_keeps_cost) a hold that keeps the table keeps the cost of every class.
 - (holdScoreNull_before) a combination of holds no score can see stays unseen when one hold is put before
   every hold in it. No hypothesis.
 - (holdScoreNull_after_of_keeps) and when a hold that keeps the table is put after every hold in it.
 - (holdScoreNull_reverse_of_keeps) and, for a symmetric table and holds that keep it, when every hold in
   it is replaced by its inverse.
 - (hold_keeping_table_package) for a symmetric table with a faithful nonnegative diagonal, a hold that
   keeps it satisfies HoldKeepsLedger.
 - (source_counted_hold_package) so does a hold that keeps the ruled score of a counted family on source
   data of the declared forms, for any cost of records that is never negative.
reading: for holds, the combinations no score can see form what Paper 5 calls a two-sided adjoint-stable
 ideal, and the adjoint of a hold is its inverse. That is K2's involutive quotient, for holds.
not claimed:
 - That the adopted reading follows from the declared inputs. It is the author's reading of a hold.
 - That the reverse of a hold is an admitted word. The inverse rearrangement exists as a map of classes;
   whether a word of the world runs as it is not typed.
 - Anything about words that are not holds, or about sides. A side does not enter the score.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
   derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_id
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
import Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
import Theorems.Thm_APFPaper5_K2_exists_rearranges_of_nothingDrawn
import Theorems.Thm_APFPaper5_K2_heldAfter_id
import Theorems.Thm_APFPaper5_K2_heldAfter_comp
import Theorems.Thm_APFPaper5_K2_heldAfter_add
import Theorems.Thm_APFPaper5_K2_heldAfter_smul
import Theorems.Thm_APFPaper5_K2_heldAfter_markClass
import Theorems.Thm_APFPaper5_K2_holdScore_id
import Theorems.Thm_APFPaper5_K2_holdScore_marks
import Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
import Theorems.Thm_APFPaper5_K2_holdScore_eq_sum
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
import Theorems.Thm_APFPaper5_K2_keeps_of_reverse_is_inverse
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_iff_keeps
import Theorems.Thm_APFPaper5_K2_tableForm_heldAfter_of_keeps
import Theorems.Thm_APFPaper5_K2_ends_reversed_of_keeps
import Theorems.Thm_APFPaper5_K2_keepsTable_diag
import Theorems.Thm_APFPaper5_K2_not_keepsTable_of_diag_ne
import Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
import Theorems.Thm_APFPaper5_K2_source_hold_score_marks
import Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uK
variable {ι : Type uI}

/-! ### The holds that keep the table -/







section
variable [Fintype ι]



/-! ### The combinations no score can see, under holds before, holds after and reversal -/







/-! ### What the adopted reading gives, in one statement -/

/-- The hold keeps K1's form; the score through it is K1's form with the inverse on the test side; reversing
the two ends with the inverse in the channel gives the same score; the cost of what it makes of a class is
not negative, and is zero only for the zero class. -/
def HoldKeepsLedger (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) : Prop :=
  (∀ x y : ι → ℝ, tableForm G (heldAfter sigma x) (heldAfter sigma y) = tableForm G x y) ∧
  (∀ x y : ι → ℝ, holdScore G sigma x y = tableForm G x (heldAfter sigma.symm y)) ∧
  (∀ x y : ι → ℝ, holdScore G sigma x y = holdScore G sigma.symm y x) ∧
  (∀ x : ι → ℝ, 0 ≤ tableForm G (heldAfter sigma x) (heldAfter sigma x)) ∧
  (∀ x : ι → ℝ, tableForm G (heldAfter sigma x) (heldAfter sigma x) = 0 → x = 0)



end

/-! ### On source data of the declared forms, for the ruled score of a counted family -/

section
open APFPaper1 APFPaper1.Source
variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
  [Fintype Record]



end

end APFPaper5.K2


