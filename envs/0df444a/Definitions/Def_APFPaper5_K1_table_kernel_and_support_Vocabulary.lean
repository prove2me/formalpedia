-- Prove2me | Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
-- name    : APFPaper5_K1_table_kernel_and_support_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:47:15.038416+00:00
-- url     : https://prove2.me/theorems/292be978-6f0a-4445-ae47-b477bc8c99e5
-- title:
--   Model vocabulary — Kernels and conditional counting bounds for finite weighted incidence tables
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   For nonnegative weights, zero diagonal form is exactly cancellation on every positive atom; faithfulness is absence of a nonzero such vector. Identical supported marks give a null difference, disjoint supports score zero, and private records of weight at least eps bound cardinality times eps by total support cost. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Finite marks/atoms, hw and the particular hsame/hdisj/hpriv assumptions must be retained. The row-equality lemma uses nonzero weights and does not require their positivity. Division by eps requires eps positive; the formal bound itself is multiplicative. No physical score or general dimension bound is established.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Finite marks/atoms, hw and the particular hsame/hdisj/hpriv assumptions must be retained. The row-equality lemma uses nonzero weights and does not require their positivity. Division by eps requires eps positive; the formal bound itself is multiplicative. No physical score or general dimension bound is established.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_table_kernel_and_support; Sib v66 / pullbacks v22, SHA-256 61e587dcab90d100333ed0e03852e7348044a522c28c7c516f691ae0d282561d. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper5_K1_table_kernel_and_support.lean

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_table_kernel_and_support
title: The form of a record-book table vanishes exactly on the combinations every positively weighted record cancels; marks with the same records merge, marks with disjoint records score zero, and a family with a private record of cost at least eps per member numbers at most its cost over eps
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:358-366 and 383-388 (the pairing of K1 is taken on the quotient by the
 left and right radicals: "contextual score-null relations lie in its radicals"), 3037-3041 (K1: a faithful
 nonnegative diagonal). Paper 1 Supplement v9.28:2502-2516 (Definition, support-independent resolution:
 exact witness supports, ORTHOGONALITY "the supports are pairwise disjoint", support-local additive
 accounting), 3124-3131 (two formal distinctions reading digits of one maintained register "merge, and the
 counting theorem charges one floor, not two"), 3612 (Example, shared coarse record), 1202 ("cardinality
 counting overcharges; use chain rank").
 Thm_APFPaper5_K1_record_book_table (seat 01WrrBvu): atomTable_form, atomTable_nonneg, and atomTable_faithful
 under a single-mark atom per mark. Thm_APFPaper5_K1_weighted_record_model (seat 01WrrBvu):
 atomTable_eq_sum_inter. Thm_APFPaper5_K1_records_meet_continuity_at_resolution (seat 01WrrBvu),
 resolution_floor_of_capacity, whose hypothesis n * eps <= C is supplied here by card_mul_le_sum_of_private.
 Codebank: nothing on the kernel of a shared-cost table (apf/aboutness_occupancy_section.py uses "radical"
 for a different object).
consumes_inputs: none. Ordinary mathematics on a record book: a finite type of atoms (records), Boolean
 marks on it, nonnegative weights.
named_hypotheses: none beyond the record book. In card_mul_le_sum_of_private, hpriv (each member of the
 family has a record of cost at least eps that no other member needs) is a hypothesis on the family in
 hand.
statement: (atomTable_form_eq_zero_iff) with nonnegative weights, the form vanishes at x exactly when, at
 every atom of positive weight, the x-weighted count of the marks holding it is zero.
 (atomTable_faithful_iff) so the diagonal is faithful exactly when no nonzero x is cancelled at every atom
 of positive weight. (atomTable_row_eq_of_same_marks) two marks that hold the same atoms of positive weight
 have the same row. (atomTable_merge_of_same_marks) and the form vanishes at their difference (markDiff), which is not
 zero: the table is not faithful, and the two are one direction after the quotient.
 (atomTable_eq_zero_of_disjoint) two marks with no record in common score zero.
 (card_mul_le_sum_of_private) if each member of S has a record of cost at least eps that no other member
 needs, the size of S times eps is at most the cost of the records S needs.
not_claimed: that a physical score is a record-book table; that any family of distinctions has private or
 disjoint records. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed,
 or that Born is derived.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]







/-- The coefficient vector "mark i less mark j". -/
def markDiff [DecidableEq ι] (i j : ι) : ι → ℝ :=
  fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)







end APFPaper5.K1


