-- Prove2me | Definitions.Def_APFPaper5_K1_shared_record_books_Vocabulary
-- name    : APFPaper5_K1_shared_record_books_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:35:17.457441+00:00
-- url     : https://prove2.me/theorems/1f472852-8114-446d-8d03-a2f147c18085
-- title:
--   Model vocabulary — Two supplied record books separate support novelty from linear rank
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Under positive record weights, record-model novelty is exactly a missing required record. A single shared record gives unit nonempty-family cost and a nonfaithful form for at least two indices. A three-index book has no private records, a faithful form, every support-novel increment at least one, and total cost 21/10. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. These are record books, not worlds of all eight forms. The cheap book does not have each index novel over all the others, so it is not a counterexample to the counted-family bridge or its bound. Formal label count is not support-independent capacity count.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. These are record books, not worlds of all eight forms. The cheap book does not have each index novel over all the others, so it is not a counterexample to the counted-family bridge or its bound. Formal label count is not support-independent capacity count.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_shared_record_books; Sib v66 / pullbacks v22, SHA-256 5f2cb8a13ff5f70388d8fcbe769e915f32b0045b3cbc71e484dc68159d75b9d4. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper5_K1_shared_record_books.lean

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_shared_record_books
title: Two record books with shared records: in one, any number of distinctions ride one record at one cost and the form has one direction; in the other, three distinctions with no private record have a faithful form while their cost over the marginal floor is 2.1
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3612 (Example, shared coarse record), 1824 and 2753 (the increment of a
 derived discriminator vanishes), 1826 (the count "concerns support-novel increments, not all predicates,
 state labels, or a representation's dimension"), 3124-3131 (the merge prescription). Paper 5 Supplement
 v7.33:232-238 (two forms of finite rank; the uniform bound on dimension is the stronger one).
 Def_APFPaper5_K1_RecordModel (seat 01WrrBvu): the model where every finite set of records is a protocol.
 Thm_APFPaper5_K1_table_kernel_and_support and Thm_APFPaper1_supportNovel_of_private_record (this seat).
 Thm_APFPaper5_K1_records_meet_continuity_at_resolution (seat 01WrrBvu): its fineness floor assumes every
 distinction of a region is charged a floor, and does not claim it.
consumes_inputs: none. These are record books (source data of the family-cost definition), NOT worlds
 meeting the eight declared forms: no states, continuations or alignments are supplied.
named_hypotheses: none.
statement: (recordModel_supportNovel_iff) in the record model with every record of positive cost, d is
 support-novel over S exactly when d needs a record S does not need.
 COARSE BOOK, n distinctions, one record of cost 1 needed by all: (coarse_cost) every nonempty family costs
 1, whatever n is. (coarse_marginal_zero) adding a distinction to a nonempty family adds nothing.
 (coarse_not_novel) no distinction is support-novel over a nonempty family. (coarse_score) every two
 distinctions score 1, the same as each scores with itself. (coarse_not_faithful) for n at least 2 the form
 is not faithful.
 CHEAP-SHARED BOOK, three distinctions needing {a,b,c}, {a,b}, {a,c}, with a costing 1/10 and b, c costing
 1: (cheap_no_private) no distinction has a record the others do not need. (cheap_faithful) the form is
 faithful. (cheap_floor) every support-novel addition raises the cost by at least 1. (cheap_cost_all) the
 three together cost 21/10. So three independent directions sit at capacity over floor 2.1.
not_claimed: that either book is a world of the framework, or that either is excluded. That the coarse book's
 n distinctions are n distinctions in the Supplement's counting sense: by the Supplement's own prescription
 they merge. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
-/
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper1_Source_sum_needed_le_bill
import Theorems.Thm_APFPaper1_Source_familyCost_eq_sum_of_available
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record_count
import Theorems.Thm_APFPaper1_Source_marginal_ge_of_private_record
import Theorems.Thm_APFPaper1_Source_each_private_excludes_riding
import Theorems.Thm_APFPaper1_Source_supportNovel_of_each_private
import Theorems.Thm_APFPaper1_Source_marginal_zero_of_no_own_record
import Theorems.Thm_APFPaper1_Source_needs_own_record_of_supportNovel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v



/-! ### The coarse book: n distinctions, one record -/

namespace CoarseBook

/-- The one record costs 1. -/
def w : Unit → NNReal := fun _ => 1

/-- Every distinction needs the one record. -/
def fam (n : ℕ) : Fin n → Finset Unit := fun _ => {()}













end CoarseBook

/-! ### The cheap-shared book: three distinctions, no private record, a faithful form -/

namespace CheapBook

/-- Record a (number 0) costs 1/10; records b and c (numbers 1 and 2) cost 1. -/
noncomputable def w : Fin 3 → NNReal := fun a => if a = 0 then 1 / 10 else 1

/-- The three distinctions need {a, b, c}, {a, b} and {a, c}. -/
def fam : Fin 3 → Finset (Fin 3) := ![{0, 1, 2}, {0, 1}, {0, 2}]

























end CheapBook

end APFPaper5.K1


