-- Prove2me | Definitions.Def_APFPaper5_K1_cost_book_Vocabulary
-- name    : APFPaper5_K1_cost_book_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:46:00.632737+00:00
-- url     : https://prove2.me/theorems/23fa667d-23c2-421c-8fca-c73785906f0f
-- title:
--   Model vocabulary — A signed subset-book representation of any finite family-cost function
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Defines a recursive subset book and proves the cost identity with an empty-family offset; singleton weights are marginals over all other indices. Shared singleton costs equal a weighted incidence table. Nonnegative empty cost and all book weights, with positive singleton weights, give bilinearity and faithful nonnegative diagonal. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. The book is a signed algebraic representation, not a positive physical record ledger. All weights need not be nonnegative; the empty offset is carried on the universal record for the table identity. No protocol-bill representation, uniqueness theorem or completely-alternating characterization is proved.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. The book is a signed algebraic representation, not a positive physical record ledger. All weights need not be nonnegative; the empty offset is carried on the universal record for the table identity. No protocol-bill representation, uniqueness theorem or completely-alternating characterization is proved.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_cost_book; Sib v66 / pullbacks v22, SHA-256 88667832d19995dd1e5de3f3f99b527fb47ae2c9b76133e5a230f87fffccd8e2. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper5_K1_cost_book.lean

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_cost_book
title: Every cost on the families of a finite set of distinctions is the cost of a book of records, one record for each set of distinctions and needed by exactly those; the shared cost of two distinctions is the cost of the records both need; and where no record has negative cost and each distinction's own record has positive cost, the table meets K1's typed conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:26: "The record ledger can be derived - each item in it". 20:31:
 "Yes" (to typing the derivation: the book of a cost function, the identity, and K1 from B05 plus
 nonnegative shared costs). NOTE_record_ledger_can_be_derived_2026-11-14. Builder seat:
 Def_APFPaper5_K1_MarkTable (atomTable), Def_APFPaper5_K1_SharedCost, record_book_table_satisfies_K1.
 The mathematics is inversion over subsets (Moebius inversion on a finite Boolean lattice), stated here
 through its defining recursion.
standing: THEOREMS ABOUT ANY REAL-VALUED FUNCTION OF FINITE FAMILIES. No input is consumed and no reading is
 used. Nothing is assumed of the cost except, in the last theorem, the three stated sign conditions.
what this file says:
 1. bookCost, book: the cost of the record needed by exactly the members of T, defined by the recursion
    "what T adds over the rest, less the costs of the records of the proper subsets of T".
 2. cost_eq_sum_book: the cost of a family is the cost of the empty family plus the costs of the records
    that some member of the family needs. An identity, for every cost function.
 3. book_empty, book_singleton: the record of no distinction costs nothing; the record a distinction needs
    alone costs what that distinction adds over all the others.
 4. sharedCost_eq_atomTable_book: the shared cost of two distinctions is the total cost of the records
    both need, the cost of the empty family being carried on the record that all need.
 5. cost_table_satisfies_K1: if the empty family costs at least nothing, no record has negative cost, and
    each distinction's own record has positive cost, the table of shared costs is bilinear with a
    nonnegative and faithful diagonal under the identity role exchange.
what this file does NOT say:
 - That the record costs are nonnegative. They can be negative; that is a property of the cost function.
 - That the book is the only one (it is, by the same inversion; not typed), or the closed alternating-sum
   formula for a record's cost (not typed), or that nonnegative record costs is the same as the cost being
   completely alternating (classical; not typed).
 - Anything about a single protocol's bill.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Definitions.Def_APFPaper5_K1_SharedCost
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace APFPaper5.K1

variable {ι : Type} [DecidableEq ι]

/-- The cost of the record needed by exactly the members of `A`, from `g` ("what a set adds over the
rest"): `g A` less the costs of the records of the proper subsets of `A`. -/
noncomputable def bookCost (g : Finset ι → ℝ) : Finset ι → ℝ :=
  Finset.strongInduction (p := fun _ => ℝ)
    (fun A ih => g A - ∑ T ∈ A.ssubsets.attach, ih T.1 (Finset.mem_ssubsets.mp T.2))





variable [Fintype ι]

/-- What a set of distinctions adds over all the others. -/
def addsOverRest (f : Finset ι → ℝ) (U : Finset ι) : ℝ := f Finset.univ - f Uᶜ

/-- The book of a cost function: the cost of the record needed by exactly the members of `T`. -/
noncomputable def book (f : Finset ι → ℝ) : Finset ι → ℝ := bookCost (addsOverRest f)







/-- The weights of the book with the cost of the empty family carried on the record that all need. -/
noncomputable def bookWeight (f : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  book f T + (if T = Finset.univ then f ∅ else 0)





end APFPaper5.K1


