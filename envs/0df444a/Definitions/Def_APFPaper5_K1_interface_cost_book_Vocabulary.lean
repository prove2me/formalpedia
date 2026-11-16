-- Prove2me | Definitions.Def_APFPaper5_K1_interface_cost_book_Vocabulary
-- name    : APFPaper5_K1_interface_cost_book_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:37:19.692812+00:00
-- url     : https://prove2.me/theorems/95bd87c4-f515-4240-872d-1288de8283ee
-- title:
--   Model vocabulary — Guarded B05 and nonnegative higher-order book weights give finite-table positivity
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   For an admissible finite indexed family with every member tested and support-novel over its complement, B05 gives positive singleton book weights at least eps. Assuming hshared for every subset of cardinality at least two then gives bilinearity and faithful nonnegative diagonal. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. hshared is NOT ADOPTED or derived. It requires nonnegative higher-order Mobius/book weights, not merely pairwise nonnegative shared costs. Expose hregion,htested,hnov and exact B05 guards. Pass30/31 are outside this batch and do not refute the fully conditioned theorem; the pass30 residue example did not check the counted-family premises.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. hshared is NOT ADOPTED or derived. It requires nonnegative higher-order Mobius/book weights, not merely pairwise nonnegative shared costs. Expose hregion,htested,hnov and exact B05 guards. Pass30/31 are outside this batch and do not refute the fully conditioned theorem; the pass30 residue example did not check the counted-family premises.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_interface_cost_book; Sib v66 / pullbacks v22, SHA-256 58ee305ebea34f8a0fe99e90449a861888366cfe12adc3e63deafd414f99ff06. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper5_K1_interface_cost_book.lean

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_interface_cost_book
title: On any source data of the declared forms, for a counted family, the declared B05 makes each distinction's own record cost at least the floor; if in addition no record needed by two or more of them has negative cost, the table of shared costs meets K1's typed conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:26: "The record ledger can be derived - each item in it". 20:31:
 "Yes". Thm_APFPaper5_K1_cost_book (this seat). Declared input B05 in its declared form
 APFB05.MarginalFloor (Def_APF_B05_DeclaredInput_r2). Builder seat: APFB05.familyAdmissible_of_subset,
 APFPaper1.Source.familyCost_nonneg.
standing: THEOREMS ON THE DECLARED FORMS. No record ledger is assumed, no reading about bills is used, and
 the availability sentence is not used. The premises are:
 - hB05: the DECLARED INPUT B05.
 - hregion, htested, hnov: the family is a counted family in the sense the author ruled as call 2 at 19:57
   HST (finite, within capacity, each member tested and support-novel over the others).
 - hshared: no record needed by two or more of the counted distinctions has negative cost. This is the ONE
   premise that is neither an input nor a definition. It is a property of the family's costs: sharing
   never costs extra, at each order. It is NOT DERIVED here and NOT ADOPTED. Whether it follows from
   anything the author holds, or fails in a world meeting the eight, is not settled.
what this file says:
 1. counted_own_record_ge_floor: under B05, in a counted family, the record a distinction needs alone
    costs at least the floor.
 2. counted_family_satisfies_K1_of_nonneg_shared: with hshared as well, the table of shared costs of the
    counted family is bilinear with a nonnegative and faithful diagonal.
what this file does NOT say: that hshared holds. That the role exchange is anything but the identity.
 Anything about orientation, K2 to K6 or the K3 models. No lane. No claim that the transfer is forced, that
 the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_cost_book_Vocabulary
import Theorems.Thm_APFPaper5_K1_book_empty
import Theorems.Thm_APFPaper5_K1_book_singleton
import Theorems.Thm_APFPaper5_K1_cost_table_satisfies_K1
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P R Record : Type*} [DecidableEq D] {ι : Type} [Fintype ι] [DecidableEq ι]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)

/-- The cost of the sub-families of an indexed family of distinctions. -/
noncomputable def indexedCost (dist : ι → D) : Finset ι → ℝ :=
  fun S => familyCost wholeResource calibration maintained sufficient usesToRealize (S.image dist)





end

end APFPaper5.K1


