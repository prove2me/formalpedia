-- Prove2me | Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
-- name    : APFPaper5_K1_interface_bridge_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:33:27.737412+00:00
-- url     : https://prove2.me/theorems/3250d683-a4c5-4c98-a5b8-697a43e4e76c
-- title:
--   Model vocabulary — Conditional equality with a record model and finite-table positivity
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   With additive bills, maintained=kept, necessary supports and exact service, identifies family cost and shared costs with weighted record sums. Private positive records give table faithfulness; guarded B05 plus tested admissible support-novel families and scoped availability supplies those private positive records. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Keep hbill, hkept, hneed, ExactlyServed, hprivate or the complete B05/hscoped/hregion/htested/hnov alternative. Fintype Record and Fintype index are required for the table conclusions. No original-interface binding is certified merely because parameters carry source names.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Keep hbill, hkept, hneed, ExactlyServed, hprivate or the complete B05/hscoped/hregion/htested/hnov alternative. Fintype Record and Fintype index are required for the table conclusions. No original-interface binding is certified merely because parameters carry source names.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_interface_bridge; Sib v66 / pullbacks v22, SHA-256 189aab98d30bc7e74e263c3d4896d69bed688e0bef01cf65b0d28362ee12eded. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper5_K1_interface_bridge.lean

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_interface_bridge
title: On source data of the declared forms, read as adopted on 2026-11-14, the ledger's own family cost is the record model's cost, the shared cost of two distinctions is the weight of the records they share, and the table of shared costs of a region's counted distinctions meets K1's typed conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST 19:31: "Do the k1 bridge". HYPOTHESIS_LEDGER_2026-11-13 line 46 (the K-layer
 model theorems lack "a binding to an original interface, which is one bridge"). Paper 5 Supplement
 v7.33:3037-3040 (K1). Builder seat: Def_APFPaper5_K1_RecordModel (recordModelCost is the ledger's familyCost
 on one supplied set of data), Thm_APFPaper5_K1_weighted_record_model (recordModel_satisfies_K1). This seat:
 Thm_APFPaper1_supportNovel_of_private_record (familyCost_eq_sum_of_available). Declared input B05 in its
 declared form APFB05.MarginalFloor (Def_APF_B05_DeclaredInput_r2). APFB05.familyAdmissible_of_subset.
standing: CONDITIONAL THEOREMS. They bind the K1 record model to any source data of the declared forms. The
 hypotheses, and where each stands:
 - hbill, "the bill is the sum of the costs of the records kept": ADOPTED READING (this seat's reading of the
   author's 13:00 HST reply, confirmed 16:45 HST; RULING_named_calls_2026-11-14).
 - hkept, "what a protocol maintains is a finite set of records": a TYPING CLAUSE of this seat. Not ruled.
 - hneed, "serving a distinction needs that distinction's own records": ADOPTED READING (16:45 HST).
 - hscoped, "every family within capacity has a protocol keeping exactly what it needs": ADOPTED READING in
   the scoped wording (17:29 HST; RULING_calls_after_pass18_2026-11-14).
 - hB05: the DECLARED INPUT B05, consumed in its declared form.
 - hregion, htested: the region's counted distinctions are tested and admissible within capacity. A
   hypothesis on the region in hand.
 - hnov, "each counted distinction is support-novel over the others": NAMED, NOT ADOPTED
   (RULING_fineness_across_regions_2026-11-14).
 - hprivate (the first form only), "each counted distinction has a record of positive cost that no other of
   them needs": the private record is the ADOPTED READING in wording (ii) (17:29 HST); that its cost is
   positive is NOT ADOPTED. private_positive_record_of_floor derives both from hB05 and hnov.
 None of the readings is installed in FOUNDATION_INPUTS. Only the author edits it.
what this file says:
 1. familyCost_eq_recordModelCost. For any family that some protocol serves by keeping exactly what it
    needs, the ledger's family cost equals the record model's cost of that family. The record model is then
    not a supplied model: it is the interface's own cost.
 2. interface_sharedCost_eq_shared_records. The shared cost of two distinctions, built from the ledger's
    family cost alone, is the total cost of the records both need.
 3. interface_region_satisfies_K1. For a region's counted distinctions the table of those shared costs is
    bilinear and has a faithful nonnegative diagonal under the identity role exchange (K1's typed
    conditions as the builder seat typed them), given a private record of positive cost for each.
 4. private_positive_record_of_floor. B05's floor on a support-novel distinction gives it a record of
    positive cost that the family does not need.
 5. interface_region_satisfies_K1_of_floor. The same K1 conditions from the declared B05, the adopted
    readings, and the named sentence hnov, with no separate premise on private records.
what this file does NOT say:
 - That the shared cost is Paper 5's ordered score. The author deferred the identification of a score off
   the record-book side (ruling 4 of the eight decisions, 2026-11-12). On the record-book side the adopted
   score is the shared count (Def_APFPaper5_K1_SharedCount). No score is supplied here, so K1.a
   (Linearizes) is not stated.
 - That the role exchange is anything but the identity. The table is symmetric, so tests and preparations
   are the same space here. Paper 5's typed boundary-role isomorphism in general is not constructed.
 - Anything about K3. The binding of the K3 models' profiles to original profiles (ledger row C12) is a
   different bridge and is not touched.
 - Any bound on the number of directions. Capacity over the floor bounds the count of counted distinctions
   only with a private record for each (Thm_APFPaper5_K1_table_kernel_and_support).
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper1_Source_sum_needed_le_bill
import Theorems.Thm_APFPaper1_Source_familyCost_eq_sum_of_available
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record_count
import Theorems.Thm_APFPaper1_Source_marginal_ge_of_private_record
import Theorems.Thm_APFPaper1_Source_each_private_excludes_riding
import Theorems.Thm_APFPaper1_Source_supportNovel_of_each_private
import Theorems.Thm_APFPaper1_Source_marginal_zero_of_no_own_record
import Theorems.Thm_APFPaper1_Source_needs_own_record_of_supportNovel
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
import Definitions.Def_APF_B05_DeclaredInput_r2

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record) (cost : Record → NNReal)

/-- Some protocol keeps exactly the records the family `S` needs, and serves `S`. -/
def ExactlyServed (S : Finset D) : Prop :=
  ∃ p : P, kept p = S.biUnion fam ∧ ∀ d ∈ S, ∃ sigma : Set Record,
    sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma













end

end APFPaper5.K1


