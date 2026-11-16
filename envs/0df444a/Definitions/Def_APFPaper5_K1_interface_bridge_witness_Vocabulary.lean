-- Prove2me | Definitions.Def_APFPaper5_K1_interface_bridge_witness_Vocabulary
-- name    : APFPaper5_K1_interface_bridge_witness_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:46:28.102827+00:00
-- url     : https://prove2.me/theorems/46951d33-6cb8-4774-85d6-494820e2868b
-- title:
--   Model vocabulary — A finite shared-plus-private record book witnesses the bridge hypotheses
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Supplies one shared record and one private record per index, all unit-priced, with every finite record set a protocol. The bridge applies; singleton shared costs are two on the diagonal and one off it. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. A nonvacuity witness for the conditional bridge, not a world of all eight original forms and not a physical interface. Fintype index is explicit.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. A nonvacuity witness for the conditional bridge, not a world of all eight original forms and not a physical interface. Fintype index is explicit.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_interface_bridge_witness; Sib v66 / pullbacks v22, SHA-256 06c30dd08392db174f046e2ea867a087c55142867caabf1292f4d6dbde73c544. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper5_K1_interface_bridge_witness.lean

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_interface_bridge_witness
title: The hypotheses of the K1 interface bridge hold together on a book with one record that all distinctions share and one private record each, and there the shared cost of two different distinctions is 1 and of a distinction with itself is 2
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFPaper5_K1_interface_bridge (this seat). Builder seat: APFB05.weighted_record_model_satisfies_floor,
 APFPaper5.K1.recordModel_supportNovel_of_needs_own_record, APFPaper5.K1.familyCost_weighted.
standing: A WORLD. It shows only that the hypotheses of interface_region_satisfies_K1_of_floor can hold
 together, with records that are really shared. It is not a claim about any physical interface.
what this file says: on finitely many distinctions, with records `none` (needed by all) and `some i` (needed
 by i alone), every record costing 1 and the floor 1, the bridge applies; the table it speaks of has 2 on
 the diagonal and 1 off it.
what this file does NOT say: that the declared inputs force this book or any book. No lane. No claim that
 the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor
import Theorems.Thm_APFPaper5_K1_weighted_marginal_ge
import Theorems.Thm_APFB05_weighted_record_model_satisfies_floor
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1.BridgeWitness

variable {ι : Type} [DecidableEq ι]

/-- Distinction `i` needs the shared record `none` and its own record `some i`. -/
def fam (i : ι) : Finset (Option ι) := {none, some i}

/-- Every record costs 1. -/
def w : Option ι → NNReal := fun _ => 1











end APFPaper5.K1.BridgeWitness


