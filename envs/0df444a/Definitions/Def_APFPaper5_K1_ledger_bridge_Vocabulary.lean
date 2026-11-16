-- Prove2me | Definitions.Def_APFPaper5_K1_ledger_bridge_Vocabulary
-- name    : APFPaper5_K1_ledger_bridge_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T00:03:22.187609+00:00
-- url     : https://prove2.me/theorems/ec6d6fc3-e5aa-4c19-a5a0-99de8855e1c2
-- title:
--   Model vocabulary — A finite counted record ledger satisfies table conditions under B05 and availability
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Instantiates the conditional bridge with RecordLedger, proves exact-service cost identities, and gives the table conclusion under guarded B05, LedgerAvailable and LedgerCounted. Includes a shared-plus-private ledger witnessing those hypotheses. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Correct the two-premises-only gloss: Fintype Record, finite index and hcounted (admissibility, testing, novelty) remain assumptions, as do the restricted representation, hB05 and havail. Defining counted does not prove hcounted. Neither the representation nor availability is installed in FOUNDATION_INPUTS.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Correct the two-premises-only gloss: Fintype Record, finite index and hcounted (admissibility, testing, novelty) remain assumptions, as do the restricted representation, hB05 and havail. Defining counted does not prove hcounted. Neither the representation nor availability is installed in FOUNDATION_INPUTS.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_ledger_bridge; Sib v66 / pullbacks v22, SHA-256 5c2061349992fecfb2b8ffc9b0c4d97856926d5393928b1c271fd529f01f867a. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Theorems\Thm_APFPaper5_K1_ledger_bridge.lean

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_ledger_bridge
title: On finite restricted record-ledger data, guarded B05, availability and a counted-family hypothesis imply a bilinear score table with a faithful nonnegative diagonal
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's "Go" of 2026-11-14 20:09 HST (restate the bridge over the ledger and needs).
 Def_APFPaper1_RecordLedger, Def_APFPaper5_K1_LedgerScore, Thm_APFPaper1_RecordLedger_laws,
 Thm_APFPaper5_K1_interface_bridge and _families (this seat). Declared input B05 in its declared form
 APFB05.MarginalFloor (Def_APF_B05_DeclaredInput_r2). Builder seat: recordModel_satisfies_K1,
 APFB05.weighted_record_model_satisfies_floor, recordModel_supportNovel_of_needs_own_record.
standing: THEOREMS ON RESTRICTED RECORD-LEDGER DATA. The K1 statement supplies finite Record and
 finite index types, hcounted (admissibility, testing and novelty over the other indices), guarded B05
 read over the ledger's own data, and LedgerAvailable. The additive bill is built into RecordLedger;
 defining that representation does not establish it for the original physical source. Defining
 LedgerCounted likewise does not establish that a family meets its obligations. LedgerAvailable is
 a hypothesis, not an installed input. Reading the eight inputs over this restricted representation
 is not installed. These are conditional reference theorems, not Foundation consequences.
what this file says:
 1. ledger_familyCost_eq_needs, ledger_score_eq_shared_needs.
 2. ledger_counted_family_satisfies_K1.
 3. Book: a ledger with one record all distinctions need and one private record each. book_needsFin (its
    needs are what was put in), book_meets_hypotheses (B05, availability and "counted" hold together on
    it). So the K1 statement is not empty.
what this file does NOT say: that the role exchange is anything but the identity; anything about
 orientation, K2 to K6, or the K3 models. No lane. No claim that the transfer is forced, that the carrier
 gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_LedgerScore
import Theorems.Thm_APFPaper1_RecordLedger_bill_eq_sum
import Theorems.Thm_APFPaper1_RecordLedger_maintained_eq_kept
import Theorems.Thm_APFPaper1_RecordLedger_needsFin_subset_of_sufficient
import Theorems.Thm_APFPaper5_K1_interface_sharedCost_families
import Definitions.Def_APFPaper5_K1_interface_bridge_witness_Vocabulary
import Theorems.Thm_APFPaper5_K1_BridgeWitness_exactly_served

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P Record : Type*} [DecidableEq Record]







end

/-! ### A ledger on which the premises hold together -/

namespace Book

open BridgeWitness

variable {ι : Type} [DecidableEq ι]

/-- One record all distinctions need (`none`), one private record each (`some i`), every record costing
1; every finite set of records is a protocol. -/
def book : RecordLedger ι (Finset (Option ι)) (Option ι) where
  cost := w
  kept := fun p => p
  sufficient := fun _ sigma d => (↑(fam d) : Set (Option ι)) ⊆ sigma
  usesToRealize := fun _ _ _ => True







end Book

end APFPaper5.K1


