-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
-- name    : Submission_Weighted_Global_TernaryColoredRuntimeCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:20:31.294802+00:00
-- url     : https://prove2.me/theorems/aea5ef06-79bf-42a6-82e6-a9d8a96401fa
-- title:
--   Ternary Colored Runtime Certificate
-- statement:
--   Definitions and structural lemmas for Ternary Colored Runtime Certificate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeCertificate.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_selected

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredRuntimeCertificate
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
def state : WeightedGlobalActualColoredRuntime.State P.K P.m :=
  WeightedGlobalColoredPrefixRuntimeIdentity.runtimeState P n free menu c A B C initial
    (WeightedGlobalColoredFinalReady.selected P n free menu c A B C initial)
    (WeightedGlobalColoredFinalReady.cleanup P n free A B C)
    (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)
end ThreeSum.WeightedGlobalColoredRuntimeCertificate


