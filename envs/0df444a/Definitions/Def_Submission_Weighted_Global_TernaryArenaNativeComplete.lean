-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
-- name    : Submission_Weighted_Global_TernaryArenaNativeComplete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:36:20.096081+00:00
-- url     : https://prove2.me/theorems/30c1b2fc-e0b9-4682-996f-2a00053305bc
-- title:
--   Ternary Arena Native Complete
-- statement:
--   Definitions and structural lemmas for Ternary Arena Native Complete, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaNativeComplete.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaNativeComplete
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernarySignedReduction
open WeightedGlobalArenaSourceSetup TernaryExtensionEncoding WeightedGlobalNativeRequesterCoverage
variable {p m F r J : ℕ} [Fact p.Prime]
set_option maxHeartbeats 4000000
def input (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) : Input :=
  { I with
    leftInput := fun j => (coefficientCode (sourceLeft H U radix (B j)) : ℤ)
    rightInput := fun k => (coefficientCode (sourceRight H U radix (C k)) : ℤ)
    targets := target H U radix A
    positions := position J
    requesterCount := nA*2^J }
def originalPosition (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) : ℕ→ℕ :=
  fun i => (TernaryWantedBatchIndex.get (entries (r := r) maps τ I) i).1
end ThreeSum.WeightedGlobalArenaNativeComplete


