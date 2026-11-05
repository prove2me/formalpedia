-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaNativeComplete
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaNativeComplete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:22:53.918225+00:00
-- url     : https://prove2.me/theorems/9d1463b2-d1dc-4a1a-befb-a9338ecd3d81
-- title:
--   TernaryArenaNativeComplete
-- statement:
--   Definitions and structural lemmas for TernaryArenaNativeComplete, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaNativeComplete.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


