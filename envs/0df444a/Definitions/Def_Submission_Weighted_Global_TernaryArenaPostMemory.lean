-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
-- name    : Submission_Weighted_Global_TernaryArenaPostMemory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:40:11.230283+00:00
-- url     : https://prove2.me/theorems/bdf25392-0fa9-4f29-aecf-31bc6fb852c1
-- title:
--   Ternary Arena Post Memory
-- statement:
--   Definitions and structural lemmas for Ternary Arena Post Memory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPostMemory
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]
structure Metadata (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (μ : ℕ→ℤ) : Prop where
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
  wanted : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I))
end ThreeSum.WeightedGlobalArenaPostMemory


