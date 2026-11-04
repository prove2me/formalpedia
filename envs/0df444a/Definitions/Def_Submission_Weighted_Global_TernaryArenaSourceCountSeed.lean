-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
-- name    : Submission_Weighted_Global_TernaryArenaSourceCountSeed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:41:59.587562+00:00
-- url     : https://prove2.me/theorems/e03f7d4d-8099-4440-95a2-6f6170826b48
-- title:
--   Ternary Arena Source Count Seed
-- statement:
--   Definitions and structural lemmas for Ternary Arena Source Count Seed, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCountSeed.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSeed
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceCountSeed
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
structure Reads (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (μ : ℕ→ℤ) : Prop where
  left : ∀i<I.nB, μ (addr I.free I.capacity 16+i)=I.leftInput i
  right : ∀i<I.nC, μ (addr I.free I.capacity 17+i)=I.rightInput i
  leftBound : ∀i<I.nB, |I.leftInput i|≤(p*(p+1)^r : ℕ)
  rightBound : ∀i<I.nC, |I.rightInput i|≤(p*(p+1)^r : ℕ)
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
  wanted : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I))
end ThreeSum.WeightedGlobalArenaSourceCountSeed


