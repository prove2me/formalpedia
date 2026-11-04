-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
-- name    : Submission_Weighted_Global_TernaryArenaCandidateGuard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:23:57.974949+00:00
-- url     : https://prove2.me/theorems/2a22f26c-c20e-45c1-b904-5c7d83b2c0f9
-- title:
--   Ternary Arena Candidate Guard
-- statement:
--   Definitions and structural lemmas for Ternary Arena Candidate Guard, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateGuard.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCandidateGuard
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
structure Resources {lim : Limits} {depth seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (A : Inputs)
    (D : Data (config p r I A seed)) : Prop where
  requester : I.requesterCount≤I.capacity
  coordinates : A.J+2≤I.capacity
  catalog : A.J*p^(r-1)≤I.capacity
  histogram : p^(r-1)*p≤I.capacity
  wanted : 3*I.requesterCount*(F*WeightedGlobalGoodOutputCatalog.cap m p τ)^r≤I.capacity
  divide : Nat.log 2 (2*WeightedGlobalArenaSeedPrimitiveGuards.rawCap m p r+1)+2≤I.capacity
  word : (WeightedGlobalArenaSeedPrimitiveGuards.word maps τ I A seed positionCap D : ℤ)≤lim.word
  depth : depth+r+6<lim.depth
  seed : seed<I.capacity
def actual (maps : Fin F→Weight m p) (τ cap U : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (seed : ℕ) (D : Data (config p r I A seed))
    (L R : ℕ→ℕ→ℤ) : LightWeightedGlobalControllerFactory.Candidate (config p r I A seed) :=
  candidate maps τ cap U (WeightedGlobalArenaSeedPrimitiveGuards.rawCap m p r)
    (WeightedGlobalNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q I)) Q I A seed D L R
end ThreeSum.WeightedGlobalArenaCandidateGuard


