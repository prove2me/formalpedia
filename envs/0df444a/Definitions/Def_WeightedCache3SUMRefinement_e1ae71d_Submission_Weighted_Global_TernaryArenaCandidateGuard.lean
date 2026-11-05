-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateGuard
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateGuard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:01:10.13913+00:00
-- url     : https://prove2.me/theorems/21224e2f-4b73-45f2-899c-789ad5dddd25
-- title:
--   TernaryArenaCandidateGuard
-- statement:
--   Definitions and structural lemmas for TernaryArenaCandidateGuard, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCandidateGuard.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


