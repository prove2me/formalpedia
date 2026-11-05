-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFull
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:27:01.251461+00:00
-- url     : https://prove2.me/theorems/fff4a15f-8c3a-45f3-8983-a590bb5fc377
-- title:
--   LightTernarySeedScoreFull
-- statement:
--   Definitions and structural lemmas for LightTernarySeedScoreFull, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernarySeedScoreFull.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalSeedScoreFull
open Light LightWeightedGlobalSeedScoreFactory
structure Outputs (C : Config) (D : Data C) (R S : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (ν : ℕ→ℤ) : Prop where
  B : Reads ν C.Bnew C.nB D.newB
  Cvalues : Reads ν C.Cnew C.nC D.newC
  O : Reads ν C.Onew C.nO D.newO
  wanted : Seg ν C.wanted (D.wantedRows R S raws words maps)
  count : ν (C.header+104)=(D.H R S raws words maps : ℤ)
end ThreeSum.LightWeightedGlobalSeedScoreFull
namespace ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
variable {lim : Limits}
end ThreeSum.LightWeightedGlobalSeedScoreFactory
end
end WeightedCache3SUMRefinement_e1ae71d


