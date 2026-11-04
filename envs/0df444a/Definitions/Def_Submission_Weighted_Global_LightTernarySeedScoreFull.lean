-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFull
-- name    : Submission_Weighted_Global_LightTernarySeedScoreFull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:18:39.472935+00:00
-- url     : https://prove2.me/theorems/9084faf6-af05-4cb5-a2d5-61772d6f64d9
-- title:
--   Light Ternary Seed Score Full
-- statement:
--   Definitions and structural lemmas for Light Ternary Seed Score Full, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFull.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
set_option autoImplicit false
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


