-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
-- name    : Submission_Weighted_Global_TernaryPrefixSeedHeader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:03:13.73152+00:00
-- url     : https://prove2.me/theorems/c568c33f-dcd6-45eb-be14-9aa4e3c6462f
-- title:
--   Ternary Prefix Seed Header
-- statement:
--   Definitions and structural lemmas for Ternary Prefix Seed Header, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
def result (xs : List ℤ) (X : Inputs) : List ℤ :=
  ((((((((((xs.set 4 X.power).set 6 X.power).set 24 X.liveHeader).set 39 (X.j+1)).set 41 (X.xB*X.p)).set 42 (X.xC*X.p)).set 43 (X.xP*X.a)).set 44 (X.tB*9)).set 45 (X.tC*9)).set 46 (X.tP*X.b*X.scale))
def nextConfig (C : Config) (X : Inputs) : Config :=
  {C with catalogRows:=X.power,power:=X.power,header:=X.liveHeader,prefixLength:=X.j+1}
instance (C : Config) [Fact C.p.Prime] (X : Inputs) : Fact (nextConfig C X).p.Prime :=
  inferInstanceAs (Fact C.p.Prime)
end ThreeSum.WeightedGlobalPrefixSeedHeader


