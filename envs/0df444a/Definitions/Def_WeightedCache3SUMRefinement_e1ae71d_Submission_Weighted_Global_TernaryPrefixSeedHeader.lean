-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:05:01.970778+00:00
-- url     : https://prove2.me/theorems/ca55a7eb-fec3-41de-9952-846c88f082fb
-- title:
--   TernaryPrefixSeedHeader
-- statement:
--   Definitions and structural lemmas for TernaryPrefixSeedHeader, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


