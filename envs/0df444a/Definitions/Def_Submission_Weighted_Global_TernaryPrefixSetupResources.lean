-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources
-- name    : Submission_Weighted_Global_TernaryPrefixSetupResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:23:12.847527+00:00
-- url     : https://prove2.me/theorems/96a0d7cd-9326-4e79-90b0-899fdce1ce7b
-- title:
--   Ternary Prefix Setup Resources
-- statement:
--   Definitions and structural lemmas for Ternary Prefix Setup Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
def need (m j F : ℕ) : Light.Need :=
  ⟨LightWeightedGlobalPrefixSetup.word m j F,4^(N m j)+2*N m j+9,N m j+4⟩
def exponent (m F : ℕ) : ℝ :=
  1+|2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)|+
    |2*Real.log (4^WeightedGlobalLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)|
end ThreeSum.WeightedGlobalPrefixSetupResources


