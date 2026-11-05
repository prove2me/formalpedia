-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSetupResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSetupResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:17:58.984205+00:00
-- url     : https://prove2.me/theorems/fbd6f1ab-85f2-487d-8ebc-3f8bcb06daae
-- title:
--   TernaryPrefixSetupResources
-- statement:
--   Definitions and structural lemmas for TernaryPrefixSetupResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSetupResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


