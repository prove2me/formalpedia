-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:31:01.822697+00:00
-- url     : https://prove2.me/theorems/625aab43-d0ff-4f4b-abc8-6fd5cc4fa0da
-- title:
--   LightTernaryDimensionsBudget
-- statement:
--   Definitions and structural lemmas for LightTernaryDimensionsBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
def coefficientBase (M b p K : ℕ) := M+b+p+8*p^(4*K+1)+10
def coefficient (M b p K : ℕ) := 5000*(coefficientBase M b p K)^2
def need (M b p K n U : ℕ) : Need := ⟨word M b p K n U,4,2⟩
end ThreeSum.LightWeightedGlobalDimensions
end WeightedCache3SUMRefinement_e1ae71d


