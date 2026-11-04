-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
-- name    : Submission_Weighted_Global_LightTernaryDimensionsBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:31:13.647194+00:00
-- url     : https://prove2.me/theorems/6931241b-e135-41ba-a3d3-464824a33098
-- title:
--   Light Ternary Dimensions Budget
-- statement:
--   Definitions and structural lemmas for Light Ternary Dimensions Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
namespace ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
def coefficientBase (M b p K : ℕ) := M+b+p+8*p^(4*K+1)+10
def coefficient (M b p K : ℕ) := 5000*(coefficientBase M b p K)^2
def need (M b p K n U : ℕ) : Need := ⟨word M b p K n U,4,2⟩
end ThreeSum.LightWeightedGlobalDimensions


