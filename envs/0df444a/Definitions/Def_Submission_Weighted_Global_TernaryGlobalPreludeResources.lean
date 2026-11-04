-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeResources
-- name    : Submission_Weighted_Global_TernaryGlobalPreludeResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:53:32.567499+00:00
-- url     : https://prove2.me/theorems/d7ad69b2-430b-4af3-a61a-36433274ea69
-- title:
--   Ternary Global Prelude Resources
-- statement:
--   Definitions and structural lemmas for Ternary Global Prelude Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
namespace ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
def need (M b p K κ n _U : ℕ) : Need where
  word:=LightWeightedGlobalDimensions.word M b p K n (n^κ)+1000*(n+1)+n^κ+κ+1
  cells:=33+LightExtensionBackendLayout.reserve
    (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
    (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))
  depth:=17
def exponent (κ : ℕ) : ℕ :=6*(κ+2)
def wordCoefficient (M b p K : ℕ) : ℕ :=2*LightWeightedGlobalDimensions.coefficient M b p K
def baseCoefficient (M b p K : ℕ) : ℕ :=3*wordCoefficient M b p K+p+2
def coefficient (M b p K κ : ℕ) : ℕ :=
  33+100000000*(baseCoefficient M b p K)^6+wordCoefficient M b p K+1000+κ+19
end ThreeSum.WeightedGlobalGlobalPreludeResources


