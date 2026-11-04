-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
-- name    : Submission_Weighted_Global_TernaryArenaFixedParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:00:05.342204+00:00
-- url     : https://prove2.me/theorems/f4df2a25-5cc0-4aee-bfbd-33e569523240
-- title:
--   Ternary Arena Fixed Parameters
-- statement:
--   Definitions and structural lemmas for Ternary Arena Fixed Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000
def familyLength (K m : ℕ) : ℕ := (nativeFamily K m (selectedMoment K)).length
def determinantBound (K radix : ℕ) : ℕ := (2*K).factorial*radix^(2*K)
def InputGuards (K m radix κ n : ℕ) : Prop :=
  let r := LightWeightedGlobalDimensions.r (outputSize m) n
  let J := LightWeightedGlobalDimensions.J (outputSize m) radix n (n^κ)
  1<n ∧ r<J ∧ 4*n^κ<radix^J ∧ n^2≤(outputSize m)^r ∧
  (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
  ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
    (determinantBound K radix)^8*n^(8*K+5)
end ThreeSum.WeightedGlobalArenaFixedParameters


