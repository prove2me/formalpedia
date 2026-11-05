-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:13:01.919013+00:00
-- url     : https://prove2.me/theorems/263b837e-78f9-44f6-8558-3e03d50b9f77
-- title:
--   TernaryArenaFixedParameters
-- statement:
--   Definitions and structural lemmas for TernaryArenaFixedParameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFixedParameters.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


