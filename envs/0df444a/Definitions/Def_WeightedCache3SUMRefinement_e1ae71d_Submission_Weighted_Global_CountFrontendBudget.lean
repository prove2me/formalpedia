-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:15:55.425512+00:00
-- url     : https://prove2.me/theorems/2fd1f096-557d-41b1-97b2-d9264aefee41
-- title:
--   CountFrontendBudget
-- statement:
--   Definitions and structural lemmas for CountFrontendBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/CountFrontendBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
def envelope (m j : ℕ) : ℝ :=
  Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy)/z^2739
def width (N : ℕ) (f g : Config) : ℕ :=
  N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3
def queryMax (m j : ℕ) (f g : Config) : ℕ :=
  (TernaryCoverLocal.vertices (fixedLength (j*m)) (fixedPi (j*m))).sup
    (fun Q => LightWeightedPreparedWanted.time f g Q)
def principalExponent (K k c d m : ℕ) : ℝ :=
  max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m)+overheadCharge k c d m
def dimensionConstant (K k c d m : ℕ) : ℝ :=
  1000000*(baseFactor K k c d m : ℝ)*
    (Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)
def prefixTime (m n j : ℕ) (f g : Config) (groups count : ℕ) : ℕ :=
  LightWeightedCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count (queryMax m j f g)+1000
def allPrefixTime (m : ℕ) (f g : ℕ→ℕ→Config) (groups wanted : ℕ→ℕ→ℕ)
    (channels : ℕ→ℕ) (n : ℕ) : ℕ :=
  channels n*∑ j ∈ Finset.range (radixLength m n+1), prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j)
def frontendExponent : ℝ :=24003492602311/12500000000000
end ThreeSum.WeightedGlobalCountFrontendBudget
end
end WeightedCache3SUMRefinement_e1ae71d


