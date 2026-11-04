-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
-- name    : Submission_Weighted_Global_TernaryNativeMomentBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:58:24.373803+00:00
-- url     : https://prove2.me/theorems/37ece360-9258-45c4-90dd-95dd2bd93bf1
-- title:
--   Ternary Native Moment Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Native Moment Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators
def pairBound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) : ℕ :=
  (S.left.NL*LightTernarySourceHost.size S.left.xs S.left.J)*
  (S.right.NL*LightTernarySourceHost.size S.right.xs S.right.J)
def momentBound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (U K : ℕ) : ℕ :=
  pairBound S*2^N*(2*U+1)^K
def scoreBound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) : ℕ :=
  pairBound S*2^N*S.left.weightU*S.right.weightU
def detectorInput {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (U H : ℕ) : ℕ :=
  U+momentBound S U (2*H)
def detectorWord (x H : ℕ) : ℕ :=
  ((LightMomentDeterminant.wordCoefficient H).toNat+1)*
    (x+1)^(LightMomentDeterminant.wordDegree H+1)
end ThreeSum.WeightedGlobalNativeMomentBounds


