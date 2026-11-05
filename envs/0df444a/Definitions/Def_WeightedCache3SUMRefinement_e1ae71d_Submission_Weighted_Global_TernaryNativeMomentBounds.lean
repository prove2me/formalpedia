-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:16:59.235976+00:00
-- url     : https://prove2.me/theorems/08c1df5c-ef3d-46c5-b085-8958e201c7f0
-- title:
--   TernaryNativeMomentBounds
-- statement:
--   Definitions and structural lemmas for TernaryNativeMomentBounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


