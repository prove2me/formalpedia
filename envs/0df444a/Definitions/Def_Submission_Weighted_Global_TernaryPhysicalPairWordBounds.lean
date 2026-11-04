-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
-- name    : Submission_Weighted_Global_TernaryPhysicalPairWordBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:02:33.939952+00:00
-- url     : https://prove2.me/theorems/0930d577-6316-4517-89bb-4c6dfcfa9014
-- title:
--   Ternary Physical Pair Word Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Physical Pair Word Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators
def weighted {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ) : ℤ :=
  TernaryConvolution.factorial (S.front.Q i)*
    TernaryWeightedPhysicalSources.pairWeight
      (leftSet S i) (rightSet S i) (leftWord S) (rightWord S)
      (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (S.front.Q i)
end ThreeSum.WeightedGlobalPhysicalPairWordBounds


