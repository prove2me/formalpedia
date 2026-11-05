-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:26:04.094663+00:00
-- url     : https://prove2.me/theorems/b6b2fb2a-f51d-4fb1-b7c4-9baf01254d99
-- title:
--   TernaryPhysicalPairWordBounds
-- statement:
--   Definitions and structural lemmas for TernaryPhysicalPairWordBounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


