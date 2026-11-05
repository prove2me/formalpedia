-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:20:39.219213+00:00
-- url     : https://prove2.me/theorems/3b53f526-fe82-4869-b910-9d9c010e5209
-- title:
--   TernaryCoverFrequency
-- statement:
--   Definitions and structural lemmas for TernaryCoverFrequency, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverFrequency.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
def Covers (B τ : ℕ) (w : Weight m p) (t : ZMod p × ZMod p) : Prop :=
  prunedHit m p B τ w t.1 t.2 ≠ 0
instance (B τ : ℕ) : DecidableRel (Covers m p B τ) := fun _ _ => inferInstanceAs (Decidable (_ ≠ (0 : ℕ)))
def frequencyFactor (m : ℕ) : ℕ :=
  4*3^16*(16*WeightedGlobalPartitionCount.partitionLoss (2379766416784020*m) (292929977780940*m))^2
end ThreeSum.WeightedGlobalCoverFrequency
end
end WeightedCache3SUMRefinement_e1ae71d


