-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:13:15.307234+00:00
-- url     : https://prove2.me/theorems/b82b871c-13e1-44e8-b60f-bf6fe8966429
-- title:
--   NearSourceWords
-- statement:
--   Definitions and structural lemmas for NearSourceWords, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearSourceWords.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSource
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedNearSourceWords
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedNearSourceWords
end
end WeightedCache3SUMRefinement_e1ae71d


