-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:17:49.507026+00:00
-- url     : https://prove2.me/theorems/7a7d3775-afb6-47a3-ab51-4806f7b33d99
-- title:
--   TernaryCompactPairedSupport
-- statement:
--   Definitions and structural lemmas for TernaryCompactPairedSupport, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCompactPairedSupport.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedSelectedChain
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalCompactPairedSupport
open LightOriginalSurvivors LightOriginalCollisionCleanup LightOriginalBucketFilter
open TernaryPairedSupportConcrete TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
end ThreeSum.WeightedGlobalCompactPairedSupport
end
end WeightedCache3SUMRefinement_e1ae71d


