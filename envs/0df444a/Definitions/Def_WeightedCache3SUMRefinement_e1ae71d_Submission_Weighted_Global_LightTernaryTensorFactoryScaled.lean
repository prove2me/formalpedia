-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:57:31.377824+00:00
-- url     : https://prove2.me/theorems/147102c5-857a-4ac8-8703-7cdb11a4c02c
-- title:
--   LightTernaryTensorFactoryScaled
-- statement:
--   Definitions and structural lemmas for LightTernaryTensorFactoryScaled, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorFactoryScaled.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType TernaryPairedTensor
open scoped BigOperators
end ThreeSum.LightWeightedGlobalTensorFactory
end
end WeightedCache3SUMRefinement_e1ae71d


