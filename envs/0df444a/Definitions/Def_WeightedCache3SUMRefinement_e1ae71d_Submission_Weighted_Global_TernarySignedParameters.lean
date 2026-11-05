-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:15:32.07067+00:00
-- url     : https://prove2.me/theorems/b2e1e29f-f8cf-4d42-8baf-e9e1666ab5c8
-- title:
--   TernarySignedParameters
-- statement:
--   Definitions and structural lemmas for TernarySignedParameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedParameters.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
end ThreeSum.WeightedGlobalSignedParameters
end
end WeightedCache3SUMRefinement_e1ae71d


