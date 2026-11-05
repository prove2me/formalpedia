-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLookupDepth
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLookupDepth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:04:17.809856+00:00
-- url     : https://prove2.me/theorems/c6472941-34f0-4e04-9a5c-96f522163cd7
-- title:
--   TernaryColoredLookupDepth
-- statement:
--   Definitions and structural lemmas for TernaryColoredLookupDepth, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLookupDepth.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPostABI
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedGlobalColoredLookupDepth
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 1000000
end ThreeSum.WeightedGlobalColoredLookupDepth
end WeightedCache3SUMRefinement_e1ae71d


