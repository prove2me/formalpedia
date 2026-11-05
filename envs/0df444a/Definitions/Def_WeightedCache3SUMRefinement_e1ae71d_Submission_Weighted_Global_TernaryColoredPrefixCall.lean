-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPrefixCall
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPrefixCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:23:38.000046+00:00
-- url     : https://prove2.me/theorems/be29db9b-635c-47c0-a2b3-cbf239bc7cc7
-- title:
--   TernaryColoredPrefixCall
-- statement:
--   Definitions and structural lemmas for TernaryColoredPrefixCall, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPrefixCall.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalColoredPrefixCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 1500000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalColoredPrefixCall
end
end WeightedCache3SUMRefinement_e1ae71d


