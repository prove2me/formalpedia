-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:22:12.977191+00:00
-- url     : https://prove2.me/theorems/f1ed0d97-939c-447c-a9e5-cc8848f1a7a3
-- title:
--   TernaryNativePairAccess
-- statement:
--   Definitions and structural lemmas for TernaryNativePairAccess, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairAccess.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalNativePairAccess
end
end WeightedCache3SUMRefinement_e1ae71d


