-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:37:23.181377+00:00
-- url     : https://prove2.me/theorems/5c21dbfb-89a0-49ff-86a9-694a2dda3dfb
-- title:
--   TernaryCanonicalTupleCodes
-- statement:
--   Definitions and structural lemmas for TernaryCanonicalTupleCodes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleWantedLookup
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalCanonicalTupleCodes
end
end WeightedCache3SUMRefinement_e1ae71d


