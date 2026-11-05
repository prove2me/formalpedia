-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleWantedLookup
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleWantedLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:34:36.579276+00:00
-- url     : https://prove2.me/theorems/e47c371f-f436-4dc9-b2f7-8311a4440260
-- title:
--   TernaryTupleWantedLookup
-- statement:
--   Definitions and structural lemmas for TernaryTupleWantedLookup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleWantedLookup.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalTupleWantedLookup
open TernaryWantedLittleEndian
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalTupleWantedLookup
end
end WeightedCache3SUMRefinement_e1ae71d


