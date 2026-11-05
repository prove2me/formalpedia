-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedBudgetCollision
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedBudgetCollision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:33:52.954396+00:00
-- url     : https://prove2.me/theorems/765eb7e5-d7ae-4eb8-888b-458bf6bdf2a1
-- title:
--   TernaryPairedBudgetCollision
-- statement:
--   Definitions and structural lemmas for TernaryPairedBudgetCollision, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedBudgetCollision.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalPairedBudgetCollision
open Real WeightedGlobalPairedCollisionRate WeightedGlobalOversizePrime WeightedGlobalCoverScale WeightedGlobalLocalParameters
end ThreeSum.WeightedGlobalPairedBudgetCollision
end
end WeightedCache3SUMRefinement_e1ae71d


