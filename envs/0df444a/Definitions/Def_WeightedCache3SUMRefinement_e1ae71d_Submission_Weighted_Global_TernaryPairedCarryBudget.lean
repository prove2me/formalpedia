-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:23:34.383486+00:00
-- url     : https://prove2.me/theorems/61f3de89-48e1-4634-9ca6-f06e88ab83e5
-- title:
--   TernaryPairedCarryBudget
-- statement:
--   Definitions and structural lemmas for TernaryPairedCarryBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedCarryBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalPairedCarryBudget
open Filter Real WeightedGlobalSignedPreparationBudget WeightedGlobalSignedPadding WeightedGlobalCoverScale
open scoped Topology
end ThreeSum.WeightedGlobalPairedCarryBudget
end
end WeightedCache3SUMRefinement_e1ae71d


