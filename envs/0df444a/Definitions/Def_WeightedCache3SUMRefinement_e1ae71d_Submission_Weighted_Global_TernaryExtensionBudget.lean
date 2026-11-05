-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:25:45.681898+00:00
-- url     : https://prove2.me/theorems/d1e171be-bc68-4c50-bf4b-2ce6f7910a52
-- title:
--   TernaryExtensionBudget
-- statement:
--   Definitions and structural lemmas for TernaryExtensionBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryExtensionBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalExtensionBudget
open ThreeSum.TernaryExtensionEncoding
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalSignedPreparationBudget
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
end ThreeSum.WeightedGlobalExtensionBudget
end
end WeightedCache3SUMRefinement_e1ae71d


