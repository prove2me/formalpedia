-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupAllocation
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:46:40.235235+00:00
-- url     : https://prove2.me/theorems/4aaa74a3-2c8e-4edc-baaf-56cf4f442672
-- title:
--   TernaryArenaCleanupAllocation
-- statement:
--   Definitions and structural lemmas for TernaryArenaCleanupAllocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCleanupAllocation.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalGuardAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCleanupAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalArenaAllocation TernaryExtensionEncoding
set_option maxHeartbeats 8000000
variable {p m F r J : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaCleanupAllocation
end
end WeightedCache3SUMRefinement_e1ae71d


