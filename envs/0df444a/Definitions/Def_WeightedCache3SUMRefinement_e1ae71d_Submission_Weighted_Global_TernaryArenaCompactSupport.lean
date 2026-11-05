-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCompactSupport
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCompactSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:57:47.112076+00:00
-- url     : https://prove2.me/theorems/864ef6fd-149e-4f57-a435-7e28c424c6a3
-- title:
--   TernaryArenaCompactSupport
-- statement:
--   Definitions and structural lemmas for TernaryArenaCompactSupport, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCompactSupport.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairRestriction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairModel
import Definitions.Def_Submission_ThreeSum_TernaryTaggedMinorSupport
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCompactSupport
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalNativeTensorScore LightOriginalSurvivors
open TernaryExtensionEncoding TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F r J K : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaCompactSupport
end
end WeightedCache3SUMRefinement_e1ae71d


