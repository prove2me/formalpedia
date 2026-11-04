-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorReady
-- name    : Submission_Weighted_Global_TernaryArenaTensorReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:54:06.871321+00:00
-- url     : https://prove2.me/theorems/41cb7af2-24a2-4a1a-adcd-2512d68d3a60
-- title:
--   Ternary Arena Tensor Ready
-- statement:
--   Definitions and structural lemmas for Ternary Arena Tensor Ready, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorReady.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaTensorReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalTensorFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalArenaTensorReady


