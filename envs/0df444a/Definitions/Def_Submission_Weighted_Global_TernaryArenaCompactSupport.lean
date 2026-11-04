-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
-- name    : Submission_Weighted_Global_TernaryArenaCompactSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:24:55.329645+00:00
-- url     : https://prove2.me/theorems/00f5908a-f456-4de6-b879-551c402c05c2
-- title:
--   Ternary Arena Compact Support
-- statement:
--   Definitions and structural lemmas for Ternary Arena Compact Support, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCompactSupport.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairRestriction
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
import Definitions.Def_Submission_ThreeSum_TernaryTaggedMinorSupport
set_option autoImplicit false
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


