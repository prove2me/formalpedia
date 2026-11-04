-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
-- name    : Submission_Weighted_Global_TernaryArenaSourceValues
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:15:20.817201+00:00
-- url     : https://prove2.me/theorems/7477d3a1-c2a6-438f-838a-fcc6823504fe
-- title:
--   Ternary Arena Source Values
-- statement:
--   Definitions and structural lemmas for Ternary Arena Source Values, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceValues.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceValues
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend LightTernarySourceHost
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable
end ThreeSum.WeightedGlobalArenaSourceValues


