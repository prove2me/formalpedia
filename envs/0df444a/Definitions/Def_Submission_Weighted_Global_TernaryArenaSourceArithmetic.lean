-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
-- name    : Submission_Weighted_Global_TernaryArenaSourceArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:03:33.611418+00:00
-- url     : https://prove2.me/theorems/86cf96a7-5632-4d9c-8342-0361782d7346
-- title:
--   Ternary Arena Source Arithmetic
-- statement:
--   Definitions and structural lemmas for Ternary Arena Source Arithmetic, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceArithmetic.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceArithmetic
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaSourceArithmetic


