-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
-- name    : Submission_Weighted_Global_TernaryPrefixPreparedHeader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:53:32.578797+00:00
-- url     : https://prove2.me/theorems/3a3c7b4f-ef5d-43e2-a477-a10dd5594206
-- title:
--   Ternary Prefix Prepared Header
-- statement:
--   Definitions and structural lemmas for Ternary Prefix Prepared Header, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalPrefixPreparedHeader


