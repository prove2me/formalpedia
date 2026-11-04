-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
-- name    : Submission_Weighted_Global_TernaryArenaSourceModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:01:46.239536+00:00
-- url     : https://prove2.me/theorems/49cb30bb-ee51-4614-b630-34f27d395ad6
-- title:
--   Ternary Arena Source Model
-- statement:
--   Definitions and structural lemmas for Ternary Arena Source Model, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
abbrev Index (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :=
  Fin ((localRecords maps cap right).length^r)
end ThreeSum.WeightedGlobalArenaSourceModel


