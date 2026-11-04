-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
-- name    : Submission_Weighted_Global_TernaryArenaSourceCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:08:41.116728+00:00
-- url     : https://prove2.me/theorems/cb5490ac-1964-49be-97af-d43a20aa6601
-- title:
--   Ternary Arena Source Certificate
-- statement:
--   Definitions and structural lemmas for Ternary Arena Source Certificate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCertificate.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceCertificate
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost TernaryCodeSemantics
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
end ThreeSum.WeightedGlobalArenaSourceCertificate


