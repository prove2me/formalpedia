-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
-- name    : Submission_Weighted_Global_TernaryColoredFinalCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T18:09:52.375187+00:00
-- url     : https://prove2.me/theorems/7f0c1c8e-9fac-4921-aacf-4b2e57ade47e
-- title:
--   Ternary Colored Final Call
-- statement:
--   Definitions and structural lemmas for Ternary Colored Final Call, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinalCall.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection WeightedGlobalArenaPostCertificate
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalColoredFinalCall


