-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
-- name    : Submission_Weighted_Global_TernaryArenaFinalSolver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:59:33.026821+00:00
-- url     : https://prove2.me/theorems/26e22f3a-569f-4bd2-a8f7-e8e30fbbbcb0
-- title:
--   Ternary Arena Final Solver
-- statement:
--   Definitions and structural lemmas for Ternary Arena Final Solver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalSolver.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostCertificate
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaFinalSolver
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection WeightedGlobalArenaPostCertificate
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaFinalSolver


