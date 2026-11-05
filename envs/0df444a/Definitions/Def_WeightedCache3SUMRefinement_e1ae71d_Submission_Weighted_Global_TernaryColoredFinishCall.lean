-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredFinishCall
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredFinishCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:40:23.026028+00:00
-- url     : https://prove2.me/theorems/216b8377-4a8a-4320-8c22-1d20baa9087b
-- title:
--   TernaryColoredFinishCall
-- statement:
--   Definitions and structural lemmas for TernaryColoredFinishCall, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredFinishCall.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLookupDepth
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalColoredFinishCall
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaLayout
open WeightedGlobalLocalParameters WeightedGlobalArenaSourceSetup WeightedGlobalColoredTerminalReceipt
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
end ThreeSum.WeightedGlobalColoredFinishCall
end
end WeightedCache3SUMRefinement_e1ae71d


