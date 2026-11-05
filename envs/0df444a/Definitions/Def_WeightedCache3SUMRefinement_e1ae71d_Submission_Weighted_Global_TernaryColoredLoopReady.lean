-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopReady
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:13:08.479714+00:00
-- url     : https://prove2.me/theorems/b1b47f79-b0dd-4884-b623-317c3f7f561b
-- title:
--   TernaryColoredLoopReady
-- statement:
--   Definitions and structural lemmas for TernaryColoredLoopReady, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopReady.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoop
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
end ThreeSum.WeightedGlobalColoredLoopSetup
end
end WeightedCache3SUMRefinement_e1ae71d


