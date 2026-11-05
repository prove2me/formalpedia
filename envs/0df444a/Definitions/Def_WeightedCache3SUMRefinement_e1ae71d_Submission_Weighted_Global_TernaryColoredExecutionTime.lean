-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredExecutionTime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredExecutionTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:01:52.225301+00:00
-- url     : https://prove2.me/theorems/23de05af-f508-458e-85e5-026724fb68f6
-- title:
--   TernaryColoredExecutionTime
-- statement:
--   Definitions and structural lemmas for TernaryColoredExecutionTime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredExecutionTime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalColoredExecutionTime
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup
variable {κ : ℕ}
set_option maxHeartbeats 1000000
end ThreeSum.WeightedGlobalColoredExecutionTime
end
end WeightedCache3SUMRefinement_e1ae71d


