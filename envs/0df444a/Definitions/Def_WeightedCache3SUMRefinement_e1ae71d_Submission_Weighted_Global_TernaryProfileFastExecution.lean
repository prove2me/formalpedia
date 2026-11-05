-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileFastExecution
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileFastExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:51:53.800355+00:00
-- url     : https://prove2.me/theorems/5cfbf804-3a80-454b-a526-36e9a38ba6ba
-- title:
--   TernaryProfileFastExecution
-- statement:
--   Definitions and structural lemmas for TernaryProfileFastExecution, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryProfileFastExecution.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredExecution
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
end ThreeSum.WeightedGlobalConcreteProfile.Profile
end
end WeightedCache3SUMRefinement_e1ae71d


