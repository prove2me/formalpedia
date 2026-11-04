-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryProfileFastExecution
-- name    : Submission_Weighted_Global_TernaryProfileFastExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:38:53.076203+00:00
-- url     : https://prove2.me/theorems/89350c9e-5346-4a9d-bf6f-20fc9d93702e
-- title:
--   Ternary Profile Fast Execution
-- statement:
--   Definitions and structural lemmas for Ternary Profile Fast Execution, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileFastExecution.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredExecution
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
end ThreeSum.WeightedGlobalConcreteProfile.Profile


