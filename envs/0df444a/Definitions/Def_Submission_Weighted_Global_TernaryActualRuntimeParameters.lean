-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
-- name    : Submission_Weighted_Global_TernaryActualRuntimeParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:19:42.162139+00:00
-- url     : https://prove2.me/theorems/e76c57ea-be6c-4241-9921-7a1531996b14
-- title:
--   Ternary Actual Runtime Parameters
-- statement:
--   Definitions and structural lemmas for Ternary Actual Runtime Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualRuntimeParameters.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalActualRuntimeParameters
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalOversizePrime
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalSignedPadding
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalActualRuntimeParameters


