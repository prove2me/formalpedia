-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualRuntimeParameters
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualRuntimeParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:34:01.017561+00:00
-- url     : https://prove2.me/theorems/0a9a2549-6aec-45f2-9e44-f1552c7921b0
-- title:
--   TernaryActualRuntimeParameters
-- statement:
--   Definitions and structural lemmas for TernaryActualRuntimeParameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualRuntimeParameters.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualSeedRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalActualRuntimeParameters
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalOversizePrime
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalSignedPadding
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalActualRuntimeParameters
end
end WeightedCache3SUMRefinement_e1ae71d


