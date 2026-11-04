-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetupBudget
-- name    : Submission_Weighted_Global_LightExtensionBackendSetupBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:32:39.413333+00:00
-- url     : https://prove2.me/theorems/eb60ba9e-5bbe-4ed5-8d39-20a03a7dae58
-- title:
--   Light Extension Backend Setup Budget
-- statement:
--   Definitions and structural lemmas for Light Extension Backend Setup Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalExtensionBackendSetup
open LightExtensionBackendLayout TernaryExtensionEncoding WeightedGlobalSignedPadding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime]
end ThreeSum.LightWeightedGlobalExtensionBackendSetup


