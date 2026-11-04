-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryProfilePreparation
-- name    : Submission_Weighted_Global_TernaryProfilePreparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:21:26.094818+00:00
-- url     : https://prove2.me/theorems/5ead653b-5d92-40d0-be3e-b2650b6821d4
-- title:
--   Ternary Profile Preparation
-- statement:
--   Definitions and structural lemmas for Ternary Profile Preparation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfilePreparation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalReceiptTransport
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationCall
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalProfilePreparation
open Light WeightedGlobalConcreteProfile LightWeightedGlobalFastProgramProof
open WeightedGlobalLocalParameters TernaryCanonicalDictionaries
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def menu (P : Profile κ) (n free : ℕ) : ℕ :=
  LightExtensionBackendLayout.physical (LightWeightedGlobalGlobalPrelude.backend free)
    (LightWeightedGlobalDimensions.dim P.M P.radix P.p P.K n (n^κ))
    (P.p^(LightWeightedGlobalDimensions.dim P.M P.radix P.p P.K n (n^κ)))
    (LightWeightedGlobalDimensions.J P.M P.radix n (n^κ))
end ThreeSum.WeightedGlobalProfilePreparation


