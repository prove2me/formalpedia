-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfilePreparation
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfilePreparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:27:05.560681+00:00
-- url     : https://prove2.me/theorems/66a63775-8e6f-433d-ac36-98c2a0babe14
-- title:
--   TernaryProfilePreparation
-- statement:
--   Definitions and structural lemmas for TernaryProfilePreparation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryProfilePreparation.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalReceiptTransport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationCall
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


