-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:26:06.402518+00:00
-- url     : https://prove2.me/theorems/c9947ddc-61f8-4d91-be42-a999f55c4b34
-- title:
--   TernaryUniformQueryTime
-- statement:
--   Definitions and structural lemmas for TernaryUniformQueryTime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryUniformQueryTime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
def maximum (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (R : ℕ) : ℕ :=
  (Finset.range (R+1)).sup fun j => WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=j) I
    (valueCap (r:=j) maps cap I)
def coefficient (m D E κ : ℕ) : ℕ :=100000*(widthCoefficient m D E κ)^3
end ThreeSum.WeightedGlobalUniformQueryTime
end
end WeightedCache3SUMRefinement_e1ae71d


