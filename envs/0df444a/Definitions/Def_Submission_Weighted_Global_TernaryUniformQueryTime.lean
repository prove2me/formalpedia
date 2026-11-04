-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
-- name    : Submission_Weighted_Global_TernaryUniformQueryTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:07:14.73114+00:00
-- url     : https://prove2.me/theorems/89f435b8-3381-4752-be97-f406519761a6
-- title:
--   Ternary Uniform Query Time
-- statement:
--   Definitions and structural lemmas for Ternary Uniform Query Time, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
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


