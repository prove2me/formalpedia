-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
-- name    : Submission_Weighted_Global_TernaryColoredQueryBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:10:28.143585+00:00
-- url     : https://prove2.me/theorems/2f1b5686-d0fb-4309-a513-799e09730a40
-- title:
--   Ternary Colored Query Budget
-- statement:
--   Definitions and structural lemmas for Ternary Colored Query Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredQueryBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredQueryBudget
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def coefficient (P : Profile κ) : ℕ :=
  WeightedGlobalUniformQueryTime.coefficient P.m (256*(P.allocation.D+1)) P.allocation.E κ
end ThreeSum.WeightedGlobalColoredQueryBudget


