-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
-- name    : Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:18:27.645537+00:00
-- url     : https://prove2.me/theorems/73d861f3-8d04-429f-a7cf-1ec47f36aa06
-- title:
--   Ternary Colored Loop Allocation Scalars
-- statement:
--   Definitions and structural lemmas for Ternary Colored Loop Allocation Scalars, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredLoopAllocationScalars
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalColoredLoopAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalLocalParameters WeightedGlobalArenaLayout
set_option maxHeartbeats 200000
set_option maxRecDepth 24000
variable {κ : ℕ}
def values (P : Profile κ) (n : ℕ) : List ℕ :=
  [P.m,P.F,P.p,fixedAlpha P.m 2,WeightedGlobalArenaSourceSetup.alphaRank P.m,
    TernaryCodeSemantics.address P.output.val,4^fixedLength P.m,P.p^(2*P.K),
    9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K,P.scale,J P n,rounds P n]
end ThreeSum.WeightedGlobalColoredLoopAllocationScalars


