-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:16:04.638974+00:00
-- url     : https://prove2.me/theorems/a3127321-b8dc-4c67-83f9-c28af6f19be8
-- title:
--   TernaryColoredLoopAllocationScalars
-- statement:
--   Definitions and structural lemmas for TernaryColoredLoopAllocationScalars, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


