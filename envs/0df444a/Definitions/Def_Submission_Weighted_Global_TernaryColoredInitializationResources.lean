-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredInitializationResources
-- name    : Submission_Weighted_Global_TernaryColoredInitializationResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:09:52.290772+00:00
-- url     : https://prove2.me/theorems/ef6d69b5-791a-410c-9a07-b868f4ccdf90
-- title:
--   Ternary Colored Initialization Resources
-- statement:
--   Definitions and structural lemmas for Ternary Colored Initialization Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredInitializationResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_constants
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredInitializationResources
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaLayout
  WeightedGlobalLocalParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000
variable {κ : ℕ}
structure Bounds (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (lim : Limits) (depth : ℕ) : Prop where
  hardware :
    (WeightedGlobalArenaAllocationResources.need P.allocation n (n ^ κ)).Ok lim (input P n free A B C).free (depth + 4)
  finish : WeightedGlobalArenaLayout.finish (input P n free A B C).free (cells P n) ≤ lim.space
  inputWord : ((n + n ^ κ : ℕ) : ℤ) + 1 ≤ lim.word
  exponentWord : (P.allocation.E : ℤ) ≤ lim.word
  menu : q P n * q P n ≤ cells P n
  constants : P.p + 4 ^ fixedLength P.m + P.F ≤ cells P n
  budgetWord :
    (LightTernaryInitialBudgets.word P.K P.radix (P.p ^ (2 * P.K)) P.drift P.scale n (J P n) (A.length * 2 ^ (J P n)) :
        ℤ) ≤
      lim.word
  depthBound : depth + 1 < lim.depth
end ThreeSum.WeightedGlobalColoredInitializationResources


