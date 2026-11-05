-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredInitializationResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredInitializationResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:15:36.884907+00:00
-- url     : https://prove2.me/theorems/f4320ed2-e833-40c9-852a-f92c26f014da
-- title:
--   TernaryColoredInitializationResources
-- statement:
--   Definitions and structural lemmas for TernaryColoredInitializationResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredInitializationResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaAllocation_Allocation_constants
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


