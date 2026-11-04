-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativeTupleWitness
-- name    : Submission_Weighted_Global_TernaryNativeTupleWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:43:20.836562+00:00
-- url     : https://prove2.me/theorems/6903fc3b-22dc-43ac-80ba-71fd34b92f95
-- title:
--   Ternary Native Tuple Witness
-- statement:
--   Definitions and structural lemmas for Ternary Native Tuple Witness, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativeTupleWitness
open Finset TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalCoverGoodMaps
open WeightedGlobalNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open scoped BigOperators
variable {p m : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
theorem output_mem_vertices (e : ActualEdge m) : output e∈vertices (fixedLength m) (fixedPi m) := by
  classical
  exact mem_filter.mpr ⟨mem_univ _,(edge_data e).2.2.1⟩
variable {I : Type*} [Fintype I] [DecidableEq I]
end ThreeSum.WeightedGlobalNativeTupleWitness


