-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTupleWitness
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTupleWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:30:42.487926+00:00
-- url     : https://prove2.me/theorems/c65d41cd-36f0-4098-ae2e-6ee59ec7422f
-- title:
--   TernaryNativeTupleWitness
-- statement:
--   Definitions and structural lemmas for TernaryNativeTupleWitness, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTupleWitness.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


