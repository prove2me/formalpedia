-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryLiteralOutputCap
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryLiteralOutputCap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:20:32.655885+00:00
-- url     : https://prove2.me/theorems/1a6e45a3-59b5-484c-8d25-e34021b5ab66
-- title:
--   TernaryLiteralOutputCap
-- statement:
--   Definitions and structural lemmas for TernaryLiteralOutputCap, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryLiteralOutputCap.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Mathlib.Tactic
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalLiteralOutputCap
open Finset TernaryJointType TernaryCoverLocal TernaryCoverFibers WeightedGlobalPartitionCount
section Finite
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
  [DecidableEq Q] [DecidableEq K] [AddCommGroup K]
end Finite
section Actual
variable {p : ℕ} [Fact p.Prime]
def actualOutput {t r s : ℕ}
    (e : LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) :
    {q // q ∈ vertices (t+2*r+3*s) (piType t r s)} := by
  classical
  exact ⟨output e,mem_filter.mpr ⟨mem_univ _,(edge_data e).2.2.1⟩⟩
def actualOutputHash {t r s : ℕ}
    (w : TernaryCoverHashes.Coordinate (Fin (t+2*r+3*s)) → ZMod p)
    (q : {q // q ∈ vertices (t+2*r+3*s) (piType t r s)}) : ZMod p := outputHash w q.val
end Actual
end ThreeSum.WeightedGlobalLiteralOutputCap
end
end WeightedCache3SUMRefinement_e1ae71d


