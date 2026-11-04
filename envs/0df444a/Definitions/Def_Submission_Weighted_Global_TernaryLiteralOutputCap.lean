-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
-- name    : Submission_Weighted_Global_TernaryLiteralOutputCap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:27.36914+00:00
-- url     : https://prove2.me/theorems/8e157723-6166-4910-9eed-3782b3738107
-- title:
--   Ternary Literal Output Cap
-- statement:
--   Definitions and structural lemmas for Ternary Literal Output Cap, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryLiteralOutputCap.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Mathlib.Tactic
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
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


