-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:12:01.458196+00:00
-- url     : https://prove2.me/theorems/e056baf8-5fbe-43eb-97b1-4ccad54d3ce6
-- title:
--   TernarySignedPadding
-- statement:
--   Definitions and structural lemmas for TernarySignedPadding, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedPadding.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalSignedPadding
open Filter Real TernarySignedReduction WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalOversizeOverhead WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
def digitLength (b U : ℕ) : ℕ := Nat.clog b (4*U+1)
def paddedLength (b U r : ℕ) : ℕ := digitLength b U+r+1
def carryExponent (m b : ℕ) (κ : ℝ) : ℝ :=
  κ*Real.log 2/Real.log (b : ℝ)+2*Real.log 2/Real.log (outputSize m : ℝ)
def carryConstant (b : ℕ) : ℝ :=
  Real.exp (3*Real.log 2+Real.log 5*Real.log 2/Real.log (b : ℝ))
end ThreeSum.WeightedGlobalSignedPadding
end
end WeightedCache3SUMRefinement_e1ae71d


