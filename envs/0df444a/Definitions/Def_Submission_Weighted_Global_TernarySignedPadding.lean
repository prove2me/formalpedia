-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
-- name    : Submission_Weighted_Global_TernarySignedPadding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:03:38.992705+00:00
-- url     : https://prove2.me/theorems/d5a5f330-0440-43aa-b5a5-ac337def0653
-- title:
--   Ternary Signed Padding
-- statement:
--   Definitions and structural lemmas for Ternary Signed Padding, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPadding.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
set_option autoImplicit false
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


