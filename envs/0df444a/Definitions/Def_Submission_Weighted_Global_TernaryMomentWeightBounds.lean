-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
-- name    : Submission_Weighted_Global_TernaryMomentWeightBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:06:38.013216+00:00
-- url     : https://prove2.me/theorems/7d8d225b-e714-45f8-9f5d-3ef072cf1179
-- title:
--   Ternary Moment Weight Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Moment Weight Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
set_option autoImplicit false
namespace ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory
def leftBound (U K : ℕ) : ℕ :=2^K*(U+1)^K
def rightBound (U K : ℕ) : ℕ :=(U+1)^K
def leftWord (U K : ℕ) : ℕ :=U+2*(2^K+1)*(U+2)^K
def rightWord (U K : ℕ) : ℕ :=U+2*(U+1)^K
end ThreeSum.WeightedGlobalMomentWeightBounds


