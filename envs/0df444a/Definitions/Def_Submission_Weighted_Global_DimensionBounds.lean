-- Prove2me | Definitions.Def_Submission_Weighted_Global_DimensionBounds
-- name    : Submission_Weighted_Global_DimensionBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:45:43.772062+00:00
-- url     : https://prove2.me/theorems/cec4c1b6-2114-4961-b938-aab3330aa4d5
-- title:
--   Dimension Bounds
-- statement:
--   Definitions and structural lemmas for Dimension Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
def bankCut (m j : ℕ) : ℕ := 3130753934820264*j*m
def queryDeficit (m j : ℕ) : ℕ := 206565920180736*j*m+1024
def bankSize (m j : ℕ) : ℕ := (bank (fixedLength (j*m)) (bankCut m j)).card
end ThreeSum.WeightedGlobalDimensionBounds


