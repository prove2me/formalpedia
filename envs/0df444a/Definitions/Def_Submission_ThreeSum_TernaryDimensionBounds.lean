-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
-- name    : Submission_ThreeSum_TernaryDimensionBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:12:28.741756+00:00
-- url     : https://prove2.me/theorems/f0b9aa11-8e6a-4a41-91c2-cef028185342
-- title:
--   Ternary Dimension Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Dimension Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters
def bankCut (m j : ℕ) : ℕ := 20385197*j*m
def queryDeficit (m j : ℕ) : ℕ := 1344861*j*m+1
def bankSize (m j : ℕ) : ℕ := (bank (fixedLength (j*m)) (bankCut m j)).card
end ThreeSum.TernaryDimensionBounds


