-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
-- name    : Submission_ThreeSum_TernaryLocalParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:08:31.810092+00:00
-- url     : https://prove2.me/theorems/b0a2bc79-7a29-4811-9470-d7213adc6b9d
-- title:
--   Ternary Local Parameters
-- statement:
--   Definitions and structural lemmas for Ternary Local Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
def fixedLength (m : ℕ) : ℕ := 100000000*m
def fixedPi (m : ℕ) : DigitType := ![81204746*m,15860450*m,2934804*m]
def fixedAlpha (m : ℕ) : DigitType := ![90113239*m,8908493*m,978268*m]
end ThreeSum.TernaryLocalParameters


