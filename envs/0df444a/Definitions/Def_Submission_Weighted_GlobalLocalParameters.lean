-- Prove2me | Definitions.Def_Submission_Weighted_GlobalLocalParameters
-- name    : Submission_Weighted_GlobalLocalParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:08:29.045204+00:00
-- url     : https://prove2.me/theorems/f6c95aef-3233-44f2-a58c-dbdc6a4dde4a
-- title:
--   Global Local Parameters
-- statement:
--   Definitions and structural lemmas for Global Local Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
def fixedLength (m : ℕ) : ℕ := 30000000000000*m
def fixedPi (m : ℕ) : DigitType := ![24361752111000*m,4760008248000*m,878239641000*m]
def fixedAlpha (m : ℕ) : DigitType := ![27034502782000*m,2672750671000*m,292746547000*m]
end ThreeSum.WeightedGlobalLocalParameters


