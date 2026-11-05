-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:05:12.283667+00:00
-- url     : https://prove2.me/theorems/b8fc46d9-9b7e-4fcf-8798-4c6ec6bbfc4d
-- title:
--   GlobalLocalParameters
-- statement:
--   Definitions and structural lemmas for GlobalLocalParameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalLocalParameters.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
def fixedLength (m : ℕ) : ℕ := 30000000000000000*m
def fixedPi (m : ℕ) : DigitType := ![24361677233089140*m,4759532833568040*m,878789933342820*m]
def fixedAlpha (m : ℕ) : DigitType := ![27034373627654100*m,2672696394564960*m,292929977780940*m]
end ThreeSum.WeightedGlobalLocalParameters
end
end WeightedCache3SUMRefinement_e1ae71d


