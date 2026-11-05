-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:21:23.659422+00:00
-- url     : https://prove2.me/theorems/425391cf-5784-4643-a3c9-d65282111cf1
-- title:
--   TernaryCoverCapParameters
-- statement:
--   Definitions and structural lemmas for TernaryCoverCapParameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverCapParameters.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound
def capBudget (p B k : ℕ) : ℕ :=
  4*(Nat.log2 p+1)+2*(Nat.log2 B+1)+8*k^2+4
def capExponent (p B k : ℕ) : ℕ := capBudget p B k ⌈/⌉ k
def rawThreshold (p B k : ℕ) : ℕ := 2 ^ capExponent p B k
noncomputable def sourceCap (m p : ℕ) : ℕ :=
  (8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card)) ⌈/⌉ p
end ThreeSum.WeightedGlobalCoverCapParameters
end WeightedCache3SUMRefinement_e1ae71d


