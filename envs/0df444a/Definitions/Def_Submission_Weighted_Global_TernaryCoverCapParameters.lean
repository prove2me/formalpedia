-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
-- name    : Submission_Weighted_Global_TernaryCoverCapParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:54.143538+00:00
-- url     : https://prove2.me/theorems/ffe1387d-4441-42e9-9fda-a53186f1d0f4
-- title:
--   Ternary Cover Cap Parameters
-- statement:
--   Definitions and structural lemmas for Ternary Cover Cap Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
set_option autoImplicit false
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


