-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
-- name    : Submission_ThreeSum_TernaryCoverCapParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:39.083541+00:00
-- url     : https://prove2.me/theorems/efffe867-f79e-4f84-84f0-813bf49b6aa4
-- title:
--   Ternary Cover Cap Parameters
-- statement:
--   Definitions and structural lemmas for Ternary Cover Cap Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
set_option autoImplicit false
namespace ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound
def capBudget (p B k : ℕ) : ℕ :=
  4*(Nat.log2 p+1)+2*(Nat.log2 B+1)+8*k^2+4
def capExponent (p B k : ℕ) : ℕ := capBudget p B k ⌈/⌉ k
def rawThreshold (p B k : ℕ) : ℕ := 2 ^ capExponent p B k
noncomputable def sourceCap (m p : ℕ) : ℕ :=
  (8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card)) ⌈/⌉ p
end ThreeSum.TernaryCoverCapParameters


