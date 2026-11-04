-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
-- name    : Submission_ThreeSum_TernaryWantedFactorial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:07.610583+00:00
-- url     : https://prove2.me/theorems/0adf577c-969e-49c0-a169-cd063ea83e09
-- title:
--   Ternary Wanted Factorial
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryWantedFactorial
open TernaryJointType
set_option maxHeartbeats 1000000
def listFactorial (xs : List ℕ) : ℤ := (xs.map fun d => (d.factorial : ℤ)).prod
end ThreeSum.TernaryWantedFactorial


