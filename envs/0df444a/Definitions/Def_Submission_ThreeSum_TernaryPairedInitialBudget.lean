-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
-- name    : Submission_ThreeSum_TernaryPairedInitialBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:02:53.265505+00:00
-- url     : https://prove2.me/theorems/208a6195-94aa-4e8f-a2c9-80db121b96df
-- title:
--   Ternary Paired Initial Budget
-- statement:
--   Definitions and structural lemmas for Ternary Paired Initial Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitialBudget.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
set_option autoImplicit false
namespace ThreeSum.TernaryPairedInitialBudget
def upper (K Λ b n carries : ℕ) : ℕ :=
  n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2
end ThreeSum.TernaryPairedInitialBudget


