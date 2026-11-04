-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
-- name    : Submission_ThreeSum_TernaryPairedBudgetSelector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:27.727736+00:00
-- url     : https://prove2.me/theorems/dc158d4e-0f47-468b-ae7f-b5bf1610db2c
-- title:
--   Ternary Paired Budget Selector
-- statement:
--   Definitions and structural lemmas for Ternary Paired Budget Selector, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedBudgetSelector.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
namespace ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
end ThreeSum.TernaryPairedBudgetSelector


