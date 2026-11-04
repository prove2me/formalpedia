-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
-- name    : Submission_ThreeSum_TernaryHybridCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:41:26.264121+00:00
-- url     : https://prove2.me/theorems/8875e9cc-08e5-44f2-b985-08f9f5a45e9a
-- title:
--   Ternary Hybrid Costs
-- statement:
--   Definitions and structural lemmas for Ternary Hybrid Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCosts.lean

import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
set_option autoImplicit false
namespace ThreeSum.TernaryHybridCosts
open Light StageBounds Filter
noncomputable section
def fastTime (T : ℕ → ℕ) (κ n : ℕ) : ℕ :=
  T n + LightNatPower.time κ + 1000
end
end ThreeSum.TernaryHybridCosts


