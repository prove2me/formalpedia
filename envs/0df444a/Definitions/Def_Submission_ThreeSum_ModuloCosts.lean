-- Prove2me | Definitions.Def_Submission_ThreeSum_ModuloCosts
-- name    : Submission_ThreeSum_ModuloCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:44:25.072658+00:00
-- url     : https://prove2.me/theorems/3be7a1a2-6f3b-4dd4-8248-fd955e5e7adb
-- title:
--   Modulo Costs
-- statement:
--   Definitions and structural lemmas for Modulo Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCosts.lean

import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
set_option autoImplicit false
namespace ThreeSum.ModuloCosts
open KaratsubaInterface
def roundedPower (p : ℕ) : ℕ := 3 ^ Nat.clog 2 p
end ThreeSum.ModuloCosts


