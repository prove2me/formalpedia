-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
-- name    : Submission_ThreeSum_LightTernaryCommitSpan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:50.075776+00:00
-- url     : https://prove2.me/theorems/f3e0b3b6-1404-45c6-b3fc-031d021a53a1
-- title:
--   Light Ternary Commit Span
-- statement:
--   Definitions and structural lemmas for Light Ternary Commit Span, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitSpan.lean

import Definitions.Def_Submission_ThreeSum_LightArray
set_option autoImplicit false
namespace ThreeSum.LightTernaryCommitSpan
open Light
def program : Program :=[copyBody]
def time (J rows : ℕ) : ℕ :=copyTime (rows*J)
end ThreeSum.LightTernaryCommitSpan


