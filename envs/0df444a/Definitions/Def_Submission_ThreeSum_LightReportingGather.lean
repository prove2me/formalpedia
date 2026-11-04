-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingGather
-- name    : Submission_ThreeSum_LightReportingGather
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:49.494639+00:00
-- url     : https://prove2.me/theorems/aca2c03e-a202-4ea0-a14a-b77af5e4efcc
-- title:
--   Light Reporting Gather
-- statement:
--   Definitions and structural lemmas for Light Reporting Gather, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGather.lean

import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightReportingGather
open Light
variable {lim : Limits} {P : Program}
def body : Stmt := pass 5 (v 3) (v 2) (M (v 1 +' M (v 0 +' v 5)))
def program : Program := [body]
def time (t : ℕ) : ℕ := 40*t+10
end ThreeSum.LightReportingGather


