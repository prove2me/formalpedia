-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingPackKeys
-- name    : Submission_ThreeSum_LightReportingPackKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:04:43.934498+00:00
-- url     : https://prove2.me/theorems/31ef76e3-114c-4090-a22f-2197960a8bb3
-- title:
--   Light Reporting Pack Keys
-- statement:
--   Definitions and structural lemmas for Light Reporting Pack Keys, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPackKeys.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightReportingPackKeys
open Light LightArray ReportingHostPackedCatalog
variable {lim : Limits} {P : Program} {d : ℕ}
def body : Stmt :=
  pass 5 (v 2) (v 4)
    (((M (v 0 +' v 5) +' v 3 *' M (v 1 +' v 5)) *' (v 2 +' k 1)) +' v 5)
def time (n : ℕ) : ℕ := 50*n+10
def word (radix n : ℕ) : ℕ := radix^2*(n+1)+n+radix+2
def program : Program := [body]
end ThreeSum.LightReportingPackKeys


