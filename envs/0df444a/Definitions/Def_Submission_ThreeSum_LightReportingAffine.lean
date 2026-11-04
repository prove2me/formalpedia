-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingAffine
-- name    : Submission_ThreeSum_LightReportingAffine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:13.310293+00:00
-- url     : https://prove2.me/theorems/869ecd88-b7c8-41cd-b518-364e2ef12728
-- title:
--   Light Reporting Affine
-- statement:
--   Definitions and structural lemmas for Light Reporting Affine, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingAffine.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightReportingAffine
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}
def body : Stmt :=
  pass 5 (v 2) (v 1) (v 3 +' v 4 *' M (v 0 +' v 5))
def time (n : ℕ) : ℕ := 23*n+6
def program : Program := [body]
end ThreeSum.LightReportingAffine


