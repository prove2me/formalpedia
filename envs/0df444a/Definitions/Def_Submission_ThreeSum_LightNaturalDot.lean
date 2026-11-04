-- Prove2me | Definitions.Def_Submission_ThreeSum_LightNaturalDot
-- name    : Submission_ThreeSum_LightNaturalDot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:23:04.021871+00:00
-- url     : https://prove2.me/theorems/543a3b69-386a-4bdf-aed5-0631196ccc8e
-- title:
--   Light Natural Dot
-- statement:
--   Definitions and structural lemmas for Light Natural Dot, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNaturalDot.lean

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators
abbrev dot := LightBooleanDot.dot
abbrev body := LightBooleanDot.body
abbrev loopBody := LightBooleanDot.loopBody
abbrev time := LightBooleanDot.time
variable {lim : Limits} {P : Program} {depth : ℕ}
def reducedBody (pDot pDigit : ℕ) : Stmt :=
  .call pDot [v 0,v 1,v 2] 4 ;; .call pDigit [v 4,k 1,v 3] 0
def reducedTime (n U V : ℕ) : ℕ := time n+40*(n*(U*V)+1)+200
end ThreeSum.LightNaturalDot


