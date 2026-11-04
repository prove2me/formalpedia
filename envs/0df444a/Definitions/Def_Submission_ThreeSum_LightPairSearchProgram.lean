-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
-- name    : Submission_ThreeSum_LightPairSearchProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:01.007963+00:00
-- url     : https://prove2.me/theorems/f294643c-b137-4d53-a371-3a0cc23a2912
-- title:
--   Light Pair Search Program
-- statement:
--   Definitions and structural lemmas for Light Pair Search Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchProgram.lean

import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
set_option autoImplicit false
namespace ThreeSum.LightPairSearch
open Light
variable {lim : Limits}
def program (predicates : Program) (pPred : ℕ) : Program :=
  predicates++[rowBody pPred,body predicates.length]
end ThreeSum.LightPairSearch


