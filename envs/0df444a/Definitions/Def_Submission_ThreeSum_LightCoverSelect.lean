-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCoverSelect
-- name    : Submission_ThreeSum_LightCoverSelect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:59.230491+00:00
-- url     : https://prove2.me/theorems/fb0bd386-ec0c-4e58-9c38-ff37d62de617
-- title:
--   Light Cover Select
-- statement:
--   Definitions and structural lemmas for Light Cover Select, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverSelect.lean

import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightCoverSelect
open Light
def body (pScores pMinimum : ℕ) : Stmt :=
  .call pScores [v 0,v 1,v 2,v 4,v 3] 5 ;;
  .call pMinimum [v 2,v 3] 0
def time (rows cols : ℕ) : ℕ :=
  LightCoverScores.time rows cols+LightMinimum.time rows+60
variable {lim : Limits} {P : Program} {d : ℕ}
structure Procs (P : Program) (pMain : ℕ) where
  pScores : ℕ
  pDot : ℕ
  pMinimum : ℕ
  main : P[pMain]? = some (body pScores pMinimum)
  scores : P[pScores]? = some (LightCoverScores.body pDot)
  dot : P[pDot]? = some LightBooleanDot.body
  minimum : P[pMinimum]? = some LightMinimum.body
def program : Program :=
  [body 1 3,LightCoverScores.body 2,LightBooleanDot.body,LightMinimum.body]
end ThreeSum.LightCoverSelect


