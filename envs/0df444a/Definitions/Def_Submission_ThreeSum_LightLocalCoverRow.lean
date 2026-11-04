-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
-- name    : Submission_ThreeSum_LightLocalCoverRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:19.369493+00:00
-- url     : https://prove2.me/theorems/a2750f24-7a88-4d3b-b358-4faa4db3d803
-- title:
--   Light Local Cover Row
-- statement:
--   Definitions and structural lemmas for Light Local Cover Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRow.lean

import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverRow
open Light
def body (pPair pSupport : ℕ) : Stmt :=
  .call pPair [v 0,v 1,v 2,v 3,v 4,v 10,v 6,v 7,v 8,v 9] 11 ;;
  .call pSupport [v 10,v 10 +' v 6 *' v 6,v 5,v 6 *' v 6,v 8 *' v 8] 11
def time (L n p : ℕ) : ℕ :=
  LightPairFlags.time L n+LightSupportMark.time (n*n) (p*p)+100
structure Procs (P : Program) (pMain : ℕ) where
  pPair : ℕ
  pDivide : ℕ
  pDot : ℕ
  pTrim : ℕ
  pSupport : ℕ
  pFill : ℕ
  pair : P[pPair]? = some (LightPairFlags.body pDivide pDot pTrim)
  divide : P[pDivide]? = some LightSmallDivide.body
  dot : P[pDot]? = some LightBooleanDot.body
  trim : P[pTrim]? = some LightTrimTest.body
  support : P[pSupport]? = some (LightSupportMark.body pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pPair pSupport)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 5,LightPairFlags.body 2 3 4,LightSmallDivide.body,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 6,fillBody]
def programProcs : Procs program 0 := ⟨1,2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightLocalCoverRow


