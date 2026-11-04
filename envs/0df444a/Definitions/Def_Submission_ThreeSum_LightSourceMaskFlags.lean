-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
-- name    : Submission_ThreeSum_LightSourceMaskFlags
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:42:12.12154+00:00
-- url     : https://prove2.me/theorems/08d3943a-4a7e-49be-9587-82f65f9b702c
-- title:
--   Light Source Mask Flags
-- statement:
--   Definitions and structural lemmas for Light Source Mask Flags, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceMaskFlags.lean

import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceMaskFlags
open Light SourceFlagProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
def body (pBits pTrim : ℕ) : Stmt :=
  .call pBits [v 0 *' v 1,v 10,v 12,v 14] 15 ;;
  .call pTrim [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 12,v 13,v 14,v 11] 15
def time (J L U : ℕ) : ℕ := LightMaskBits.time (J*L)+LightSourceTrim.time J L U+100
def word (J L p U V cap : ℕ) : ℕ := 2^(J*L+1)+LightSourceRowFlag.word L p U V cap
def space (work J L U : ℕ) : ℕ :=
  work+max (J*L+1) (3+(Nat.log 2 (L*U+1)+2))
structure Procs (P : Program) (pMain : ℕ) where
  pBits : ℕ
  pPowers : ℕ
  pErase : ℕ
  pTrim : ℕ
  bits : P[pBits]? = some (LightMaskBits.body pPowers pErase)
  powers : P[pPowers]? = some powTableBody
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  trim : LightSourceTrim.Procs P pTrim
  main : P[pMain]? = some (body pBits pTrim)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 4,LightMaskBits.body 2 3,powTableBody,LightMaskErase.body 3,
    LightSourceTrim.body 5,LightSourceRowFlag.body 6 7 8,LightSourceRowScan.body,
    emodBody,LightSourceFlagTest.body]
def programProcs : Procs program 0 :=
  ⟨1,2,3,4,rfl,rfl,rfl,⟨5,6,7,8,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightSourceMaskFlags


