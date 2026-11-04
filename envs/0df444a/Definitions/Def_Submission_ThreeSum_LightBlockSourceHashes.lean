-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
-- name    : Submission_ThreeSum_LightBlockSourceHashes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:35:05.319764+00:00
-- url     : https://prove2.me/theorems/8c85feb4-720a-4d6b-91f5-2dfa3d5c1a42
-- title:
--   Light Block Source Hashes
-- statement:
--   Definitions and structural lemmas for Light Block Source Hashes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceHashes.lean

import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightBlockSourceHashes
open Light BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def body (pCoefficients pHashes : ℕ) : Stmt :=
  .call pCoefficients [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 11] 12 ;;
  .call pHashes [v 0 *' v 1,v 7,v 8,v 10,v 5,v 6,v 11] 12 ;;
  .call pHashes [v 0 *' v 1,v 7,v 9,v 10,v 6,v 5,v 11] 12
def time (J L n : ℕ) : ℕ :=
  LightBlockCoefficients.time J L + 2*LightMaskHashes.time (J*L) n + 200
def word (J L p U : ℕ) : ℕ :=
  LightBlockCoefficients.word J p U + LightOneHot.word (J*L) (p^J*U)
def space (work J L : ℕ) : ℕ := work + max (J+1) (J*L+1)
structure Procs (P : Program) (pMain : ℕ) where
  pCoefficients : ℕ
  pPowers : ℕ
  pScale : ℕ
  pHashes : ℕ
  pOneHot : ℕ
  coefficients : P[pCoefficients]? = some (LightBlockCoefficients.body pPowers pScale)
  powers : P[pPowers]? = some powTableBody
  scale : P[pScale]? = some LightScaleArray.body
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pOneHot)
  onehot : P[pOneHot]? = some (LightOneHot.body pOneHot)
  main : P[pMain]? = some (body pCoefficients pHashes)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 4,LightBlockCoefficients.body 2 3,powTableBody,LightScaleArray.body,
    LightMaskHashes.body 2 5,LightOneHot.body 5]
def programProcs : Procs program 0 := ⟨1,2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightBlockSourceHashes


