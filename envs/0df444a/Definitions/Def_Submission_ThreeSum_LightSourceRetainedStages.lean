-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
-- name    : Submission_ThreeSum_LightSourceRetainedStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:09.008991+00:00
-- url     : https://prove2.me/theorems/fa4a26f9-acd3-4794-87cf-b143ff266de5
-- title:
--   Light Source Retained Stages
-- statement:
--   Definitions and structural lemmas for Light Source Retained Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRetainedStages.lean

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceRetainedStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
def source {L : ℕ} (m : ℕ) (endpoint : Finset (Fin L) → ℤ)
    (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ) (S : Finset (Fin L)) : ℤ :=
  ((if flag S = 1 then hist (LightResidues.residue m 1 (endpoint S)) else 0 : ℕ) : ℤ)
def body (pGather pZeta : ℕ) : Stmt :=
  .call pGather [v 0,v 1,v 2,v 3,v 9,v 4,v 5] 10 ;;
  .call pZeta [v 6,v 7,v 3,v 8,v 5] 10
def time (L cut E : ℕ) : ℕ :=
  LightSourceGather.time (downsetCap L cut) E+LightZetaStages.time L cut+100
def space (work L E : ℕ) : ℕ :=
  max (work+(Nat.log 2 (E+1)+2)) (work+tableSize L+(L+1))
def word (L m E B : ℕ) : ℕ :=
  4*E+4*m+16+B+(L+1)*2^(L+1)+2^L*B
structure Procs (P : Program) (pMain : ℕ) where
  pGather : ℕ
  pEmod : ℕ
  pZeta : ℕ
  gather : P[pGather]? = some (LightSourceGather.body pEmod)
  emod : P[pEmod]? = some emodBody
  zeta : LightSourceStages.ZetaProcs P pZeta
  main : P[pMain]? = some (body pGather pZeta)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 3,LightSourceGather.body 2,emodBody,LightZetaStages.body 4 5,
    LightDownsetSize.body 9 16,LightZetaPass.body 6 7,
    LightSubsetEnumerationSetup.body 14 18,LightZetaBatch.body 8,
    LightZetaCell.body 9 16 17 15,LightSubsetSetup.body 10 14 15,
    buildBody 11 12,fillBody,rowBody 13,LightArray.linearBody,powTableBody,
    rankBody 15,LightSubsetOffset.body,LightMaskErase.body 17,LightSubsetEnumeration.body 18]
def programProcs : Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨4,5,6,18,7,8,9,10,11,12,13,14,15,16,17,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩
end ThreeSum.LightSourceRetainedStages


