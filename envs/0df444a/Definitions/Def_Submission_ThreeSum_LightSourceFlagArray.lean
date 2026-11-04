-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
-- name    : Submission_ThreeSum_LightSourceFlagArray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:45:06.532174+00:00
-- url     : https://prove2.me/theorems/5de786ca-a259-4278-a042-67f347f2bad8
-- title:
--   Light Source Flag Array
-- statement:
--   Definitions and structural lemmas for Light Source Flag Array, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceFlagArray.lean

import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceFlagArray
open Light SourceFlagProduct
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
def flag (J L h p cap : ℕ) (sel candidate : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (mask : ℕ) : ℕ :=
  product (LightSourceTrim.rowFlag L h p cap sel candidate
    (LightMaskBits.bit (J*L) mask) w0 w1 counts) J
def body (pFlag : ℕ) : Stmt :=
  .for 16 (v 11) (
    .call pFlag [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,
      M (v 10 +' v 16),v 12 +' k 2 *' v 11,v 13,v 14,v 15] 17 ;;
    .store (v 12 +' v 16) (M (v 12 +' k 2 *' v 11)) ;;
    .store (v 12 +' v 11 +' v 16) (M (v 12 +' k 2 *' v 11 +' k 1)))
def time (n J L U : ℕ) : ℕ := n*(LightSourceMaskFlags.time J L U+200)+10
structure Procs (P : Program) (pMain : ℕ) where
  pFlag : ℕ
  flagProcs : LightSourceMaskFlags.Procs P pFlag
  main : P[pMain]? = some (body pFlag)
def Inv (μ : ℕ → ℤ) (J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work : ℕ)
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,dst,bitBase,rowOut,work,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (flag J L h p cap sel candidate w0 w1 leftCount (mask j) : ℤ)) ∧
    (∀ j < i, ν (dst+n+j) = (flag J L h p cap sel candidate w1 w0 rightCount (mask j) : ℤ)) ∧
    KeptBut μ ν bitBase dst (2*n+2)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1,LightSourceMaskFlags.body 2 5,LightMaskBits.body 3 4,powTableBody,LightMaskErase.body 4,
    LightSourceTrim.body 6,LightSourceRowFlag.body 7 8 9,LightSourceRowScan.body,
    emodBody,LightSourceFlagTest.body]
def programProcs : Procs program 0 :=
  ⟨1,⟨2,3,4,5,rfl,rfl,rfl,⟨6,7,8,9,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightSourceFlagArray


