-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceTrim
-- name    : Submission_ThreeSum_LightSourceTrim
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:55.976945+00:00
-- url     : https://prove2.me/theorems/1a764356-f15b-43aa-b507-fc2e6fb1acfb
-- title:
--   Light Source Trim
-- statement:
--   Definitions and structural lemmas for Light Source Trim, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceTrim.lean

import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceTrim
open Light SourceFlagProduct
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
def rowFlag (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  LightSourceRowFlag.flag L h p cap (fun a => bits (j*L+a))
    (w0 (sel j)) (w1 (sel j)) (counts (candidate (sel j)))
def roundBody (pRowFlag : ℕ) : Stmt :=
  .call pRowFlag [v 10 +' v 16 *' v 1,
    v 6 +' k 2 *' v 1 *' M (v 5 +' v 16),
    v 6 +' k 2 *' v 1 *' M (v 5 +' v 16) +' v 1,
    v 1,v 2,
    v 8 +' M (v 7 +' M (v 5 +' v 16)) *' v 3,
    v 9 +' M (v 7 +' M (v 5 +' v 16)) *' v 3,
    v 3,v 4,v 11,v 12] 17 ;;
  .set 14 (v 14 *' M (v 11)) ;;
  .set 15 (v 15 *' M (v 11 +' k 1))
def body (pRowFlag : ℕ) : Stmt :=
  .set 14 (k 1) ;;
  .set 15 (k 1) ;;
  .for 16 (v 0) (roundBody pRowFlag) ;;
  .store (v 13) (v 14) ;;
  .store (v 13 +' k 1) (v 15)
def time (J L U : ℕ) : ℕ := J*(LightSourceRowFlag.time L U+250)+100
structure Procs (P : Program) (pMain : ℕ) where
  pRowFlag : ℕ
  pRow : ℕ
  pEmod : ℕ
  pFlag : ℕ
  rowFlagDef : P[pRowFlag]? = some (LightSourceRowFlag.body pRow pEmod pFlag)
  row : P[pRow]? = some LightSourceRowScan.body
  emod : P[pEmod]? = some emodBody
  flag : P[pFlag]? = some LightSourceFlagTest.body
  main : P[pMain]? = some (body pRowFlag)
def Inv (μ : ℕ → ℤ) (J L h p cap occ maps candidates histL histR bitBase rowOut work dst : ℕ)
    (sel candidate bits : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,h,p,cap,occ,maps,candidates,histL,histR,bitBase,rowOut,work,dst,
      product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) j,
      product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) j,j,r],ν⟩ ∧
    Kept μ ν rowOut
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1,LightSourceRowFlag.body 2 3 4,LightSourceRowScan.body,emodBody,LightSourceFlagTest.body]
def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightSourceTrim


