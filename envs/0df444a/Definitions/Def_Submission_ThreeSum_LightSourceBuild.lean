-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBuild
-- name    : Submission_ThreeSum_LightSourceBuild
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:48.72171+00:00
-- url     : https://prove2.me/theorems/9da10f73-05d6-483c-9a9e-519cc56e016c
-- title:
--   Light Source Build
-- statement:
--   Definitions and structural lemmas for Light Source Build, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBuild.lean

import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceBuild
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def body (pHistogram pGather : ℕ) : Stmt :=
  .call pHistogram [v 0,v 7,v 1,v 5,v 6,v 9,v 10,v 11] 12 ;;
  .call pGather [v 2,v 3,v 7,v 8,v 4,v 6,v 10] 12
def time (N n p m U D E : ℕ) : ℕ :=
  LightSourceHistogram.time N p m U D + LightSourceGather.time n E + 100
def word (p m U D E : ℕ) : ℕ := LightSourceResidues.word p m U D+4*E+4*m+16
def space (work p U D E : ℕ) : ℕ :=
  max (LightSourceResidues.space work p U D) (work+(Nat.log 2 (E+1)+2))
structure Procs (P : Program) (pMain : ℕ) where
  pHistogram : ℕ
  pGather : ℕ
  histogram : LightSourceHistogram.Procs P pHistogram
  gather : P[pGather]? = some (LightSourceGather.body histogram.pEmod)
  main : P[pMain]? = some (body pHistogram pGather)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 6,LightSourceHistogram.body 2 4,LightSourceResidues.body 3,emodBody,
    LightHistogram.histogramBody 5,fillBody,LightSourceGather.body 3]
def programProcs : Procs program 0 :=
  ⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
end ThreeSum.LightSourceBuild


