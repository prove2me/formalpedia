-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceHistogram
-- name    : Submission_ThreeSum_LightSourceHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:27:45.627018+00:00
-- url     : https://prove2.me/theorems/042f48e3-2cbf-4dd8-852c-e8e69f94c8bf
-- title:
--   Light Source Histogram
-- statement:
--   Definitions and structural lemmas for Light Source Histogram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceHistogram
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
def body (pKeys pHistogram : ℕ) : Stmt :=
  .call pKeys [v 0,v 5,v 2,v 3,v 4,v 6,v 7] 8 ;;
  .call pHistogram [v 5,v 1,v 2,v 4] 8
def time (n p m U D : ℕ) : ℕ :=
  LightSourceResidues.time n p U D + LightHistogram.histogramTime n m + 40
structure Procs (P : Program) (pMain : ℕ) where
  pKeys : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pFill : ℕ
  keys : P[pKeys]? = some (LightSourceResidues.body pEmod)
  emod : P[pEmod]? = some emodBody
  histogram : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pKeys pHistogram)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 3,LightSourceResidues.body 2,emodBody,LightHistogram.histogramBody 4,fillBody]
def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightSourceHistogram


