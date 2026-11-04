-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryMomentRow
-- name    : Submission_ThreeSum_LightTernaryMomentRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:22.959067+00:00
-- url     : https://prove2.me/theorems/3a6819b0-2476-46d5-8ed1-7d28583fd631
-- title:
--   Light Ternary Moment Row
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentRow.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentGather
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryMomentRow
open Light FiniteMomentZeroDetector
def body (H pGather pDetector : ℕ) : Stmt :=
  .set 7 (M (v 0)) ;;
  .set 8 (M (v 1 +' v 7)) ;;
  .call pGather [v 3,v 4,v 5,v 6,k (2*H+1)] 9 ;;
  .call pDetector [v 6,v 8] 0
def time (H : ℕ) : ℕ := LightTernaryMomentGather.time (2*H+1)+
  LightMomentDeterminant.time (LightMomentZeroDetector.atoms H) H+100
structure Procs (H : ℕ) (P : Program) (pMain : ℕ) where
  pGather : ℕ
  pDetector : ℕ
  gather : P[pGather]?=some LightTernaryMomentGather.body
  detector : P[pDetector]?=some (LightMomentDeterminant.body (LightMomentZeroDetector.atoms H) H)
  main : P[pMain]?=some (body H pGather pDetector)
variable {lim : Limits} {P : Program} {d : ℕ}
def program (H : ℕ) : Program :=
  [body H 1 2,LightTernaryMomentGather.body,
    LightMomentDeterminant.body (LightMomentZeroDetector.atoms H) H]
def procs (H : ℕ) : Procs H (program H) 0 := ⟨1,2,rfl,rfl,rfl⟩
end ThreeSum.LightTernaryMomentRow


