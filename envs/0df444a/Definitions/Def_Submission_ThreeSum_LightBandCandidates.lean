-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandCandidates
-- name    : Submission_ThreeSum_LightBandCandidates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:21.154004+00:00
-- url     : https://prove2.me/theorems/876ff4f8-1b37-417f-b2ce-b78a93dcbab0
-- title:
--   Light Band Candidates
-- statement:
--   Definitions and structural lemmas for Light Band Candidates, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidates.lean

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandCandidates
open Light BandEnumeration BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
def body (pBC pAB pAC : ℕ) : Stmt :=
  .set 5 (v 3 *' v 4) ;;
  .set 6 (v 2 *' v 3) ;;
  .set 7 (v 2 *' v 4) ;;
  .set 8 (v 5 +' v 6 +' v 7) ;;
  .call pBC [v 0,v 1,v 3,v 4] 9 ;;
  .call pAB [v 0 +' v 5,v 1 +' k 4 *' v 5,v 2,v 3] 9 ;;
  .call pAC [v 0 +' v 5 +' v 6,v 1 +' k 4 *' (v 5 +' v 6),v 2,v 4] 9 ;;
  .set 0 (v 8)
def time (a b c : ℕ) : ℕ :=
  LightBandCandidatesTable.time b c+LightBandCandidatesTable.time a b+
    LightBandCandidatesTable.time a c+250
def word (a b c : ℕ) : ℕ := a+b+c+10
def space (dst a b c : ℕ) : ℕ := dst+4*LightBandEnumeration.count a b c
structure Procs (P : Program) (pMain : ℕ) where
  pBC : ℕ
  pAB : ℕ
  pAC : ℕ
  pRowBC : ℕ
  pRowAB : ℕ
  pRowAC : ℕ
  pCellBC : ℕ
  pCellAB : ℕ
  pCellAC : ℕ
  bc : P[pBC]?=some (LightBandCandidatesTable.body pRowBC)
  ab : P[pAB]?=some (LightBandCandidatesTable.body pRowAB)
  ac : P[pAC]?=some (LightBandCandidatesTable.body pRowAC)
  rowBC : P[pRowBC]?=some (LightBandCandidatesRow.body pCellBC)
  rowAB : P[pRowAB]?=some (LightBandCandidatesRow.body pCellAB)
  rowAC : P[pRowAC]?=some (LightBandCandidatesRow.body pCellAC)
  cellBC : P[pCellBC]?=some (LightBandCandidatesCell.body .bc)
  cellAB : P[pCellAB]?=some (LightBandCandidatesCell.body .ab)
  cellAC : P[pCellAC]?=some (LightBandCandidatesCell.body .ac)
  main : P[pMain]?=some (body pBC pAB pAC)
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}
def program : Program :=
  [body 1 2 3,LightBandCandidatesTable.body 4,LightBandCandidatesTable.body 5,
    LightBandCandidatesTable.body 6,LightBandCandidatesRow.body 7,
    LightBandCandidatesRow.body 8,LightBandCandidatesRow.body 9,
    LightBandCandidatesCell.body .bc,LightBandCandidatesCell.body .ab,LightBandCandidatesCell.body .ac]
def programProcs : Procs program 0 :=
  ⟨1,2,3,4,5,6,7,8,9,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightBandCandidates


