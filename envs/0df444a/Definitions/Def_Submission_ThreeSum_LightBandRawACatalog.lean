-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
-- name    : Submission_ThreeSum_LightBandRawACatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:32:59.662745+00:00
-- url     : https://prove2.me/theorems/340d0cfa-817f-4bc2-bbf1-5f4d0d743b6d
-- title:
--   Light Band Raw ACatalog
-- statement:
--   Definitions and structural lemmas for Light Band Raw ACatalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawACatalog.lean

import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandRawACatalog
open Light BandEnumeration BandCandidateRows BandRawA
set_option maxHeartbeats 2100000
set_option maxRecDepth 8000
def body (pCandidates pRaw : ℕ) : Stmt :=
  .set 8 (M (v 3)) ;;
  .set 9 (M (v 3 +' k 1)) ;;
  .set 10 (M (v 4 +' k 1)) ;;
  .set 11 (M (v 5 +' k 1)) ;;
  .call pCandidates [v 0,v 1,v 9,v 10,v 11] 12 ;;
  .call pRaw [v 1,v 12,v 2,v 8,v 6,v 7] 0
def time (a b c g : ℕ) : ℕ :=
  LightBandCandidates.time a b c+LightBandRawA.time (LightBandEnumeration.count a b c) g+300
def word (n a b c g : ℕ) : ℕ :=
  LightBandCandidates.word a b c+LightBandRawA.word n g (LightBandEnumeration.count a b c)+20
def space (vals a b c g : ℕ) : ℕ :=
  LightBandRawA.space vals (LightBandEnumeration.count a b c) g
structure Procs (P : Program) (pMain : ℕ) where
  pCandidates : ℕ
  pRaw : ℕ
  candidates : LightBandCandidates.Procs P pCandidates
  raw : LightBandRawA.Procs P pRaw
  main : P[pMain]?=some (body pCandidates pRaw)
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}
def program : Program :=
  [body 1 11,
    LightBandCandidates.body 2 5 8,
    LightBandCandidatesTable.body 3,LightBandCandidatesRow.body 4,LightBandCandidatesCell.body .bc,
    LightBandCandidatesTable.body 6,LightBandCandidatesRow.body 7,LightBandCandidatesCell.body .ab,
    LightBandCandidatesTable.body 9,LightBandCandidatesRow.body 10,LightBandCandidatesCell.body .ac,
    LightBandRawA.body 12,LightBandRawAStep.body 13,LightBandRawARow.body 14 15,copyBody,fillBody]
def programProcs : Procs program 0 where
  pCandidates := 1
  pRaw := 11
  candidates := ⟨2,5,8,3,6,9,4,7,10,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  raw := ⟨12,13,14,15,rfl,rfl,rfl,rfl,rfl⟩
  main := rfl
end ThreeSum.LightBandRawACatalog


