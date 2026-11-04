-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandPair
-- name    : Submission_ThreeSum_LightSourceBandPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:07:28.098163+00:00
-- url     : https://prove2.me/theorems/a9099561-1913-4e87-b39b-633bb833bf0c
-- title:
--   Light Source Band Pair
-- statement:
--   Definitions and structural lemmas for Light Source Band Pair, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandPair.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceBandPair
open Light BandPartition SourceBandPairData
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
def body (pSetup pFill : ℕ) : Stmt :=
  .set 9 (M (v 1)) ;;
  .set 10 (M (v 3)) ;;
  .set 11 (M (v 7)) ;;
  .set 12 (M (v 1 +' k 1)) ;;
  .set 13 (M (v 3 +' k 1)) ;;
  .set 14 (v 8 +' k 8) ;;
  .call pSetup [v 0,v 9,v 4,v 5,v 6,k 0,v 14] 15 ;;
  .call pSetup [v 2,v 10,v 4,v 5,v 6,v 11,v 15] 16 ;;
  .call pFill [v 16,v 6 +' k 1,k 0] 17 ;;
  .set 18 (v 16 +' v 6 +' k 1) ;;
  .store (v 8) (v 14) ;;
  .store (v 8 +' k 1) (v 12) ;;
  .store (v 8 +' k 2) (v 15) ;;
  .store (v 8 +' k 3) (v 13) ;;
  .store (v 8 +' k 4) (v 16) ;;
  .store (v 8 +' k 5) (v 18) ;;
  .store (v 8 +' k 6) (v 9) ;;
  .store (v 8 +' k 7) (v 10) ;;
  .set 0 (v 18)
def time (NL NR g p m U D : ℕ) : ℕ :=
  LightSourceBandSetup.time NL g p m U D+LightSourceBandSetup.time NR g p m U D+
    fillTime (m+1)+2000
def space (base NL NR g p m U D : ℕ) : ℕ :=
  LightSourceResidues.space (next base NL NR g m) p U D
def word (NL NR g p m U D : ℕ) : ℕ :=
  max (LightSourceBandStep.word NL g p m U D) (LightSourceBandStep.word NR g p m U D)+16
structure Procs (P : Program) (pMain : ℕ) where
  pSetup : ℕ
  pFill : ℕ
  setup : LightSourceBandSetup.Procs P pSetup
  fill : P[pFill]?=some fillBody
  main : P[pMain]?=some (body pSetup pFill)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := LightSourceBandProgram.program ++ [body 12 5]
def setupProcs : LightSourceBandSetup.Procs program 12 :=
  ⟨11,10,rfl,⟨9,⟨0,⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,⟨7,8,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩
def programProcs : Procs program 13 := ⟨12,5,setupProcs,rfl,rfl⟩
end ThreeSum.LightSourceBandPair


