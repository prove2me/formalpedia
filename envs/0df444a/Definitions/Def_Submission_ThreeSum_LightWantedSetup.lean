-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWantedSetup
-- name    : Submission_ThreeSum_LightWantedSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:03:55.56958+00:00
-- url     : https://prove2.me/theorems/1c52a707-7165-42ac-9dfc-7a84ebd035b6
-- title:
--   Light Wanted Setup
-- statement:
--   Definitions and structural lemmas for Light Wanted Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedSetup.lean

import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightWantedSetup
open Light WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def leftCodes (free : ℕ) : ℕ := free+4
def rightCodes (free NL : ℕ) : ℕ := leftCodes free+NL
def bucketBase (free NL NR : ℕ) : ℕ := rightCodes free NL+NR
def pairBase (free NL NR M : ℕ) : ℕ :=
  LightSourceBucketSetup.next (bucketBase free NL NR) NR M
def body (pResidues pBuckets pJoin : ℕ) : Stmt :=
  .set 7 (v 6 +' k 4) ;;
  .set 8 (v 7 +' v 2) ;;
  .set 9 (v 8 +' v 3) ;;
  .set 10 (v 9 +' v 4) ;;
  .set 11 (v 9 +' k 3 *' v 4 +' k 1) ;;
  .set 12 (v 11 +' v 3) ;;
  .call pResidues [v 0,v 7,v 2,v 4,v 4,v 12,v 5] 13 ;;
  .call pResidues [v 1,v 8,v 3,v 4,v 4,v 12,k 0] 13 ;;
  .call pBuckets [v 8,v 3,v 4,v 9] 13 ;;
  .call pJoin [v 7,v 10,v 11,v 2,v 3,v 4,v 12] 14 ;;
  .store (v 6) (v 14) ;;
  .store (v 6 +' k 1) (v 12) ;;
  .store (v 6 +' k 2) (v 12 +' k 2 *' v 14) ;;
  .store (v 6 +' k 3) (v 5) ;;
  .set 0 (v 6)
def bucketProgram : Program := ReportingHostRelocation.program
  LightSourceResidues.program LightSourceBucketSetup.program
def joinedProgram : Program := ReportingHostRelocation.program
  bucketProgram LightWantedJoin.program
def program : Program := joinedProgram ++ [body 0 2 9]
def time (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) : ℕ :=
  LightSourceResidues.time NL M U D+LightSourceResidues.time NR M U D+
    LightSourceBucketSetup.time NR M+
    LightWantedJoin.time (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL+500
def space (free M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) : ℕ :=
  max (LightSourceResidues.space (pairBase free NL NR M) M U D)
    (pairBase free NL NR M+2*total M left right NL NR shift)
def Output (ν : ℕ → ℤ) (free M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : Prop :=
  ν free=(total M left right NL NR shift : ℤ) ∧
  ν (free+1)=(pairBase free NL NR M : ℤ) ∧
  ν (free+2)=((pairBase free NL NR M+2*total M left right NL NR shift : ℕ) : ℤ) ∧
  ν (free+3)=shift ∧
  ∃ ps : List (ℕ × ℕ), ps.length=total M left right NL NR shift ∧ ps.Nodup ∧
    (∀ i j, (i,j) ∈ ps ↔ i < NL ∧ j < NR ∧ (M : ℤ) ∣ left i+shift-right j) ∧
    Seg ν (pairBase free NL NR M) (WantedPairs.cells ps)
variable {lim : Limits}
end ThreeSum.LightWantedSetup


