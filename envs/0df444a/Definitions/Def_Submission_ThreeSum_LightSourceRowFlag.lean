-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
-- name    : Submission_ThreeSum_LightSourceRowFlag
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:00.710011+00:00
-- url     : https://prove2.me/theorems/e5ada4f8-74a8-4375-a747-19abd7b3162c
-- title:
--   Light Source Row Flag
-- statement:
--   Definitions and structural lemmas for Light Source Row Flag, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowFlag.lean

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
import Definitions.Def_Submission_ThreeSum_LightResidues
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceRowFlag
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def flag (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) : ℕ :=
  LightSourceFlagTest.flag (LightSourceRowScan.count bits L) h
    (hist (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ))) cap
def body (pRow pEmod pFlag : ℕ) : Stmt :=
  .call pRow [v 0,v 1,v 2,v 3,v 10] 11 ;;
  .call pEmod [M (v 10 +' k 1),v 7,v 10 +' k 3] 12 ;;
  .call pEmod [M (v 10 +' k 2),v 7,v 10 +' k 3] 13 ;;
  .call pFlag [M (v 10),v 4,M (v 5 +' v 12),v 8] 14 ;;
  .call pFlag [M (v 10),v 4,M (v 6 +' v 13),v 8] 15 ;;
  .store (v 9) (v 14) ;;
  .store (v 9 +' k 1) (v 15)
def time (L U : ℕ) : ℕ := LightSourceRowScan.time L+
  2*LightResidues.residueBudget (L*U)+2*LightSourceFlagTest.time+160
def word (L p U V cap : ℕ) : ℕ := LightSourceRowScan.word L U+
  4*(L*U)+4*p+16+2*L+V+cap+2
def space (work L U : ℕ) : ℕ := work+3+(Nat.log 2 (L*U+1)+2)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2 3,LightSourceRowScan.body,emodBody,LightSourceFlagTest.body]
end ThreeSum.LightSourceRowFlag


