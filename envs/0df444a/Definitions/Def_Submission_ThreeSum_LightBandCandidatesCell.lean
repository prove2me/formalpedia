-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandCandidatesCell
-- name    : Submission_ThreeSum_LightBandCandidatesCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:16:17.610615+00:00
-- url     : https://prove2.me/theorems/891d8e29-1894-4696-a47f-7447754a45f5
-- title:
--   Light Band Candidates Cell
-- statement:
--   Definitions and structural lemmas for Light Band Candidates Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesCell.lean

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightBandCandidatesCell
open Light BandCandidateRows
set_option maxHeartbeats 1400000
set_option maxRecDepth 6000
def tail (mode : Mode) : Stmt :=
  .store (v 3) (v 4) ;;
  .store (v 3 +' k 1) (match mode with | .bc => v 5 | _ => v 1) ;;
  .store (v 3 +' k 2) (match mode with | .bc => v 1 | .ab => v 2 | .ac => v 5) ;;
  .store (v 3 +' k 3) (match mode with | .ab => v 5 | _ => v 2)
def body (mode : Mode) : Stmt :=
  .set 4 (k 0) ;;
  .set 5 (k 0) ;;
  .ite (k 0 <' v 0) (.set 4 (k 1) ;; .set 5 (v 0 -' k 1)) .skip ;;
  tail mode
def time : ℕ := 220
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {r i j dst U : ℕ}
end ThreeSum.LightBandCandidatesCell


