-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandRawAStep
-- name    : Submission_ThreeSum_LightBandRawAStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:11.379023+00:00
-- url     : https://prove2.me/theorems/a86536f9-5319-4504-80a7-7baff684d4b9
-- title:
--   Light Band Raw AStep
-- statement:
--   Definitions and structural lemmas for Light Band Raw AStep, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAStep.lean

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightBandRawAStep
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
def tail (pRow : ℕ) : Stmt :=
  .call pRow [v 0 +' v 10,v 6 +' v 9,v 7 +' v 9,v 8 +' v 9,v 11,v 5,v 10] 12 ;;
  .set 0 (v 9 +' v 11)
def body (pRow : ℕ) : Stmt :=
  .ite (v 3 =' k 1)
    (.set 10 (v 4 *' v 2) ;;
      .set 11 (v 1 -' v 10) ;;
      .ite (v 2 <' v 11) (.set 11 (v 2)) .skip ;;
      tail pRow)
    (.set 0 (v 9))
def time (g : ℕ) : ℕ := LightBandRawARow.time g+250
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src n g owner values owners positions previous capacity : ℕ} {r : Record}
end ThreeSum.LightBandRawAStep


