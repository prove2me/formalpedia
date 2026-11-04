-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandRawARow
-- name    : Submission_ThreeSum_LightBandRawARow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:23:33.360444+00:00
-- url     : https://prove2.me/theorems/2b0ae997-1397-4c9e-805c-4eceaef76401
-- title:
--   Light Band Raw ARow
-- statement:
--   Definitions and structural lemmas for Light Band Raw ARow, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawARow.lean

import Definitions.Def_Submission_ThreeSum_BandRawA
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Theorems.Thm_Light_Ends_call
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightBandRawARow
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
def body (pCopy pFill : ℕ) : Stmt :=
  .call pCopy [v 0,v 1,v 4] 7 ;;
  .call pFill [v 2,v 4,v 5] 7 ;;
  pass 8 (v 4) (v 3) (v 6 +' v 8)
def time (n : ℕ) : ℕ := copyTime n+fillTime n+30*n+100
def KeptOthers (μ ν : ℕ → ℤ) (values owners positions n : ℕ) : Prop :=
  SameOn (fun a => Outside values n a ∧ Outside owners n a ∧ Outside positions n a) μ ν
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src values owners positions n owner start : ℕ}
def program : Program := [body 1 2,copyBody,fillBody]
end ThreeSum.LightBandRawARow


