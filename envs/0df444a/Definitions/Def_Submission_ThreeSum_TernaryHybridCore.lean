-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryHybridCore
-- name    : Submission_ThreeSum_TernaryHybridCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:00:48.422417+00:00
-- url     : https://prove2.me/theorems/fba123ea-a219-4cce-bdca-38da7f2fd17f
-- title:
--   Ternary Hybrid Core
-- statement:
--   Definitions and structural lemmas for Ternary Hybrid Core, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
def body (fastSize fastProc κ cutoff : ℕ) : Stmt :=
  .ite (v 0 <' k cutoff)
    (.call (fastSize+3) [v 0,v 1,v 2,v 3] 0)
    (.call (fastSize+4) [v 0,k κ] 4 ;;
      .ite (v 4 <' v 1)
        (.call (fastSize+3) [v 0,v 1,v 2,v 3] 0)
        (.call fastProc [v 2,v 0,v 3] 0))
def libraries (fastP : Program) : Program :=
  ReportingHostRelocation.program fastP LightBruteThreeSum.program
def program (fastP : Program) (fastProc κ cutoff : ℕ) : Program :=
  libraries fastP++[LightNatPower.body,body fastP.length fastProc κ cutoff]
def time (fastTime : ℕ → ℕ) (κ cutoff n U : ℕ) : ℕ :=
  if n<cutoff ∨ n^κ<U then
    LightBruteThreeSum.time n+LightNatPower.time κ+1000
  else fastTime n+LightNatPower.time κ+1000
variable (fastNeed : ℕ → ℕ → Need) (fastTime : ℕ → ℕ)
end ThreeSum.TernaryHybridCore


