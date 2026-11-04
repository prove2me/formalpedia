-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
-- name    : Submission_ThreeSum_LightOriginalSurvivorStage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:44:29.981202+00:00
-- url     : https://prove2.me/theorems/5966617c-ed76-4563-ad99-73c6fd49759b
-- title:
--   Light Original Survivor Stage
-- statement:
--   Definitions and structural lemmas for Light Original Survivor Stage, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorStage.lean

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightOriginalSurvivorStage
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
def body : Stmt :=
  .call 1 [v 0,v 1,v 2,v 3,v 4] 17 ;;
  .call 2 [v 4 +' v 1,v 17,v 5,v 1,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 16 ;;
  .set 18 (v 1 -' v 17) ;;
  .call 6 [v 4,v 5,v 13,v 18,v 1] 19 ;;
  .call 6 [v 4,v 0,v 14,v 18,v 1] 19 ;;
  .store (v 15) (v 18) ;;
  .set 0 (v 16)
def program : Program := LightOriginalCollisionCleanup.program ++ [LightReportingGather.body,body]
def time (keys : ℕ → ℕ) (n scanN L : ℕ) : ℕ :=
  LightOriginalCollisionCleanup.time keys n scanN L +
    2*LightReportingGather.time (indices keys n).length + 300
def Above (μ ν : ℕ → ℤ) (boundary : ℕ) : Prop := ∀ x, boundary < x → ν x = μ x
def Unwritten (out n dstValues dstKeys count lengthCell x : ℕ) : Prop :=
  (x < out ∨ out+2*n ≤ x) ∧ (x < dstValues ∨ dstValues+count ≤ x) ∧
    (x < dstKeys ∨ dstKeys+count ≤ x) ∧ x ≠ lengthCell
def Preserves (μ ν : ℕ → ℤ) (out n dstValues dstKeys count lengthCell : ℕ) : Prop :=
  ∀ x, Unwritten out n dstValues dstKeys count lengthCell x → ν x = μ x
variable {lim : Limits}
end ThreeSum.LightOriginalSurvivorStage


