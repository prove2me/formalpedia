-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
-- name    : Submission_ThreeSum_LightTernaryFinalPreparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:46:13.419181+00:00
-- url     : https://prove2.me/theorems/0944a6c4-578f-4c8e-934c-111504b20e46
-- title:
--   Light Ternary Final Preparation
-- statement:
--   Definitions and structural lemmas for Light Ternary Final Preparation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFinalPreparation.lean

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryFinalPreparation
open Light LightSubsetAddress
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000
def body : Stmt :=
  .call 4 [v 5,v 6 +' k 1,k 2] 9 ;;
  .call 0 [v 0,v 1,v 7,v 4] 9 ;;
  .call 0 [v 2,v 3,v 8,v 4] 0
def program : Program := LightOriginalCollisionScore.program ++ [powTableBody,body]
def time (nB nC q W : ℕ) : ℕ :=
  powTableTime (W+1)+LightOriginalCollisionScore.time nB q+LightOriginalCollisionScore.time nC q+200
def Unwritten (powers W histB histC q x : ℕ) : Prop :=
  (x < powers ∨ powers+(W+1) ≤ x) ∧ (x < histB ∨ histB+q ≤ x) ∧ (x < histC ∨ histC+q ≤ x)
variable {lim : Limits}
end ThreeSum.LightTernaryFinalPreparation


