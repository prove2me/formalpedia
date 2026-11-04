-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
-- name    : Submission_ThreeSum_LightExtensionMenuMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:28:54.581074+00:00
-- url     : https://prove2.me/theorems/c0423b18-ea17-4bfa-9a9d-c957116a6d7d
-- title:
--   Light Extension Menu Matrix
-- statement:
--   Definitions and structural lemmas for Light Extension Menu Matrix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuMatrix.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientMatrix
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionMenuMatrix
open Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 6000
noncomputable local instance _p2m_local_instance_68cd7abcc2_10 (Q : Prop) : Decidable Q := Classical.propDecidable Q
def body (pTable pSeeds pPermute : ℕ) : Stmt :=
  .call pTable [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 11 ;;
  .call pSeeds [v 7,v 0,v 2,v 8,v 10 +' k 2] 11 ;;
  .call pPermute [v 8,v 9,v 0 *' v 0,v 10] 11
def extra : Program :=
  [LightExtensionSeedRow.body 2,LightExtensionSeedMatrix.body 15 2 3,
    LightSignedCoefficientLayout.body,LightSignedCoefficientMatrix.body 17,body 14 16 18]
def program : Program := LightExtensionMultiplyTable.program++extra
def time (C : LightExtensionQuotientPredicate.Layout) (q J : ℕ) : ℕ :=
  LightExtensionMultiplyTable.time q (LightExtensionMultiplyCell.time C q)+
  LightExtensionSeedMatrix.time (J+2) q+LightSignedCoefficientMatrix.time (q*q) J+500
variable {lim : Limits}
end ThreeSum.LightExtensionMenuMatrix


