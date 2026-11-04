-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
-- name    : Submission_ThreeSum_LightExtensionMultiplyTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:41.011378+00:00
-- url     : https://prove2.me/theorems/ad4e9a93-689d-40fc-8e93-072b2fcfaedd
-- title:
--   Light Extension Multiply Table
-- statement:
--   Definitions and structural lemmas for Light Extension Multiply Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyTable.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionMultiplyTable
noncomputable local instance _p2m_local_instance_2a3ffe096f_5 (Q : Prop) : Decidable Q := Classical.propDecidable Q
open Light
set_option maxHeartbeats 3000000
def body (pCell pDigit pDivide : ℕ) : Stmt :=
  .set 8 (v 0 *' v 0) ;;
  .for 9 (v 8) (
    .call pDivide [v 9,v 0] 10 ;;
    .call pDigit [v 9,k 1,v 0] 11 ;;
    .call pCell [v 10,v 11,v 1,v 2,v 3,v 4,v 5,v 6,v 0] 12 ;;
    .store (v 7 +' v 9) (v 12))
def time (q T : ℕ) : ℕ := q*q*(T+60*(q*q)+400)+30
def word (q ctx p dim powers a b : ℕ) : ℕ :=
  30*(q*q+q+p+dim+10)
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program := LightExtensionMultiplyCell.program++[body 13 2 3]
end ThreeSum.LightExtensionMultiplyTable


