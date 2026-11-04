-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedCoefficientLayout
-- name    : Submission_ThreeSum_LightSignedCoefficientLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:22:35.897028+00:00
-- url     : https://prove2.me/theorems/a68e4a74-f9be-43cd-bc5e-8d19318225ec
-- title:
--   Light Signed Coefficient Layout
-- statement:
--   Definitions and structural lemmas for Light Signed Coefficient Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedCoefficientLayout.lean

import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSignedCoefficientLayout
open Light TernarySignedLayout
set_option maxHeartbeats 2000000
def roundBody : Stmt :=
  .ite (v 3 <' v 2)
    (.store (v 1 +' v 2 -' k 1 -' v 3) (M (v 0 +' v 3)))
    (.store (v 1 +' v 3) (M (v 0 +' v 3)))
def body : Stmt := .for 3 (v 2 +' k 2) roundBody
def time (J : ℕ) : ℕ := 50*(J+2)+10
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightSignedCoefficientLayout


