-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedCoefficientMatrix
-- name    : Submission_ThreeSum_LightSignedCoefficientMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:24.165369+00:00
-- url     : https://prove2.me/theorems/8990df45-271b-4f56-835f-4ac1f8b58716
-- title:
--   Light Signed Coefficient Matrix
-- statement:
--   Definitions and structural lemmas for Light Signed Coefficient Matrix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedCoefficientMatrix.lean

import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientLayout
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSignedCoefficientMatrix
open Light
set_option maxHeartbeats 3000000
def body (pRow : ℕ) : Stmt :=
  .for 4 (v 2) (.call pRow [v 0 +' v 4 *' (v 3 +' k 2),v 1 +' v 4 *' (v 3 +' k 2),v 3] 5)
def time (rows J : ℕ) : ℕ := rows*(LightSignedCoefficientLayout.time J+100)+10
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightSignedCoefficientMatrix


