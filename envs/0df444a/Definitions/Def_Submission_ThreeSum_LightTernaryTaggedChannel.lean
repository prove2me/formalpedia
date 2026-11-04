-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryTaggedChannel
-- name    : Submission_ThreeSum_LightTernaryTaggedChannel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:22:28.284217+00:00
-- url     : https://prove2.me/theorems/52051c88-e7db-4efe-8249-4f61818d5334
-- title:
--   Light Ternary Tagged Channel
-- statement:
--   Definitions and structural lemmas for Light Ternary Tagged Channel, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTaggedChannel.lean

import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryProductChannel
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryTaggedChannel
open Light TernarySignedLayout
def offsetBody : Stmt := .ite (v 0 <' v 1)
  (.set 0 (v 1 -' k 1 -' v 0)) (.set 0 (v 0))
variable {lim : Limits} {P : Program} {d : ℕ}
def body (pOffset pProduct : ℕ) : Stmt :=
  .call pOffset [v 3,v 2] 6 ;;
  .call pOffset [v 4,v 2] 7 ;;
  .call pProduct [v 0,v 1,v 2 +' k 2,v 6,v 7,v 5] 0
def time (n : ℕ) : ℕ := LightTernaryProductChannel.time n+120
def program : Program := [body 1 2,offsetBody,LightTernaryProductChannel.body]
end ThreeSum.LightTernaryTaggedChannel


