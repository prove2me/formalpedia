-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryProduct
-- name    : Submission_ThreeSum_LightTernaryProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:13.863966+00:00
-- url     : https://prove2.me/theorems/e8cb3f13-cc29-42c9-93be-3460518824ff
-- title:
--   Light Ternary Product
-- statement:
--   Definitions and structural lemmas for Light Ternary Product, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryProduct.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightTernaryProduct
open Light ThreeSum.LightArray
def body : Stmt :=
  pass 4 (v 3) (v 2) (M (v 0 +' v 4) *' M (v 1 +' v 4))
def time (n : ℕ) : ℕ := 24*n+10
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightTernaryProduct


