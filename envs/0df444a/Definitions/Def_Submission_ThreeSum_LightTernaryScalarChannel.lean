-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
-- name    : Submission_ThreeSum_LightTernaryScalarChannel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:47.829666+00:00
-- url     : https://prove2.me/theorems/1274df4f-f8f6-4745-86b2-de95c542e25f
-- title:
--   Light Ternary Scalar Channel
-- statement:
--   Definitions and structural lemmas for Light Ternary Scalar Channel, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryScalarChannel.lean

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightTernaryScalarChannel
open Light LightFixedArithmetic TernaryWeightChannels
def atoms : ℕ→Expr := fun _ => M (v 0 +' v 3)
def body (e : Circuit) : Stmt := pass 3 (v 1) (v 2) (e.compile atoms)
def time (e : Circuit) (n : ℕ) : ℕ := n*((e.compile atoms).cost+12)+6
variable {lim : Limits} {P : Program} {d : ℕ}
def program (e : Circuit) : Program := [body e]
end ThreeSum.LightTernaryScalarChannel


