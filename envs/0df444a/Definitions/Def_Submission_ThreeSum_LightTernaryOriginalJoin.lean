-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryOriginalJoin
-- name    : Submission_ThreeSum_LightTernaryOriginalJoin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:08:15.623854+00:00
-- url     : https://prove2.me/theorems/24806399-6fa4-4a92-8f00-de436ab23e35
-- title:
--   Light Ternary Original Join
-- statement:
--   Definitions and structural lemmas for Light Ternary Original Join, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalJoin.lean

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
set_option autoImplicit false
namespace ThreeSum.LightTernaryOriginalJoin
open Light
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
def program : Program := LightWantedSetup.program
def keys (p : ℤ) (base : List ℤ) (J : ℕ) : List ℤ :=
  RadixKeyLists.values p base J
def joinCount (M : ℕ) (input : ℕ → ℤ) (NL : ℕ)
    (p : ℤ) (base : List ℤ) (J : ℕ) (shift : ℤ) : ℕ :=
  WantedResidueKeys.total M input (fun j => (keys p base J).getD j 0)
    NL (keys p base J).length shift
variable {lim : Limits}
end ThreeSum.LightTernaryOriginalJoin


