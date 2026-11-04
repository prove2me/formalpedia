-- Prove2me | Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
-- name    : Submission_ThreeSum_LightFixedRadixDictionary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:41.723867+00:00
-- url     : https://prove2.me/theorems/df51d6fb-eb47-48e5-a57c-8d5c0ab1d4b7
-- title:
--   Light Fixed Radix Dictionary
-- statement:
--   Definitions and structural lemmas for Light Fixed Radix Dictionary, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedRadixDictionary.lean

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightFixedRadixDictionary
open Light RadixKeyLists
variable {lim : Limits}
set_option maxHeartbeats 1400000
def body (pTable pKeys : ℕ) : Stmt :=
  .call pTable [v 0] 4 ;;
  .call pKeys [v 0,v 4,v 2,v 3,v 1] 5 ;;
  .set 0 (v 5)
def program (xs : List ℤ) : Program :=
  [LightSignedFiniteTable.body xs,LightRadixKeys.body 1 2,
    LightRadixRows.body 3,LightReportingAffine.body,body 0 1]
def time (xs : List ℤ) (J : ℕ) : ℕ := 7*xs.length+2+LightRadixKeys.time xs.length J+50
end ThreeSum.LightFixedRadixDictionary


