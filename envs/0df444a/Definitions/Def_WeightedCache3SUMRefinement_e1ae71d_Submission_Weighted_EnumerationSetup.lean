-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EnumerationSetup
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EnumerationSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:08:33.213212+00:00
-- url     : https://prove2.me/theorems/26ae4244-e5ed-4e94-ab13-6e6814585bc3
-- title:
--   EnumerationSetup
-- statement:
--   Definitions and structural lemmas for EnumerationSetup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EnumerationSetup.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedEnumerationSetup
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
variable {lim : Limits} {P : Program}
def body (pPowers pEnum : ℕ) : Stmt :=
  .call pPowers [v 3,k 2 *' v 0 +' k 1,k 2] 4 ;;
  .call pEnum [v 0,v 1,k 0,v 2,v 3] 0
def time (N T : ℕ) : ℕ := powTableTime (2*N+1)+LightCacheEnumeration.time N T+40
def program : Program := [body 1 2,powTableBody,LightCacheEnumeration.body 2]
end ThreeSum.LightWeightedEnumerationSetup
end WeightedCache3SUMRefinement_e1ae71d


