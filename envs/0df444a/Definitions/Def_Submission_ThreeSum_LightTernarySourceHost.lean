-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
-- name    : Submission_ThreeSum_LightTernarySourceHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:13:34.674195+00:00
-- url     : https://prove2.me/theorems/9fb5ec1f-6c2e-46fd-978f-2670e68eb405
-- title:
--   Light Ternary Source Host
-- statement:
--   Definitions and structural lemmas for Light Ternary Source Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHost.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalJoin
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
import Definitions.Def_Submission_ThreeSum_TernarySourceHostRecords
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernarySourceHost
open Light RadixKeyLists ThreeSum.LightSubsetAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
variable {lim : Limits}
def joined (xs ys zs : List ℤ) : Program := ReportingHostRelocation.program
  (LightTernaryParallelDictionaries.program xs ys zs) LightTernaryOriginalJoin.program
def libraries (xs ys zs : List ℤ) : Program :=
  ReportingHostRelocation.program (joined xs ys zs) LightTernaryGroupedSources.program
def body : Stmt :=
  .call 15 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9] 23 ;;
  .set 24 (M (v 23)) ;;
  .set 25 (v 23 -' v 5) ;;
  .set 26 (v 1 +' v 25 +' k 1) ;;
  .set 27 (v 3 +' v 25 +' k 1) ;;
  .set 28 (v 5 +' v 25 +' k 1) ;;
  .call 27 [v 10,v 26,v 11,v 24,v 12,k 0,v 13] 29 ;;
  .set 30 (M (v 29)) ;;
  .set 31 (M (v 29 +' k 1)) ;;
  .call 28 [v 14,v 15,v 16,v 17,v 31,v 30,v 27,v 24,
    v 18,v 19,v 20,v 11,v 21,v 28,v 22] 32 ;;
  .set 0 (v 19)
def program (xs ys zs : List ℤ) : Program := libraries xs ys zs++[body]
def size (xs : List ℤ) (J : ℕ) : ℕ := xs.length^J
def dictionary (xs : List ℤ) (p J : ℕ) (i : ℕ) : ℤ := (values (p : ℤ) xs J).getD i 0
def count (xs : List ℤ) (p J M NL : ℕ) (input : ℕ → ℤ) : ℕ :=
  WantedResidueKeys.total M input (dictionary xs p J) NL (size xs J) 0
def time (xs ys zs : List ℤ) (p J M NL U L bank groups : ℕ) (input : ℕ → ℤ) : ℕ :=
  LightTernaryParallelDictionaries.time xs ys zs J+
    LightWantedSetup.time M input (dictionary xs p J) NL (size xs J) U 0 0+
    LightTernaryGroupedSources.time L (count xs p J M NL input) bank groups+500
end ThreeSum.LightTernarySourceHost


