-- Prove2me | Definitions.Def_Submission_ThreeSum_LightGuardedWanted
-- name    : Submission_ThreeSum_LightGuardedWanted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:12:37.150628+00:00
-- url     : https://prove2.me/theorems/1524ce18-8f37-4afa-9666-91a6786b1748
-- title:
--   Light Guarded Wanted
-- statement:
--   Definitions and structural lemmas for Light Guarded Wanted, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
def left (P : ℕ) (xs : List ℤ) : ℕ → ℤ := fun i => (RawAKeyLists.keys P xs).getD i 0
def right (h J : ℕ) : ℕ → ℤ := fun j => (globalKeys h J).getD j 0
def totalKeys (h J : ℕ) : ℕ := LightGlobalKeys.localCount h^J
def keyBound (P h J : ℕ) : ℕ := 2*P+(512*h*localPrime h)*(localPrime h+1)^J
def wantedFree (free h J n : ℕ) : ℕ := LightCoverKeyData.keyEnd free h J+3*n
def body (pCover pLifts pWanted : ℕ) : Stmt :=
  .call pCover [v 0,v 1,v 6] 7 ;;
  .set 8 (M (v 7)) ;;
  .set 9 (v 7 +' k 1) ;;
  .set 10 (v 9 +' v 8) ;;
  .set 11 (k 3 *' v 3) ;;
  .set 12 (v 10 +' v 11) ;;
  .call pLifts [v 2,v 3,v 4,v 10] 13 ;;
  .call pWanted [v 10,v 9,v 11,v 8,v 5,v 12] 0
def liftProgram : Program := ReportingHostRelocation.program LightCoverKeys.program LightRawAKeys.program
def program : Program := ReportingHostRelocation.program liftProgram LightBalancedWanted.program ++
  [body 67 68 97]
def time (P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightCoverKeys.time h J+LightRawAKeys.time xs.length U+
    LightBalancedWanted.time M (left P xs) (right h J) (3*xs.length) (totalKeys h J)
      (keyBound P h J)+300
def space (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (LightCoverKeys.space free h J)
    (max (LightRawAKeys.space (LightCoverKeyData.keyEnd free h J) xs.length U)
      (LightBalancedWanted.space (wantedFree free h J xs.length) M (left P xs) (right h J)
        (3*xs.length) (totalKeys h J) (keyBound P h J)))
def word (P M h J U n : ℕ) : ℕ :=
  max (LightCoverKeys.word h J) (max (LightRawAKeys.word P U)
    (LightBalancedWanted.word M (3*n) (totalKeys h J) (keyBound P h J)))
variable {lim : Limits}
end ThreeSum.LightGuardedWanted


