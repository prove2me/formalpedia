-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
-- name    : Submission_ThreeSum_LightTernaryNearEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:55.907366+00:00
-- url     : https://prove2.me/theorems/1e2d45f9-6aec-44e5-81f8-a396fb39a74a
-- title:
--   Light Ternary Near Enumeration
-- statement:
--   Definitions and structural lemmas for Light Ternary Near Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000
def output (qs : List ℕ) (D pref : ℕ) : List ℤ :=
  (words qs D).map (fun rs => ((pref+code rs : ℕ) : ℤ))
def Allowed (q r D : ℕ) : Prop := r ≤ q ∧ q-r ≤ D
instance (q r D : ℕ) : Decidable (Allowed q r D) := inferInstanceAs (Decidable (_ ∧ _))
def branchOutput (qs : List ℕ) (D pref q r : ℕ) : List ℤ :=
  if Allowed q r D then output qs (D-(q-r)) (pref+digitCode r*4^qs.length) else []
def branchCount (qs : List ℕ) (D q r : ℕ) : ℕ :=
  if Allowed q r D then (words qs (D-(q-r))).length else 0
def branchVisits (qs : List ℕ) (D q r : ℕ) : ℕ :=
  if Allowed q r D then visits qs (D-(q-r)) else 0
def branchBody (pSelf : ℕ) : Stmt :=
  .ite (v 7 ≤' v 6)
    (.ite (v 6 -' v 7 ≤' v 1)
      (.ite (v 7 =' k 2) (.set 8 (k 3)) (.set 8 (v 7)) ;;
        .call pSelf [v 0,v 1 -' (v 6 -' v 7),
          v 2 +' v 8 *' M (v 4 +' k 2 *' v 0),v 3,v 4,v 5] 0)
      (.set 0 (k 0)))
    (.set 0 (k 0))
def body (pBranch : ℕ) : Stmt :=
  .ite (v 0 <' k 1)
    (.store (v 3) (v 2) ;; .set 0 (k 1))
    (.set 6 (v 0 -' k 1) ;;
      .set 7 (M (v 5)) ;;
      .call pBranch [v 6,v 1,v 2,v 3,v 4,v 5 +' k 1,v 7,k 0] 8 ;;
      .call pBranch [v 6,v 1,v 2,v 3 +' v 8,v 4,v 5 +' k 1,v 7,k 1] 9 ;;
      .call pBranch [v 6,v 1,v 2,v 3 +' v 8 +' v 9,v 4,v 5 +' k 1,v 7,k 2] 10 ;;
      .set 0 (v 8 +' v 9 +' v 10))
def time (qs : List ℕ) (D : ℕ) : ℕ := 900 * visits qs D
def branchTime (qs : List ℕ) (D q r : ℕ) : ℕ := 900 * branchVisits qs D q r + 200
variable {lim : Limits} {P : Program}
def program : Program := [body 1,branchBody 0]
end ThreeSum.LightTernaryNearEnumeration


