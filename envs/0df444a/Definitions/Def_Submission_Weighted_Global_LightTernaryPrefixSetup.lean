-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
-- name    : Submission_Weighted_Global_LightTernaryPrefixSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:48:01.768631+00:00
-- url     : https://prove2.me/theorems/954c87a7-1be1-4233-9501-3f0ce3be02c8
-- title:
--   Light Ternary Prefix Setup
-- statement:
--   Definitions and structural lemmas for Light Ternary Prefix Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
def N (m j : ℕ) : ℕ := 30000000000000*(j*m)
def T (m j : ℕ) : ℕ := 3130753934820264*(j*m)
def nb (m j : ℕ) : ℕ := (codes (N m j) (T m j)).length
def header (m j F bank work : ℕ) : List ℤ :=
  [N m j,T m j,2*N m j,(F^j:ℕ),nb m j,bank,work,j]
def body (pPower pSetup : ℕ) : Stmt :=
  .set 6 (v 0 *' v 1) ;;
  .set 7 (k 30000000000000 *' v 6) ;;
  .set 8 (k 3130753934820264 *' v 6) ;;
  .set 9 (k 2 *' v 7) ;;
  .call pPower [v 2,v 0] 10 ;;
  .call pSetup [v 7,v 8,v 4,v 5] 11 ;;
  .store (v 3) (v 7) ;;
  .store (v 3 +' k 1) (v 8) ;;
  .store (v 3 +' k 2) (v 9) ;;
  .store (v 3 +' k 3) (v 10) ;;
  .store (v 3 +' k 4) (v 11) ;;
  .store (v 3 +' k 5) (v 4) ;;
  .store (v 3 +' k 6) (v 5) ;;
  .store (v 3 +' k 7) (v 0) ;;
  .set 0 (v 3)
def word (m j F : ℕ) : ℕ :=
  3130753934820264+1025*N m j+j+m+F+(F+1)^(j+1)+4^(N m j+1)+1100
def time (m j : ℕ) : ℕ := LightNatPower.time j+LightWeightedEnumerationSetup.time (N m j) (T m j)+500
variable {lim : Limits} {P : Program}
def program : Program := [body 1 2,LightNatPower.body,LightWeightedEnumerationSetup.body 3 4,
  powTableBody,LightCacheEnumeration.body 4]
def workAt (free m j : ℕ) : ℕ := free+4^(N m j)
def headerAt (free m j : ℕ) : ℕ := workAt free m j+2*N m j+1
def endAt (free m j : ℕ) : ℕ := headerAt free m j+8
def allocateBody (pPower pPrefix : ℕ) : Stmt :=
  .set 4 (v 0 *' v 1) ;;
  .set 5 (k 30000000000000 *' v 4) ;;
  .call pPower [k 4,v 5] 6 ;;
  .set 7 (v 3 +' v 6) ;;
  .set 8 (v 7 +' k 2 *' v 5 +' k 1) ;;
  .call pPrefix [v 0,v 1,v 2,v 8,v 3,v 7] 0
def allocateTime (m j : ℕ) : ℕ := LightNatPower.time (N m j)+time m j+200
def allocatedProgram : Program := program++[allocateBody 1 0]
end ThreeSum.LightWeightedGlobalPrefixSetup


