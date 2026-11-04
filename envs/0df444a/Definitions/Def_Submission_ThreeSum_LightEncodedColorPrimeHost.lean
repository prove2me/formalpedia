-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
-- name    : Submission_ThreeSum_LightEncodedColorPrimeHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:49:44.810186+00:00
-- url     : https://prove2.me/theorems/9ea8e9e0-2786-48b9-8850-5f0796afb0e6
-- title:
--   Light Encoded Color Prime Host
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Prime Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrimeHost.lean

import Definitions.Def_Submission_ThreeSum_LightEncodedColorNormalize
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorPrimeHost
open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout
set_option maxHeartbeats 3200000
set_option maxRecDepth 15000
def body (pNormalize pPrime : ℕ) : Stmt :=
  .call pNormalize [v 0,v 1,v 2,v 3,v 4] 5 ;;
  .set 6 (v 5 +' k 1) ;;
  .set 7 (M (v 4)) ;;
  .set 8 (M (v 4 +' k 1)) ;;
  .set 9 (M (v 4 +' k 2)) ;;
  .set 10 (M (v 4 +' k 3)) ;;
  .set 11 (M (v 4 +' k 4)) ;;
  .set 12 (M (v 4 +' k 5)) ;;
  .set 13 (M (v 4 +' k 6)) ;;
  .set 14 (M (v 2 +' k 17)) ;;
  .set 15 (M (v 2 +' k 14)) ;;
  .set 16 (M (v 2 +' k 18)) ;;
  .call pPrime [v 7,v 8,v 9,v 10,v 11,v 12,v 14,v 13,v 15,v 16,v 6] 17 ;;
  .set 0 (v 6)
def joined : Program := ReportingHostRelocation.program LightEncodedColorNormalize.program LightEncodedColorPrime.program
def program : Program := joined ++ [body 45 70]
def time (k n : ℕ) : ℕ := LightEncodedColorNormalize.time n+BandPrimeCosts.timeBudget k n+1760
def space (free k n : ℕ) : ℕ := max (LightEncodedColorNormalize.space free n)
  (LightEncodedColorPrimeCore.space (prime free n (bandSize n)) (maxMod n) (bandSize n)
    (radix n) (primeWindow n) (n^k))
def word (k n : ℕ) : ℕ := max (LightEncodedColorNormalize.word n (n^k))
  (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) (n^k))+
    bandSize n+radix n+primeWindow n+100
def depth (n : ℕ) : ℕ := max
  (LightBandRawAColor.depth (inputBits n+1) n (bandSize n)+3)
  (Nat.clog 2 (maxMod n)+11)
def inputTime (n U : ℕ) : ℕ := LightEncodedColorNormalize.time n+
  LightEncodedColorPrime.time (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U+600
def inputSpace (free n U : ℕ) : ℕ := max (LightEncodedColorNormalize.space free n)
  (LightEncodedColorPrimeCore.space (prime free n (bandSize n)) (maxMod n) (bandSize n)
    (radix n) (primeWindow n) U)
def inputWord (n U : ℕ) : ℕ := max (LightEncodedColorNormalize.word n U)
  (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U)+
    bandSize n+radix n+primeWindow n+100
variable {lim : Limits} {d : ℕ}
end ThreeSum.LightEncodedColorPrimeHost


