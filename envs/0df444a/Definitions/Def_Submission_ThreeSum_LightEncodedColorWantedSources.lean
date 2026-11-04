-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
-- name    : Submission_ThreeSum_LightEncodedColorWantedSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:21:32.109557+00:00
-- url     : https://prove2.me/theorems/a6a0ac8f-3997-4f60-b238-9350e57f8179
-- title:
--   Light Encoded Color Wanted Sources
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Wanted Sources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorWantedSources.lean

import Definitions.Def_Submission_ThreeSum_LightEncodedColorFiniteSources
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorWantedSources
open Light Scales TrimScales BandScales
set_option maxHeartbeats 2500000
set_option maxRecDepth 13000
def body (pWanted pSources : ℕ) : Stmt :=
  .call pWanted [v 0,v 1,v 3,v 4,v 5,v 6,v 7] 13 ;;
  .call pSources [v 0,v 1,v 2,v 8,v 9,v 10,v 11,v 12,v 5,v 13,v 7] 0
def joined : Program := ReportingHostRelocation.program LightGuardedWanted.program LightEncodedColorSources.program
def program : Program := joined ++ [body 98 179]
def args (a free bv be cv ce n p M len : ℕ) : List ℤ :=
  [microHalf (inputBits n),blockCount (inputBits n),mu n,a,len,p,M,free,bv,be,cv,ce,bandSize n]
def time (n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightGuardedWanted.time p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs+
    EncodedColorSourcesCosts.time n p U M+400
def space (free n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (LightGuardedWanted.space free p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs)
    (SourceFiniteCosts.space (LightEncodedColorFiniteSources.base free n p M xs) n p U M)
def word (n p M U len : ℕ) : ℕ :=
  max (LightGuardedWanted.word p M (microHalf (inputBits n)) (blockCount (inputBits n)) U len)
    (SourceFiniteCosts.word n p U M)
def depth (n M len : ℕ) : ℕ :=
  max (512*microHalf (inputBits n)+blockCount (inputBits n)+Nat.clog 2 M+3*len+13)
    (256*mu n+18)
variable {lim : Limits} {d : ℕ}
end ThreeSum.LightEncodedColorWantedSources


