-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
-- name    : Submission_Weighted_Global_LightTernaryPrefixHeader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:34:36.483321+00:00
-- url     : https://prove2.me/theorems/4a07b6ae-4b08-4874-884b-eb8231df7012
-- title:
--   Light Ternary Prefix Header
-- statement:
--   Definitions and structural lemmas for Light Ternary Prefix Header, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
namespace ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
noncomputable def patch (base : ℕ) (loc : ℕ→ ℤ) : (ℕ→ ℤ)→ List (ℕ×ℕ)→ (ℕ→ ℤ)
  | μ,[]=>μ
  | μ,(i,r)::xs=>patch base loc (Function.update μ (base+i) (loc r)) xs
def args (template live hdr s m p power alpha2 alphaRank localQ radix J : ℕ) : List ℤ :=
  [template,live,hdr,s,m,p,power,alpha2,alphaRank,localQ,radix,J]
def locals (N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase : ℕ) : List ℤ :=
  [N,T,L,groups,nb,bank,powers,power*p,alpha2*s,2^(alpha2*s),alphaRank*s,
    (N+1)*nb,N*nb,(1024*(alphaRank*s)+3*(alpha2*s)),(((1024*(alphaRank*s)+3*(alpha2*s))-T-1:ℕ):ℤ),
    LightTernaryRepeatWord.value localQ radix s,Fbase+N*nb,Gbase+N*nb]
def time (s alpha2 : ℕ) : ℕ := LightNatPower.time (alpha2*s)+LightTernaryRepeatWord.time s+5000
end ThreeSum.LightWeightedGlobalPrefixHeader


