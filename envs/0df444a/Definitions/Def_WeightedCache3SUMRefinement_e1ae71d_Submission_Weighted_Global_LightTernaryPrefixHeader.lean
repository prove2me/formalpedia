-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:59:48.216931+00:00
-- url     : https://prove2.me/theorems/2c023e02-1baa-4781-89a7-3a9ddefbb501
-- title:
--   LightTernaryPrefixHeader
-- statement:
--   Definitions and structural lemmas for LightTernaryPrefixHeader, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixHeader.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
    (N+1)*nb,N*nb,(2738*(alphaRank*s)+6*(alpha2*s)),(((2738*(alphaRank*s)+6*(alpha2*s))-T-1:ℕ):ℤ),
    LightTernaryRepeatWord.value localQ radix s,Fbase+N*nb,Gbase+N*nb]
def time (s alpha2 : ℕ) : ℕ := LightNatPower.time (alpha2*s)+LightTernaryRepeatWord.time s+5000
end ThreeSum.LightWeightedGlobalPrefixHeader
end WeightedCache3SUMRefinement_e1ae71d


