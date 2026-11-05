-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixHeaderSegment
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixHeaderSegment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:03:21.655893+00:00
-- url     : https://prove2.me/theorems/eaa6fa7d-792c-4a5c-968c-8312b14f1974
-- title:
--   TernaryPrefixHeaderSegment
-- statement:
--   Definitions and structural lemmas for TernaryPrefixHeaderSegment, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000
def patchList (loc : ℕ→ℤ) : List ℤ→ List (ℕ×ℕ)→ List ℤ
  | xs,[]=>xs
  | xs,(i,r)::fs=>patchList loc (xs.set i (loc r)) fs
def resultHeader (templateValues : List ℤ)
    (template live hdr s m p power alpha2 alphaRank localQ radix J N T L groups nb bank powers Fbase Gbase : ℕ)
    (ret : ℤ) : List ℤ :=
  (patchList
    (frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
      locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]))
    templateValues LightWeightedGlobalPrefixLoop.headerWrites).set 104 0
end ThreeSum.LightWeightedGlobalPrefixHeader
end WeightedCache3SUMRefinement_e1ae71d


