-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
-- name    : Submission_Weighted_Global_TernaryPrefixHeaderSegment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:43:05.452811+00:00
-- url     : https://prove2.me/theorems/7b04202e-b161-40eb-8046-83f4211442a8
-- title:
--   Ternary Prefix Header Segment
-- statement:
--   Definitions and structural lemmas for Ternary Prefix Header Segment, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
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


