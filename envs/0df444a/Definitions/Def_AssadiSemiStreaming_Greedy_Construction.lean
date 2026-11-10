-- Prove2me | Definitions.Def_AssadiSemiStreaming_Greedy_Construction
-- name    : AssadiSemiStreaming_Greedy_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:40:52.462582+00:00
-- url     : https://prove2.me/theorems/d7a21b01-7776-4ffa-a32c-83f684cfa98e
-- title:
--   The explicit blueprint constructed from complementary buckets
-- statement:
--   For every j∈{1,…,2m−1} and t∈{L,…,D}, enumerate the left bucket (j,t) and right bucket (2m−j,t), zip the lists, and take those pairs as edges. List zipping stops at the shorter list, thereby choosing subsets of the prescribed minimum cardinality and a bijection between them. This fixes the arbitrary choices permitted in §6.2. Take the union over all such j,t. Each resulting edge receives source type t+2, represented internally by index t+1 recovered from its left endpoint maximum time. The constructor contains no global matching hypothesis, ban hypothesis, value lower bound, or framework oracle. Its range guard gives no edge only at out-of-range types; the guard always succeeds for the construction domain m≥1 and L≤t≤D.
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), §6.2, printed p. 19 / PDF 21

import Definitions.Def_AssadiSemiStreaming_Greedy_DelayedWalk

namespace AssadiSemiStreaming.Greedy

/-- A concrete allowed choice of subsets and bijection: pair the arbitrary
finite enumerations until the smaller bucket is exhausted. No global matching
or ban condition is imposed on this operation. -/
noncomputable def bucketPairs (m j t : ℕ) : Finset (WalkLabel m × WalkLabel m) := by
  classical
  exact ((bucket m false j t).toList.zip (bucket m true (2 * m - j) t).toList).toFinset

noncomputable def constructedPairs (m : ℕ) : Finset (WalkLabel m × WalkLabel m) := by
  classical
  exact (Finset.Icc 1 (2 * m - 1)).biUnion (fun j =>
    (Finset.Icc (lengthBound m) (delayBound m)).biUnion (bucketPairs m j))

/-- The type p=t+2 is represented by the zero-based index t+1. -/
noncomputable def constructedBlueprint (m : ℕ) : Blueprint := by
  classical
  exact {
    P := labelLength m
    C := alphabetSize m
    edgeType := fun x y =>
      if (x, y) ∈ constructedPairs m then
        if h : maximumTime m false x + 1 < labelLength m then
          some ⟨maximumTime m false x + 1, h⟩
        else none
      else none }


end AssadiSemiStreaming.Greedy


