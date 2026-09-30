-- Prove2me | Definitions.Def_KKBinPacking_LinearGrouping_LinGroup
-- name    : KKBinPacking_LinearGrouping_LinGroup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:17:59.878033+00:00
-- url     : https://prove2.me/theorems/36e73da2-bd8d-4fec-ba2f-da63bb8a191b
-- title:
--   Linear grouping with parameter $k$
-- statement:
--   Let $I$ be an instance and $k$ a positive integer. Sort the pieces of $I$ in non-increasing order of size and cut the sorted list into consecutive groups $G_1, G_2, \dots, G_q$ of $k$ pieces each (the last group may be smaller), so that $G_1$ holds the $k$ largest pieces, $G_2$ the next $k$ largest, and so on. Let $G_i'$ be the multiset obtained from $G_i$ by increasing the size of every piece to the largest size in $G_i$. **Linear grouping with parameter $k$** outputs
--
--   $$
--   J = \bigcup_{i=2}^{q} G_i', \qquad J' = G_1 .
--   $$
--
--   The purpose is to reduce the number of distinct sizes (at most $q-1$ in $J$) while increasing sizes only a little.
--
--   **Formalization Note** The pieces are sorted with `Multiset.sort (· ≥ ·)` and cut with `List.toChunks k`. Pieces are sizes, so ties among equal sizes do not affect the groups as multisets. Since each group is sorted non-increasingly, its largest size is its first element. The output is a pair `(J, J')`. For `k = 0`, which the paper excludes ("let $k$ be positive integer"), the definition puts all pieces into one group and returns $J = \emptyset$, $J' = I$; ALGORITHM 1 reaches `k = 0` only when its instance is empty, where both outputs are empty.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 314, §4 Linear Grouping

import Mathlib

namespace KKBinPacking.LinearGrouping

/-- The groups `G_1, G_2, …, G_q` of linear grouping with parameter `k` (p. 314): the pieces of
`I` sorted in non-increasing order and cut into consecutive blocks of `k` (the last block may
be shorter). -/
noncomputable def linGroups (k : ℕ) (I : Multiset ℝ) : List (List ℝ) :=
  (I.sort (· ≥ ·)).toChunks k

/-- `G'`: every piece of the group `G` raised to the maximum size in the group. The groups are
sorted non-increasingly, so the maximum is the head; for an empty group the result is empty. -/
noncomputable def roundUpGroup (G : List ℝ) : Multiset ℝ :=
  Multiset.replicate G.length (G.headD 0)

/-- Linear grouping with parameter `k` (p. 314): `linGroup k I = (J, J')` with
`J = G_2' ∪ ⋯ ∪ G_q'` (the rounded-up groups after the first) and `J' = G_1` (the `k` largest
pieces, not rounded). -/
noncomputable def linGroup (k : ℕ) (I : Multiset ℝ) : Multiset ℝ × Multiset ℝ :=
  ((((linGroups k I).drop 1).map roundUpGroup).sum,
    (((linGroups k I).headD []) : Multiset ℝ))

end KKBinPacking.LinearGrouping


