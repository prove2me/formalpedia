-- Prove2me | Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
-- name    : KKBinPacking_GeometricGrouping_GeomGroup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T17:06:48.265846+00:00
-- url     : https://prove2.me/theorems/f5b5eb11-482c-4fe5-bb47-b65aa3234cdf
-- title:
--   The second variation of geometric grouping, producing $J$ and $J'$
-- statement:
--   Let $I$ be an instance and $k$ a positive integer. **Geometric grouping** (second variation) sorts the pieces of $I$ in non-increasing order of size and cuts the sorted list greedily into consecutive groups $G_1, G_2, \dots, G_q$: starting from the largest piece, $G_1$ receives as many pieces as necessary to make its total size at least $k$; the same operation on the remaining pieces gives $G_2$, and so on. The last group may fall short of $k$ when the pieces run out. Let $l_i = |G_i|$.
--
--   For $i = 2, \dots, q$:
--
--   1. $\Delta G_i$ is the set of the smallest $\max(0,\, l_i - l_{i-1})$ pieces of $G_i$, so that $G_i - \Delta G_i$ consists of the $\min(l_i, l_{i-1})$ largest pieces of $G_i$;
--   2. $G_i'$ is obtained from $G_i - \Delta G_i$ by increasing the size of each piece to the largest size in $G_i$.
--
--   The two output instances are
--
--   $$J = \bigcup_{i=2}^{q} G_i', \qquad J' = G_1 \cup \bigcup_{i=2}^{q} \Delta G_i.$$
--
--   The pieces of $J$ take at most $q-1$ distinct sizes, while $J'$ is small; this is the reduction ALGORITHM 2 applies before each call of the linear programming subroutine.
--
--   **Formalization Note** `geomPairs k I` records $J$ together with the real pieces it rounds: it is the multiset of pairs (real piece of $G_i - \Delta G_i$, rounded size), so that `geomJ k I` (the second components) is $J$ and the first components together with `geomJ' k I` form exactly $I$. Sorting a multiset of reals is unique, so the construction is deterministic. The paper asserts $l_1 \le l_2 \le \dots \le l_q$, which fails when the last group falls short of $k$; the convention $\Delta G_i$ = the smallest $\max(0, l_i - l_{i-1})$ pieces handles that case and keeps $G_i' \le G_{i-1}$. The paper's display writes $J = \bigcup_{i=2}^q G_i$ and $J' = \bigcup_{i=2}^q \Delta G_i' \cup G_1$; the primes are misplaced, and the definition follows the construction in the text ($J$ from the rounded $G_i'$, $J'$ from the unrounded $\Delta G_i$).
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 315, §4, "Now we present another variation of Geometric Grouping" (left column, definition of G_i, ΔG_i, G_i', J, J')

import Mathlib

namespace KKBinPacking.GeometricGrouping

/-- `takeUntil k L`: the shortest prefix of the list `L` whose sum is at least `k`, or all of
`L` if its total is below `k`. Applied to the pieces sorted in non-increasing order, this is
"put as many items in the group as necessary to make the size of the group equal or exceed
`k`" (p. 315). -/
noncomputable def takeUntil (k : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs => if k ≤ x then [x] else x :: takeUntil (k - x) xs

/-- A group cut from a nonempty list is nonempty (structural; used for termination). -/
theorem takeUntil_cons_length_pos (k x : ℝ) (xs : List ℝ) :
    0 < (takeUntil k (x :: xs)).length := by
  unfold takeUntil
  split_ifs <;> simp

/-- The groups `G_1, G_2, …, G_q` of the second variation of geometric grouping (p. 315):
cut the list `L` greedily into consecutive groups, each the shortest prefix of what remains
whose size is at least `k`; the last group may fall short of `k`. -/
noncomputable def geomGroupsList (k : ℝ) : List ℝ → List (List ℝ)
  | [] => []
  | x :: xs =>
      takeUntil k (x :: xs) ::
        geomGroupsList k ((x :: xs).drop (takeUntil k (x :: xs)).length)
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

/-- The groups `G_1, …, G_q` of `I` with parameter `k` (p. 315): the pieces of `I` sorted in
non-increasing order of size, then cut by `geomGroupsList`. Each group is a non-increasing
list, so its head is its largest piece and its last entries are its smallest pieces. -/
noncomputable def geomGroups (k : ℕ) (I : Multiset ℝ) : List (List ℝ) :=
  geomGroupsList (k : ℝ) (I.sort (· ≥ ·))

/-- The rounded part of geometric grouping (p. 315), as pairs (real piece, rounded size). For
each `i ≥ 2`, `G_i − ΔG_i` consists of the `l_{i−1}` largest pieces of `G_i` (all of `G_i` when
`l_i ≤ l_{i−1}`, which can only happen for a short last group), and each of them is paired
with the maximum size of a piece in `G_i − ΔG_i`, i.e. the head of `G_i`. The second
components form `J = ⋃_{i ≥ 2} G_i'`; the first components are the real pieces. -/
noncomputable def geomPairs (k : ℕ) (I : Multiset ℝ) : Multiset (ℝ × ℝ) :=
  (List.zipWith
      (fun (Gprev Gi : List ℝ) =>
        (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0)) : List (ℝ × ℝ)) :
          Multiset (ℝ × ℝ)))
      (geomGroups k I) (geomGroups k I).tail).sum

/-- `J = ⋃_{i=2}^{q} G_i'` (p. 315): the rounded-up pieces. -/
noncomputable def geomJ (k : ℕ) (I : Multiset ℝ) : Multiset ℝ :=
  (geomPairs k I).map Prod.snd

/-- `J' = ⋃_{i=2}^{q} ΔG_i ∪ G_1` (p. 315): the first group together with, for each `i ≥ 2`,
the set `ΔG_i` of the smallest `max(0, l_i − l_{i−1})` pieces of `G_i`, not rounded. -/
noncomputable def geomJ' (k : ℕ) (I : Multiset ℝ) : Multiset ℝ :=
  (((geomGroups k I).headD []) : Multiset ℝ) +
    (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length : List ℝ) : Multiset ℝ))
      (geomGroups k I) (geomGroups k I).tail).sum

end KKBinPacking.GeometricGrouping


