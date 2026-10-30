-- Prove2me | Definitions.Def_MITMSynthesis_sortC
-- name    : MITMSynthesis_sortC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:30.800553+00:00
-- url     : https://prove2.me/theorems/3c730a1c-f2e3-492f-9ff3-3e9b639a8aab
-- title:
--   Merge sort with counted comparisons and moves
-- statement:
--   Merge sort of a list by a key into a linearly ordered type, written in the cost monad:
--
--   1. a list with at most one element costs one step;
--   2. a list of length $m \ge 2$ is split into its first $\lfloor m/2\rfloor$ and remaining elements at cost $m$, both halves are sorted recursively, and the results are merged;
--   3. merging costs one step per comparison, one step per element output, and one step per element of the remaining list copied at the end.
--
--   This is the sorting step of MITM-factor, which sorts $S_i$ by the order on unitaries.
--
--   **Formalization Note** `sortC key l` uses `cmpC` for every comparison of keys; no library sort is called outside the cost monad.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6 ("The set S_i can then be sorted with respect to this ordering in O(|S_i| log(|S_i|)) time")

import Mathlib
import Definitions.Def_MITMSynthesis_Timed

namespace MITMSynthesis


variable {β : Type} {κ : Type} [LinearOrder κ]

/-- Merge two lists (sorted by `key`), charging one comparison per step plus one step per
element output, and one step per element of a list copied at the end. -/
def mergeC (key : β → κ) : List β → List β → Timed (List β)
  | [], ys => do ticks (ys.length + 1); pure ys
  | x :: xs, [] => do ticks (xs.length + 2); pure (x :: xs)
  | x :: xs, y :: ys => do
      let o ← cmpC (key x) (key y)
      if o = Ordering.gt then do
        let r ← mergeC key (x :: xs) ys
        tick
        pure (y :: r)
      else do
        let r ← mergeC key xs (y :: ys)
        tick
        pure (x :: r)
termination_by xs ys => xs.length + ys.length

/-- **Merge sort by `key`**, written inside `Timed`: splitting a list of length `m` costs `m`
steps, every comparison costs a step, and every element moved by a merge costs a step. -/
def sortC (key : β → κ) (l : List β) : Timed (List β) :=
  match l with
  | [] => do tick; pure []
  | [x] => do tick; pure [x]
  | x :: y :: zs => do
      ticks (zs.length + 2)
      let a ← sortC key ((x :: y :: zs).take ((zs.length + 2) / 2))
      let b ← sortC key ((x :: y :: zs).drop ((zs.length + 2) / 2))
      mergeC key a b
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

end MITMSynthesis


