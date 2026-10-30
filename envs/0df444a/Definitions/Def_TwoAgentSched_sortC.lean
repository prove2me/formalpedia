-- Prove2me | Definitions.Def_TwoAgentSched_sortC
-- name    : TwoAgentSched_sortC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:47:16.67399+00:00
-- url     : https://prove2.me/theorems/1d4e69ad-de7c-4d4e-abdf-c62c3c3004ac
-- title:
--   Merge sort by a key, with its comparison cost
-- statement:
--   **Merge sort** of a list by a key into a linearly ordered set, written as a timed computation:
--
--   1. a list of length at most one is returned as is, at no cost;
--   2. a list of length $m\ge2$ is split into halves at a cost of $m$ steps, both halves are sorted recursively, and the sorted halves are **merged**: each comparison of two keys costs one step, each element output costs one step, and handing back the remaining list when one side is exhausted costs one step.
--
--   The algorithm of §4 uses it to order the B-jobs by deadline before the main loop, the step the paper charges $O(n_B\log n_B)$.
--
--   **Formalization Note** `mergeC` and `sortC` are defined by well-founded recursion on list lengths; no uncharged library sort is used.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), p. 233 ("The job set J^B can be ordered a priori, in nondecreasing order of deadlines D^B_k, in time O(n_B log n_B)")

import Mathlib
import Definitions.Def_TwoAgentSched_Timed

namespace TwoAgentSched

variable {β : Type} {κ : Type} [LinearOrder κ]

/-- Merge two lists (each sorted by `key`): one step per key comparison, one step per element
output, and one step to hand back the remaining list when one side is exhausted. -/
def mergeC (key : β → κ) : List β → List β → Timed (List β)
  | [], ys => do tick; pure ys
  | x :: xs, [] => do tick; pure (x :: xs)
  | x :: xs, y :: ys => do
      let b ← leC (key x) (key y)
      if b then do
        let r ← mergeC key xs (y :: ys)
        tick
        pure (x :: r)
      else do
        let r ← mergeC key (x :: xs) ys
        tick
        pure (y :: r)
termination_by xs ys => xs.length + ys.length

/-- **Merge sort by `key`**, nondecreasing, written inside `Timed`. A list of length `≤ 1` is
returned as is, at no cost. A list of length `m ≥ 2` is split in `m` steps (computing its length
and its halves), both halves are sorted recursively, and the results are merged by `mergeC`
(one step per comparison and per element moved). -/
def sortC (key : β → κ) (l : List β) : Timed (List β) :=
  match l with
  | [] => pure []
  | [x] => pure [x]
  | x :: y :: zs => do
      ticks (zs.length + 2)
      let a ← sortC key ((x :: y :: zs).take ((zs.length + 2) / 2))
      let b ← sortC key ((x :: y :: zs).drop ((zs.length + 2) / 2))
      mergeC key a b
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

end TwoAgentSched


