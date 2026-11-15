-- Prove2me | Definitions.Def_QuantumLTF_Membership_boundarySearchTree
-- name    : QuantumLTF_Membership_boundarySearchTree
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-15T02:38:43.121497+00:00
-- url     : https://prove2.me/theorems/e7b2f726-3236-475e-b39c-b03298d427a9
-- title:
--   Boundary-search query tree
-- statement:
--   An explicit deterministic decision tree for Theorem 3.1. It queries the two endpoints of the promised interval to determine the orientation of the threshold along the reference direction, then performs orientation-aware bisection for a prescribed number of steps.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, pp. 21–22 (PDF pp. 22–23).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_QueryTree

namespace QuantumLTF.Membership

def QueryTree.map {n : ℕ} {α β : Type} (g : α → β) : QueryTree n α → QueryTree n β
  | .leaf a => .leaf (g a)
  | .query x next => .query x fun ans => (next ans).map g

/-- Orientation-aware bisection on the line `t ↦ t • p`.  For positive orientation,
an answer `1` moves the right endpoint to the midpoint; for negative orientation it moves the
left endpoint.  Non-`±1` branches are irrelevant for membership oracles and follow the `-1`
branch. -/
noncomputable def boundaryBisect {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) (s : ℤ) :
    ℕ → ℝ → ℝ → QueryTree n ℝ
  | 0, lo, hi => .leaf ((lo + hi) / 2)
  | k + 1, lo, hi =>
      let mid := (lo + hi) / 2
      .query (mid • p) fun ans =>
        if s = 1 then
          if ans = 1 then boundaryBisect p s k lo mid
          else boundaryBisect p s k mid hi
        else
          if ans = 1 then boundaryBisect p s k mid hi
          else boundaryBisect p s k lo mid

/-- Query both endpoints to learn the orientation and then bisect the boundary location.
`q` is the number of bisection queries after the two endpoint queries. -/
noncomputable def boundarySearchTree {n : ℕ} (p : EuclideanSpace ℝ (Fin n))
    (L : ℝ) (q : ℕ) : QueryTree n (ℤ × ℝ) :=
  .query (L • p) fun rightAns =>
    .query ((-L) • p) fun leftAns =>
      let s : ℤ := if rightAns = 1 ∧ leftAns = -1 then 1 else -1
      (boundaryBisect p s q (-L) L).map fun h => (s, h)

end QuantumLTF.Membership


