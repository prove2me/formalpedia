-- Prove2me | Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict
-- name    : QuantumLTF_Membership_boundarySearchTreeStrict
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-15T02:54:19.616331+00:00
-- url     : https://prove2.me/theorems/1ed4059c-9dbf-41e4-af3a-6a42d9616ee5
-- title:
--   Strict-endpoint boundary-search query tree
-- statement:
--   The corrected Theorem 3.1 decision tree queries at the two points corresponding to scalar parameters $L+1$ and $-(L+1)$, strictly outside the promised boundary interval. This avoids ambiguity from the convention sign(0)=1, then bisects the original interval $[-L,L]$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, pp. 21–22 (PDF pp. 22–23).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTree

namespace QuantumLTF.Membership

/-- Corrected boundary-search tree: orientation is learned strictly outside the promised interval
`[-L,L]`, avoiding the `sgn 0 = 1` endpoint ambiguity.  Bisection itself remains on `[-L,L]`. -/
noncomputable def boundarySearchTreeStrict {n : ℕ} (p : EuclideanSpace ℝ (Fin n))
    (L : ℝ) (q : ℕ) : QueryTree n (ℤ × ℝ) :=
  .query ((L + 1) • p) fun rightAns =>
    .query ((-(L + 1)) • p) fun leftAns =>
      let s : ℤ := if rightAns = 1 ∧ leftAns = -1 then 1 else -1
      (boundaryBisect p s q (-L) L).map fun h => (s, h)

end QuantumLTF.Membership


