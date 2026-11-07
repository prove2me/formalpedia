-- Prove2me | Definitions.Def_QuantumLTF_Membership_QueryTree
-- name    : QuantumLTF_Membership_QueryTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:44.10046+00:00
-- url     : https://prove2.me/theorems/0e18c418-3e96-4bc5-8137-6e2706ffdbe2
-- title:
--   A deterministic membership-query algorithm as a decision tree
-- statement:
--   A deterministic membership-query algorithm is a tree: a leaf returns an output, and a node queries the function at a point of $\mathbb R^n$ and continues according to the answer. Its output against a function is the leaf reached, and its depth is the worst-case number of queries over answer sequences in $\{1,-1\}$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, p. 21 (PDF p. 22)

import Mathlib

namespace QuantumLTF.Membership

/-- **A deterministic membership-query algorithm, as a decision tree.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.1, p. 21
(PDF p. 22): "a deterministic algorithm that uses O(log(L_ϵ/ζ)) membership queries". A node queries
the function at a point of `Rⁿ` and continues according to the answer; a leaf returns the output.

**Formalization Note.** The tree is fixed before the target; children are read at `next 1` and
`next (-1)` only, the answers of a `±1`-valued function. -/
inductive QueryTree (n : ℕ) (α : Type) where
  /-- Stop and output `a`. -/
  | leaf (a : α) : QueryTree n α
  /-- Query at the point `x`, then continue with `next (answer)`. -/
  | query (x : EuclideanSpace ℝ (Fin n)) (next : ℤ → QueryTree n α) : QueryTree n α

/-- The output of the tree against the function `f`. -/
noncomputable def QueryTree.run {n : ℕ} {α : Type} : QueryTree n α → (EuclideanSpace ℝ (Fin n) → ℤ) → α
  | .leaf a, _ => a
  | .query x next, f => (next (f x)).run f

/-- The worst-case number of queries along a path of answers in `{1, −1}`. -/
def QueryTree.depth {n : ℕ} {α : Type} : QueryTree n α → ℕ
  | .leaf _ => 0
  | .query _ next => 1 + max (next 1).depth (next (-1)).depth

end QuantumLTF.Membership


