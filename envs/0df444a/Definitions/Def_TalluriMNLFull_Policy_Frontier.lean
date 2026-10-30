-- Prove2me | Definitions.Def_TalluriMNLFull_Policy_Frontier
-- name    : TalluriMNLFull_Policy_Frontier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:59:01.470978+00:00
-- url     : https://prove2.me/theorems/4c4fe7ee-d5e1-4f1e-80db-f6df4f825b6c
-- title:
--   Tie-aware fare frontier
-- statement:
--   Let $N$ be the finite product set and $r_i$ the fare of product $i$. An assortment $S$ has **no strict fare inversion** when
--   $$
--   \forall i\notin S\;\forall j\in S,\qquad r_i\le r_j.
--   $$
--   This condition permits any selection within an equal-fare block and permits the empty set. It does not define or assume nondominance. With fares in decreasing order, it describes a prefix after reordering within fare ties, with the reordering allowed to depend on $S$.
--
--   This is the minimal corrected frontier conclusion of Proposition 6. For two unit weights and two unit fares, the singleton containing product 2 is nondominated although it is not a fixed-order prefix. The goal relates this independently defined condition to the published two-branch Definition 1.
-- source:
--   Talluri and van Ryzin, Revenue Management Under a General Discrete Choice Model of Consumer Behavior, UPF Economics Working Paper 533, October 21, 2001, Proposition 6, corrected frontier clause, printed p. 23 (PDF p. 23), https://econ-papers.upf.edu/papers/533.pdf; PDF SHA-256 053050fd8f6c12672e0e41e7782705b4f3a78b906f24bb52c7697a6d8c453c2c.

import Mathlib

namespace TalluriMNLFull.Policy

/-- The corrected first clause of Proposition 6 (p. 23): no excluded product has a
strictly higher fare than an included product. This is independent of nondominance. -/
def NoStrictFareInversion {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ i : Fin n, i ∉ S → ∀ j : Fin n, j ∈ S → r i ≤ r j

end TalluriMNLFull.Policy


