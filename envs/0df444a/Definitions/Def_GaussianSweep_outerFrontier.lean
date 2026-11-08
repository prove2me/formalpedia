-- Prove2me | Definitions.Def_GaussianSweep_outerFrontier
-- name    : GaussianSweep_outerFrontier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:05.787207+00:00
-- url     : https://prove2.me/theorems/a53290f1-a22f-4e19-b9ec-5277d3f48dd1
-- title:
--   Outer frontier $\partial^+S_t$
-- statement:
--   For a labeling $y : V(G) \to \mathbb R$ and $t \in \mathbb R$, let $S_t = \{v : y_v \le t\}$ be the sublevel set. Its **outer frontier** is
--   $$
--   \partial^+ S_t = N(S_t) \setminus S_t = \{v : y_v > t,\ \exists u \in N(v) : y_u \le t\}.
--   $$
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 4.2, p.23 (PDF p.25)

import Mathlib

namespace GaussianSweep

/-- The outer frontier `∂⁺S_t = N(S_t) ∖ S_t = {v : y_v > t, ∃ u ∈ N(v) : y_u ≤ t}` of the
sublevel set `S_t = {v : y_v ≤ t}` of a labeling `y` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 4.2, p.23 (PDF p.25)). -/
noncomputable def outerFrontier {V : Type*} [Fintype V] (G : SimpleGraph V) (y : V → ℝ) (t : ℝ) :
    Finset V :=
  by classical exact Finset.univ.filter fun v => t < y v ∧ ∃ u, G.Adj v u ∧ y u ≤ t

end GaussianSweep


