-- Prove2me | Definitions.Def_GaussianSweep_innerFrontier
-- name    : GaussianSweep_innerFrontier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:09.742613+00:00
-- url     : https://prove2.me/theorems/6bbc3c8b-4035-45f3-a147-406ea1fd8830
-- title:
--   Inner frontier $\partial^-S_t$
-- statement:
--   For a labeling $y : V(G) \to \mathbb R$ and $t \in \mathbb R$, with sublevel set $S_t = \{v : y_v \le t\}$, the **inner frontier** is
--   $$
--   \partial^- S_t = \{u \in S_t : N(u) \not\subseteq S_t\} = \{u : y_u \le t,\ \exists v \in N(u) : y_v > t\}.
--   $$
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 4.2, p.23 (PDF p.25)

import Mathlib

namespace GaussianSweep

/-- The inner frontier `∂⁻S_t = {u ∈ S_t : N(u) ⊄ S_t}` of the sublevel set
`S_t = {v : y_v ≤ t}` of a labeling `y` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 4.2, p.23 (PDF p.25)). -/
noncomputable def innerFrontier {V : Type*} [Fintype V] (G : SimpleGraph V) (y : V → ℝ) (t : ℝ) :
    Finset V :=
  by classical exact Finset.univ.filter fun u => y u ≤ t ∧ ∃ v, G.Adj u v ∧ t < y v

end GaussianSweep


