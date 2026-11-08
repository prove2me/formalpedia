-- Prove2me | Definitions.Def_GaussianSweep_switchD
-- name    : GaussianSweep_switchD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:08.127871+00:00
-- url     : https://prove2.me/theorems/d8c10334-97eb-4f83-994b-ab890da8f2a0
-- title:
--   The set $D$ of vertices switched at threshold zero
-- statement:
--   For a labeling $y$ of a graph $G$, let $D$ be the set of vertices of degree $3$ all of whose neighbors lie on the other side of zero:
--   $$
--   D = \{v : d(v) = 3 \text{ and } \big(y_v \le 0 < \min_{x \in N(v)} y_x \ \text{ or } \ y_v > 0 \ge \max_{x \in N(v)} y_x\big)\}.
--   $$
--   A vertex of degree less than $3$ is never in $D$. Then $D \subseteq U \cup W$ for $U = \partial^-S_0$, $W = \partial^+S_0$.
--
--   **Formalization Note** Since $N(v)$ has three elements, the minimum (maximum) condition is written as a condition on every neighbor.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 8.1, p.46 (PDF p.48)

import Mathlib

namespace GaussianSweep

/-- The set `D` of Section 8.1 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 8.1, p.46 (PDF p.48)): the vertices `v` of degree 3
all of whose neighbors lie on the other side of zero, i.e. `d(v) = 3` and either
`y_v ≤ 0 < min_{x ∈ N(v)} y_x` or `y_v > 0 ≥ max_{x ∈ N(v)} y_x`.

**Formalization Note** For a vertex of degree 3 the neighborhood is nonempty, so the minimum
(maximum) condition is the stated `∀`-condition over the neighbors. -/
noncomputable def switchD {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → ℝ) : Finset V :=
  by classical exact Finset.univ.filter fun v => G.degree v = 3 ∧
    ((y v ≤ 0 ∧ ∀ x, G.Adj v x → 0 < y x) ∨ (0 < y v ∧ ∀ x, G.Adj v x → y x ≤ 0))

end GaussianSweep


