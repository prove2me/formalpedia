-- Prove2me | Definitions.Def_GaussianSweep_labelBall
-- name    : GaussianSweep_labelBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:12.662093+00:00
-- url     : https://prove2.me/theorems/514b65ee-4874-403a-b3ce-7afbe8a07b24
-- title:
--   Label ball $B(v) = \{w : D(v,w) \le \hat R\}$
-- statement:
--   For arc lengths $\ell$ and a radius $\hat R > 0$, the label ball of a vertex $v$ is
--   $$
--   B(v) = \{w \in V(G) : D(v, w) \le \hat R\},
--   $$
--   where $D$ is the directed distance. It is the set of vertices whose variables enter the label of $v$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_GaussianSweep_dirDist

namespace GaussianSweep

/-- The label ball `B(v) = {w : D(v, w) ≤ R̂}` of Definition 5.2 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2, p.28
(PDF p.30)). -/
noncomputable def labelBall {V : Type*} [Fintype V] (G : SimpleGraph V) (len : V → V → ℝ)
    (Rhat : ℝ) (v : V) : Finset V :=
  by classical exact Finset.univ.filter fun w => dirDist G len v w ≤ ENNReal.ofReal Rhat

end GaussianSweep


