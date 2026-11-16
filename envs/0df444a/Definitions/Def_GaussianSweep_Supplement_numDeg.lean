-- Prove2me | Definitions.Def_GaussianSweep_Supplement_numDeg
-- name    : GaussianSweep_Supplement_numDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:37:30.40145+00:00
-- url     : https://prove2.me/theorems/0e5c1143-6119-4670-b364-61a7e38185d5
-- title:
--   Degree counts $n_d(G)$
-- statement:
--   For a finite graph $G$ and $d \in \mathbb N$, $n_d(G)$ is the number of vertices of $G$ of degree exactly $d$. The per-degree pathwidth bounds are linear combinations $\sum_d a_d n_d$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 1.1, p.1 (PDF p.3); Section 7, p.38 (PDF p.40)

import Mathlib

namespace GaussianSweep.Supplement

/-- `n_d(G)`, the number of vertices of `G` of degree (exactly) `d`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 1.1, p.1 (PDF p.3); Section 7, p.38 (PDF p.40)). -/
def numDeg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = d).card

end GaussianSweep.Supplement


