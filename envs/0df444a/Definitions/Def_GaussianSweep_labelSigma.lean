-- Prove2me | Definitions.Def_GaussianSweep_labelSigma
-- name    : GaussianSweep_labelSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:13.72766+00:00
-- url     : https://prove2.me/theorems/f00805f8-8d3a-4d41-bd9f-8c0bcd8b8ca4
-- title:
--   Label normalization $\sigma_v$
-- statement:
--   For arc lengths $\ell$ and a radius $\hat R$, put
--   $$
--   \sigma_v = \Big(\sum_{w \in B(v)} e^{-2D(v,w)}\Big)^{1/2}.
--   $$
--   For independent standard normal $Z_w$ this is the standard deviation of $X_v = \sum_{w \in B(v)} e^{-D(v,w)} Z_w$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_GaussianSweep_dirDist
import Definitions.Def_GaussianSweep_labelBall

namespace GaussianSweep

/-- The normalization `σ_v = (∑_{w ∈ B(v)} e^{−2D(v,w)})^{1/2}` of Definition 5.2 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac),
Definition 5.2, p.28 (PDF p.30)).

**Formalization Note** The sum runs over `B(v)` only, where `D(v, w) ≤ R̂ < ∞`, so `toReal` of
the directed distance is its true value. -/
noncomputable def labelSigma {V : Type*} [Fintype V] (G : SimpleGraph V) (len : V → V → ℝ)
    (Rhat : ℝ) (v : V) : ℝ :=
  Real.sqrt (∑ w ∈ labelBall G len Rhat v, Real.exp (-2 * (dirDist G len v w).toReal))

end GaussianSweep


