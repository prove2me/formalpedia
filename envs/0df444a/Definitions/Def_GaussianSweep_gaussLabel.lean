-- Prove2me | Definitions.Def_GaussianSweep_gaussLabel
-- name    : GaussianSweep_gaussLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:06.399202+00:00
-- url     : https://prove2.me/theorems/057918b3-5993-4b0b-bab7-7b2f6692a6d7
-- title:
--   Gaussian label $Y_v = X_v/\sigma_v$
-- statement:
--   Let $G$ be a graph, $(Z_w)_{w \in V(G)}$ independent $N(0,1)$ variables, $\ell$ positive arc lengths and $\hat R > 0$. The **Gaussian label** of a vertex $v$ is
--   $$
--   Y_v = \frac{X_v}{\sigma_v}, \qquad X_v = \sum_{w \in B(v)} e^{-D(v,w)} Z_w, \qquad \sigma_v^2 = \sum_{w \in B(v)} e^{-2D(v,w)},
--   $$
--   with $D$ the directed distance and $B(v) = \{w : D(v,w) \le \hat R\}$. Sorting the vertices by these labels gives the layouts from which all pathwidth bounds of the paper are built.
--
--   **Formalization Note** The variables $(Z_w)$ are the coordinates of a point $z : V \to \mathbb R$, so a label is a function of $z$; the statements use the product measure $\bigotimes_w N(0,1)$ on $V \to \mathbb R$. The coefficients $e^{-D(v,w)}$ appear only for $w \in B(v)$, where $D(v,w)$ is finite.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_GaussianSweep_dirDist
import Definitions.Def_GaussianSweep_labelBall
import Definitions.Def_GaussianSweep_labelSigma

namespace GaussianSweep

/-- The Gaussian label `Y_v = X_v / σ_v`, `X_v = ∑_{w ∈ B(v)} e^{−D(v,w)} Z_w`, of Definition 5.2
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2, p.28 (PDF p.30)), for arc lengths `len` and radius `R̂`.

**Formalization Note** The independent `N(0, 1)` variables `(Z_w)` are the coordinates of a point
`z : V → ℝ`; the label is a function of `z`, and statements about it use the product measure
`Measure.pi fun _ => gaussianReal 0 1` on `V → ℝ`. The coefficients `e^{−D}` occur only for
`w ∈ B(v)`, where `D` is finite. -/
noncomputable def gaussLabel {V : Type*} [Fintype V] (G : SimpleGraph V) (len : V → V → ℝ)
    (Rhat : ℝ) (v : V) (z : V → ℝ) : ℝ :=
  (∑ w ∈ labelBall G len Rhat v, Real.exp (-(dirDist G len v w).toReal) * z w) /
    labelSigma G len Rhat v

end GaussianSweep


