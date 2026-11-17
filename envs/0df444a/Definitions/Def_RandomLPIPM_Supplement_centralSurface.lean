-- Prove2me | Definitions.Def_RandomLPIPM_Supplement_centralSurface
-- name    : RandomLPIPM_Supplement_centralSurface
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:49:39.804203+00:00
-- url     : https://prove2.me/theorems/6d46f3a6-2e7d-49df-9a6a-62f31bf50596
-- title:
--   The surface of possible central points $M_\mu=\{x>0:(x-\mathbf 1)^\top(\mu/x-\mathbf 1)=0\}$
-- statement:
--   Fix $\mu$ (in the paper $0<\mu<1$) and write
--   $$H(x)=(x-\mathbf 1)^\top\Big(\frac{\mu}{x}-\mathbf 1\Big)=\sum_{i=1}^n (x_i-1)\Big(\frac{\mu}{x_i}-1\Big),\qquad x\in\mathbb R^n_{>0},$$
--   with the quotient taken coordinatewise. The **surface of possible central points** is
--   $$M_\mu=\{x\in\mathbb R^n_{>0}: H(x)=0\}.$$
--
--   If $x$ is the $\mu$-central point of a subspace $W$ (so $x-\mathbf 1\in W$ and $s-\mathbf 1\in W^\perp$ with $s=\mu/x$), the two vectors are orthogonal, so every central point at parameter $\mu$ lies on $M_\mu$. It contains $\mathbf 1$ and $\mu\mathbf 1$; $M_\mu^\circ=M_\mu\setminus\{\mathbf 1,\mu\mathbf 1\}$.
--
--   **Formalization Note** $M_\mu$ is a subset of Euclidean space $\mathbb R^n$ with its Euclidean metric, on which the surface measure is built.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §7.1, p.60 (definition of H and M_μ)

import Mathlib

namespace RandomLPIPM.Supplement

/-- **The surface of possible central points `M_μ`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §7.1 p.60: for `0 < μ < 1`,
`H(x) = (x − 1)ᵀ(μ/x − 1)` and `M_μ = {x ∈ ℝⁿ_{>0} : H(x) = 0}`; every central point at parameter
`μ` lies on `M_μ` (because `x − 1 ∈ W` and `s − 1 ∈ W^⊥` are orthogonal, `s = μ/x`).

**Formalization Note.** `M_μ` is a subset of `EuclideanSpace ℝ (Fin n)` (the Euclidean metric, which
the surface measure `σ_μ` of `surfMeasure` needs); `WithLp.ofLp x i` is the `i`-th coordinate. The
quotient `μ / xᵢ` is only evaluated where `xᵢ > 0`. The paper fixes `0 < μ < 1`; the set is
defined for every `μ`, and the theorems that use it carry the hypothesis. -/
def centralSurface (n : ℕ) (μ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, 0 < WithLp.ofLp x i) ∧
    ∑ i, (WithLp.ofLp x i - 1) * (μ / WithLp.ofLp x i - 1) = 0}

end RandomLPIPM.Supplement


