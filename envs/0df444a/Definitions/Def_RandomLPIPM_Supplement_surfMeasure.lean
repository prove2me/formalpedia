-- Prove2me | Definitions.Def_RandomLPIPM_Supplement_surfMeasure
-- name    : RandomLPIPM_Supplement_surfMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:50:14.931204+00:00
-- url     : https://prove2.me/theorems/9b2b7b23-de4a-4684-bdff-7cac8200528a
-- title:
--   The surface measure $\sigma_\mu$ on $M_\mu$
-- statement:
--   The surface $M_\mu\subseteq\mathbb R^n$ is a smooth hypersurface (the gradient $\nabla H(x)=D_x\mathbf 1-\mathbf 1$, $D_x=\mu X^{-2}$, does not vanish on it). Its metric is the restriction of the Euclidean inner product, and $\sigma_\mu$ denotes the induced $(n-1)$-dimensional volume (surface measure) on $M_\mu$, viewed as a measure on $\mathbb R^n$ concentrated on $M_\mu$.
--
--   It is the reference measure for the density of the central point $x_\mu(A)$ of a Gaussian LP in Theorem 7.7.
--
--   **Formalization Note** $\sigma_\mu$ is the $(n-1)$-dimensional Hausdorff measure of Euclidean $\mathbb R^n$ restricted to $M_\mu$. Mathlib's Hausdorff measure is not normalised, so on a smooth hypersurface it is a constant multiple (depending only on $n$) of the Riemannian surface volume; every statement that uses it takes the density existentially, so the constant is absorbed.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §7.1, p.60 ("σ_µ denotes the induced (n−1)-dimensional volume (surface measure) on M_µ")

import Mathlib
import Definitions.Def_RandomLPIPM_Supplement_centralSurface

open MeasureTheory

namespace RandomLPIPM.Supplement

/-- **The surface measure `σ_μ` on `M_μ`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §7.1 p.60: "The metric is the restriction of the
Euclidean inner product of `ℝⁿ`, so lengths and volumes on `M_μ` are the ordinary Euclidean ones,
and `σ_μ` denotes the induced `(n − 1)`-dimensional volume (surface measure) on `M_μ`."

**Formalization Note.** `σ_μ` is the `(n − 1)`-dimensional Hausdorff measure of Euclidean `ℝⁿ`
(`EuclideanSpace ℝ (Fin n)`, not the sup metric of `Fin n → ℝ`) restricted to `M_μ`. On the smooth
hypersurface `M_μ` (`∇H ≠ 0` there, p.60) Mathlib's unnormalised Hausdorff measure is a constant
multiple (depending only on `n`) of the Riemannian surface volume; every statement that uses
`surfMeasure` takes its density existentially, so this constant is absorbed. -/
noncomputable def surfMeasure (n : ℕ) (μ : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (Measure.hausdorffMeasure ((n : ℝ) - 1)).restrict (centralSurface n μ)

end RandomLPIPM.Supplement


