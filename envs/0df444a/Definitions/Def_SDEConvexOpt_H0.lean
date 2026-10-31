-- Prove2me | Definitions.Def_SDEConvexOpt_H0
-- name    : SDEConvexOpt_H0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:58.025984+00:00
-- url     : https://prove2.me/theorems/becc211b-f34e-434b-b3bc-3a9cb6c04a14
-- title:
--   Standing assumptions (H0): $f$ convex, $C^1$ with $L$-Lipschitz gradient, $\operatorname{argmin} f\neq\emptyset$
-- statement:
--   The objective $f:\mathbb R^d\to\mathbb R$ of the minimization problem $\min_{x\in\mathbb R^d} f(x)$ satisfies (H0) with constant $L\ge0$ when
--
--   1. $f$ is continuously differentiable,
--   2. $f$ is convex,
--   3. $\nabla f$ is $L$-Lipschitz continuous: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$,
--   4. the solution set $\mathcal S=\operatorname{argmin}(f)$ is nonempty.
--
--   These are the standing assumptions on the potential of the gradient SDE studied throughout the paper.
--
--   **Formalization Note** $\mathbb R^d$ is `EthierKurtz.SDEState d`, $\nabla f$ is Mathlib's `gradient f`, and $L:\mathbb R_{\ge0}$, as for the class $C^{1,1}_L(\mathbb R^d)$ of p.6; $L=0$ is allowed.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (H0), p.1; class $C^{1,1}_L$, p.6

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SDEConvexOpt_argminSet

open scoped NNReal

namespace SDEConvexOpt

open EthierKurtz

/-- The standing assumptions (H0) on the objective `f : ℝ^d → ℝ`
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, (H0), p.1): `f` is continuously differentiable
and convex with `L`-Lipschitz continuous gradient, and `S = argmin(f) ≠ ∅`.

**Formalization Note** `ℝ^d` is `EthierKurtz.SDEState d = EuclideanSpace ℝ (Fin d)`; `∇f` is
Mathlib's `gradient f`. The Lipschitz constant is `L : ℝ≥0`, so `L ≥ 0` as for the class
`C^{1,1}_L(ℝ^d)` of p.6; `L = 0` is allowed. -/
def H0 {d : ℕ} (f : SDEState d → ℝ) (L : ℝ≥0) : Prop :=
  ContDiff ℝ 1 f ∧ ConvexOn ℝ Set.univ f ∧ LipschitzWith L (gradient f) ∧
    (argminSet f).Nonempty

end SDEConvexOpt


