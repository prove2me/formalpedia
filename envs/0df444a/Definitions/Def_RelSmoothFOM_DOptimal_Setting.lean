-- Prove2me | Definitions.Def_RelSmoothFOM_DOptimal_Setting
-- name    : RelSmoothFOM_DOptimal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:24.269318+00:00
-- url     : https://prove2.me/theorems/f59317aa-6509-4ec0-9acc-94751c82d3cb
-- title:
--   (7), (16), (39), Algorithm 1 — D-optimal design and the primal gradient run
-- statement:
--   Let $H$ be an $m\times n$ real matrix and $X=\operatorname{Diag}(x)$. The D-optimal design objective is $f(x)=-\log\det(HXH^\top)$, used where $HXH^\top$ is positive definite. The logarithmic reference function is $h(x)=-\sum_{j=1}^n\log x_j$, used for positive coordinates. The positive simplex is $\Delta_n^\circ=\{x:x_j>0\ (1\le j\le n),\ \sum_jx_j=1\}$.
--
--   The Bregman distance of a differentiable reference function is
--   $$D_h(y,x)=h(y)-h(x)-\nabla h(x)\cdot(y-x).$$
--   A primal gradient run starts in its feasible set $Q$ and at step $i$ chooses $x^{i+1}\in Q$ minimizing $f(x^i)+\nabla f(x^i)\cdot(u-x^i)+L D_h(u,x^i)$ over $u\in Q$.
--
--   These definitions fix the model and the algorithm used by all subsequent statements.
--
--   **Formalization Note** Derivatives are Fréchet derivatives. The total real logarithm is evaluated only on positive arguments in the theorems; the algorithm runs over the positive simplex, matching the page's positive subproblem minimizer.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), pp. 334, 337, 340–341, 349, (7), Algorithm 1, (16), (39)

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.DOptimal

/-- The relative interior of the probability simplex. -/
def posSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∑ j, x j = 1}

/-- The objective of (16), evaluated only where its determinant is positive. -/
noncomputable def dOptObj {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  -Real.log (H * Matrix.diagonal x * H.transpose).det

/-- The logarithmic reference function (39), used on the positive orthant. -/
noncomputable def logBarrier {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  -∑ j, Real.log (x j)

end RelSmoothFOM.DOptimal


