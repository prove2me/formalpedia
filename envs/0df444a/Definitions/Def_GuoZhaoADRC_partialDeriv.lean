-- Prove2me | Definitions.Def_GuoZhaoADRC_partialDeriv
-- name    : GuoZhaoADRC_partialDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:04.802345+00:00
-- url     : https://prove2.me/theorems/603e5123-56b3-4b8d-98e7-b1a7378987d9
-- title:
--   Partial derivative $\partial V/\partial y_j(y)$ on a Euclidean space
-- statement:
--   For a function $V:\mathbb R^k\to\mathbb R$ and a coordinate $j$, this is the partial derivative
--
--   $$\frac{\partial V}{\partial y_j}(y)=DV(y)\,e_j,$$
--
--   the Fréchet derivative of $V$ at $y$ applied to the $j$-th unit vector. It is the partial derivative appearing in Assumptions A2 (2)–(3) and A3 (2)–(3).
--
--   **Formalization Note** It is only used for functions that A2 and A3 assume continuously differentiable, where it is the classical partial derivative.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, Assumption A2 (2)–(3), p.1729; Assumption A3 (2)–(3), p.1730

import Mathlib

namespace GuoZhaoADRC

/-- **The partial derivative `∂V/∂y_j (y)` of a function on a Euclidean space.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), Assumptions A2 (2)–(3), p.1729, and A3 (2)–(3),
p.1730.

**Formalization Note.** The Fréchet derivative of `V` at `y` applied to the `j`-th unit vector.
It is only used for functions assumed continuously differentiable (A2, A3), where it is the
classical partial derivative. -/
noncomputable def partialDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : EuclideanSpace ℝ ι → ℝ) (j : ι) (y : EuclideanSpace ℝ ι) : ℝ :=
  fderiv ℝ V y (EuclideanSpace.single j 1)

end GuoZhaoADRC


