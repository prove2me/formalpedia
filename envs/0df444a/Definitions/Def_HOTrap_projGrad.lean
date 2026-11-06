-- Prove2me | Definitions.Def_HOTrap_projGrad
-- name    : HOTrap_projGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:53.538071+00:00
-- url     : https://prove2.me/theorems/fb10a051-8525-40e5-b8fe-1d07143021d8
-- title:
--   Projected-gradient mapping $G_\gamma$
-- statement:
--   For a stepsize $\gamma>0$, the projected-gradient mapping is
--   $$
--   G_\gamma(x):=\frac1\gamma\Big(x-\mathrm{proj}_{[0,1]^d}\big(x-\gamma\nabla f(x)\big)\Big).
--   $$
--
--   A point $x\in[0,1]^d$ is an $\varepsilon$-KKT point with respect to $\gamma$ if $\|G_\gamma(x)\|_2\le\varepsilon$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §2, p.13

import Mathlib
import Definitions.Def_HOTrap_boxProj

namespace HOTrap

/-- **The projected-gradient mapping** `G_γ(x) := (1/γ)(x − proj_{[0,1]^d}(x − γ∇f(x)))`.
Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, §2, p.13.

**Formalization Note** `∇f` is Mathlib's `gradient f`, which is the true gradient wherever `f` is
differentiable. -/
noncomputable def projGrad {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (γ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  γ⁻¹ • (x - boxProj (x - γ • gradient f x))

end HOTrap


