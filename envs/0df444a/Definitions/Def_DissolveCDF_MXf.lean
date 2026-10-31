-- Prove2me | Definitions.Def_DissolveCDF_MXf
-- name    : DissolveCDF_MXf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:55.293671+00:00
-- url     : https://prove2.me/theorems/0f63a778-13c8-40c6-99c8-0d06ea439416
-- title:
--   §2.3 — $M_{x,f}=\sup_{y\in\Theta_x}\|\nabla f(\mathcal A(y))\|$
-- statement:
--   For $x\in\mathcal M$,
--
--   $$
--   M_{x,f}:=\sup_{y\in\Theta_x}\|\nabla f(\mathcal A(y))\|,
--   $$
--
--   the largest size of the gradient of $f$ at the points $\mathcal A(y)$, $y\in\Theta_x$.
--
--   Here $\Theta_x=\{y:\|y-x\|\le\rho_x\}$. Under Assumptions 1.1 and 1.2 the supremum is finite (a continuous function on a compact ball).
--
--   **Formalization Note** The supremum is Lean's `sSup`, which agrees with the true supremum because the set is nonempty and bounded; boundedness follows from the assumptions and is not added as a hypothesis.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7

import Mathlib
import Definitions.Def_DissolveCDF_rhoX

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): `M_{x,f} := sup_{y∈Θ_x} ‖∇f(A(y))‖` (the gradient of `f` evaluated at
`A(y)`).

**Formalization Note** `Θ_x = {y : ‖y − x‖ ≤ ρ_x}` is `Metric.closedBall x (rhoX c x)`. The
supremum is Lean's `sSup`, which is the true supremum because the set is nonempty and bounded
under Assumptions 1.1 and 1.2 (a continuous function on a compact ball); this boundedness is a
consequence of the assumptions, not an extra hypothesis. -/
noncomputable def MXf {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => ‖gradient f (A y)‖) '' Metric.closedBall x (rhoX c x))

end DissolveCDF


