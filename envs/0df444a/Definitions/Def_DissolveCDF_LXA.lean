-- Prove2me | Definitions.Def_DissolveCDF_LXA
-- name    : DissolveCDF_LXA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:55.639264+00:00
-- url     : https://prove2.me/theorems/e61ec89e-9850-40cc-9760-9e9fc24dea74
-- title:
--   §2.3 — $L_{x,A}$, the Lipschitz constant of $J_{\mathcal A}$ on $\Theta_x$
-- statement:
--   For $x\in\mathcal M$,
--
--   $$
--   L_{x,A}:=\sup_{y,z\in\Theta_x,\ y\ne z}\frac{\|J_{\mathcal A}(y)-J_{\mathcal A}(z)\|}{\|y-z\|}.
--   $$
--
--   Here $\Theta_x=\{y:\|y-x\|\le\rho_x\}$. Under Assumptions 1.1 and 1.2 the supremum is finite, because a locally Lipschitz map is Lipschitz on the compact ball $\Theta_x$.
--
--   **Formalization Note** The supremum is Lean's `sSup` over the difference quotients of pairs $y\neq z$ in $\Theta_x$; it agrees with the true supremum because the set is bounded (a consequence of the assumptions, not an added hypothesis). If $\Theta_x$ has no two distinct points the value is $0$.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7

import Mathlib
import Definitions.Def_DissolveCDF_transJac
import Definitions.Def_DissolveCDF_rhoX

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): `L_{x,A} := sup_{y,z∈Θ_x, y≠z} ‖J_A(y) − J_A(z)‖ / ‖y − z‖`.

**Formalization Note** `Θ_x` is `Metric.closedBall x (rhoX c x)`. The supremum of the
difference quotients over pairs `y ≠ z` in `Θ_x` is Lean's `sSup`; the set is bounded because a
locally Lipschitz map is Lipschitz on the compact ball `Θ_x` (Assumptions 1.1 and 1.2). If `Θ_x`
has no two distinct points the set is empty and the value is `0`. -/
noncomputable def LXA {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {r : ℝ | ∃ y ∈ Metric.closedBall x (rhoX c x), ∃ z ∈ Metric.closedBall x (rhoX c x), y ≠ z ∧
    r = ‖transJac A y - transJac A z‖ / ‖y - z‖}

end DissolveCDF


