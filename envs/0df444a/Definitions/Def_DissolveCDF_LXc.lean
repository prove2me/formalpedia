-- Prove2me | Definitions.Def_DissolveCDF_LXc
-- name    : DissolveCDF_LXc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:09.581019+00:00
-- url     : https://prove2.me/theorems/faba4186-7c3e-4b99-931d-7d4832e8b36a
-- title:
--   §2.3 — $L_{x,c}$, the Lipschitz constant of $J_c$ on $\Theta_x$
-- statement:
--   For $x\in\mathcal M$,
--
--   $$
--   L_{x,c}:=\sup_{y,z\in\Theta_x,\ y\ne z}\frac{\|J_c(y)-J_c(z)\|}{\|y-z\|}.
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

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): `L_{x,c} := sup_{y,z∈Θ_x, y≠z} ‖J_c(y) − J_c(z)‖ / ‖y − z‖`.

**Formalization Note** `Θ_x` is `Metric.closedBall x (rhoX c x)`. The supremum of the
difference quotients over pairs `y ≠ z` in `Θ_x` is Lean's `sSup`; the set is bounded because a
locally Lipschitz map is Lipschitz on the compact ball `Θ_x` (Assumptions 1.1 and 1.2). If `Θ_x`
has no two distinct points the set is empty and the value is `0`. -/
noncomputable def LXc {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {r : ℝ | ∃ y ∈ Metric.closedBall x (rhoX c x), ∃ z ∈ Metric.closedBall x (rhoX c x), y ≠ z ∧
    r = ‖transJac c y - transJac c z‖ / ‖y - z‖}

end DissolveCDF


