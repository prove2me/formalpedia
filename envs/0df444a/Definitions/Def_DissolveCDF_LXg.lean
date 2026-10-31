-- Prove2me | Definitions.Def_DissolveCDF_LXg
-- name    : DissolveCDF_LXg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:18.247811+00:00
-- url     : https://prove2.me/theorems/613addf1-05a1-429a-9fa5-67a68c6b86a3
-- title:
--   §2.3 — $L_{x,g}$, the Lipschitz constant of $\nabla g$ on $\Theta_x$
-- statement:
--   For $x\in\mathcal M$, with $g(y):=f(\mathcal A(y))$,
--
--   $$
--   L_{x,g}:=\sup_{y,z\in\Theta_x,\ y\ne z}\frac{\|\nabla g(y)-\nabla g(z)\|}{\|y-z\|}.
--   $$
--
--   Here $\Theta_x=\{y:\|y-x\|\le\rho_x\}$. Under Assumptions 1.1 and 1.2 the supremum is finite, because a locally Lipschitz map is Lipschitz on the compact ball $\Theta_x$.
--
--   **Formalization Note** The supremum is Lean's `sSup` over the difference quotients of pairs $y\neq z$ in $\Theta_x$; it agrees with the true supremum because the set is bounded (a consequence of the assumptions, not an added hypothesis). If $\Theta_x$ has no two distinct points the value is $0$.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7 (g := f∘A from §2.1, p.5)

import Mathlib
import Definitions.Def_DissolveCDF_rhoX

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): `L_{x,g} := sup_{y,z∈Θ_x, y≠z} ‖∇g(y) − ∇g(z)‖ / ‖y − z‖`, where
`g(y) := f(A(y))` (§2.1, p.5).

**Formalization Note** `Θ_x` is `Metric.closedBall x (rhoX c x)`. The supremum of the
difference quotients over pairs `y ≠ z` in `Θ_x` is Lean's `sSup`; the set is bounded because a
locally Lipschitz map is Lipschitz on the compact ball `Θ_x` (Assumptions 1.1 and 1.2). If `Θ_x`
has no two distinct points the set is empty and the value is `0`. -/
noncomputable def LXg {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {r : ℝ | ∃ y ∈ Metric.closedBall x (rhoX c x), ∃ z ∈ Metric.closedBall x (rhoX c x), y ≠ z ∧
    r = ‖gradient (fun w => f (A w)) y - gradient (fun w => f (A w)) z‖ / ‖y - z‖}

end DissolveCDF


