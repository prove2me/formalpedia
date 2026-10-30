-- Prove2me | Definitions.Def_NAPPAL_VPEB_Problem_F
-- name    : NAPPAL_VPEB_Problem_F
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:05:26.176075+00:00
-- url     : https://prove2.me/theorems/b90911de-bb0f-4b28-930c-c89973367abe
-- title:
--   The objective $F(u,v) = G(u,v) + J(u) + H(v)$
-- statement:
--   For an instance of (P), the **objective** is
--   $$F(u,v) = G(u,v) + J(u) + H(v) \in (-\infty, +\infty], \qquad u \in \mathbb{R}^n,\ v \in \mathbb{R}^d .$$
--   It is $+\infty$ exactly when $J(u) = +\infty$. Assumption (H7) asks it to be bounded below and coercive on the feasible set, and the bound (27) compares the potential $\Lambda^k$ with it.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §1.1, p. 2

import Mathlib
import Definitions.Def_NAPPAL_VPEB_UV
import Definitions.Def_NAPPAL_VPEB_Problem

namespace NAPPAL.VPEB

/-- **The objective `F(u, v) = G(u, v) + J(u) + H(v)` of (P).**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §1.1, p. 2: "let us denote the overall objective to be F(u, v) := G(u, v) + J(u) + H(v)".

`P.F u v = J(u) + (G(u, v) + H(v))` in `(−∞, +∞]`.

**Formalization Note.** The value is `+∞` exactly when `J(u) = +∞` (`G`, `H` are real-valued). -/
noncomputable def Problem.F {n d m : ℕ} (P : Problem n d m) (u : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin d)) : EReal :=
  P.J u + ((P.G (WithLp.toLp 2 (u, v)) + P.H v : ℝ) : EReal)

end NAPPAL.VPEB


