-- Prove2me | Definitions.Def_NAPPAL_VPEB_augLag
-- name    : NAPPAL_VPEB_augLag
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:07:54.818685+00:00
-- url     : https://prove2.me/theorems/c1a3586d-428e-4cae-9384-b59ccf2abc9e
-- title:
--   Augmented Lagrangian $\mathcal L_\gamma(u,v,p)$
-- statement:
--   For an instance of (P) and $\gamma \in \mathbb{R}$, the **augmented Lagrangian** is
--   $$\mathcal L_\gamma(u,v,p) = F(u,v) + \langle p, \Theta(u) + Bv \rangle + \frac{\gamma}{2}\|\Theta(u) + Bv\|^2 \in (-\infty, +\infty].$$
--   Its values along the iterates drive the convergence analysis (Lemma 4.2 and the potential $\Lambda^k$).
--
--   **Formalization Note** The three arguments are separate so that mixed points such as $(u^{k+1}, v^{k+1}, p^k)$ can be written. The version with the constraint $u \in U$ built in is $\tilde{\mathcal L}_\gamma$.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §2, p. 6

import Mathlib
import Definitions.Def_NAPPAL_VPEB_UV
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Problem_Theta

open scoped InnerProductSpace Topology

namespace NAPPAL.VPEB

/-- **The augmented Lagrangian `L_γ(u, v, p)`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §2, p. 6: "the augmented Lagrangian function of (P) is defined as
Lγ(w) = F(u, v) + ⟨p, Θ(u) + Bv⟩ + (γ/2)‖Θ(u) + Bv‖²", with "w = (u, v, p)".

`augLag P γ u v p = J(u) + (G(u, v) + H(v) + ⟨p, Θ(u) + Bv⟩ + (γ/2)‖Θ(u) + Bv‖²)`, a value in
`(−∞, +∞]`.

**Formalization Note.** The three arguments are separate so that the mixed points
`(u^{k+1}, v^{k+1}, p^k)` of Lemma 4.2 can be written directly. The function with the
constraint `u ∈ U` built in, whose subdifferential the paper writes `∂L_γ`, is `Ltil`. -/
noncomputable def augLag {n d m : ℕ} (P : Problem n d m) (γ : ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin d))
    (p : EuclideanSpace ℝ (Fin m)) : EReal :=
  P.J u + ((P.G (WithLp.toLp 2 (u, v)) + P.H v + ⟪p, P.Theta u + P.B v⟫_ℝ +
    γ / 2 * ‖P.Theta u + P.B v‖ ^ 2 : ℝ) : EReal)

end NAPPAL.VPEB


