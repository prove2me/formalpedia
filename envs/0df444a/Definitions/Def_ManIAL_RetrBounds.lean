-- Prove2me | Definitions.Def_ManIAL_RetrBounds
-- name    : ManIAL_RetrBounds
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:07.210277+00:00
-- url     : https://prove2.me/theorems/61a50852-8d62-42de-af20-dc04b37bd973
-- title:
--   Retraction bounds (2.1): $\|R_x(u)-x\|\le\alpha\|u\|$, $\|R_x(u)-x-u\|\le\beta\|u\|^2$
-- statement:
--   Let $\mathcal M\subseteq\mathbb R^n$ and, for $x\in\mathcal M$, let $T_x\mathcal M$ be its tangent space at $x$. A map $R$, with $R_x(u):=R(x,u)$, satisfies the **retraction bounds** with constants $\alpha,\beta$ if for every $x\in\mathcal M$ and every $u\in T_x\mathcal M$
--
--   $$
--   R_x(u)\in\mathcal M,\qquad \|R_x(u)-x\|\le\alpha\|u\|,\qquad \|R_x(u)-x-u\|\le\beta\|u\|^2 .
--   $$
--
--   These are the inequalities (2.1) of Proposition 2.2, which every retraction on a compact submanifold satisfies for some $\alpha,\beta>0$. The whole analysis of ManIAL in §3 uses the manifold and the retraction only through compactness of $\mathcal M$ and these bounds, so the mission's statements are made for every pair $(\mathcal M,R)$ satisfying them.
--
--   **Formalization Note** $T_x\mathcal M$ is the linear span of the tangent cone of $\mathcal M$ at $x$ (the published `ProjLikeRetr.Retractor.tangentSpace`), which is the tangent space for an embedded submanifold. Only the values of $R$ on tangent vectors are constrained.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Proposition 2.2, display (2.1), p.5

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

open ProjLikeRetr.Retractor

namespace ManIAL

/-- The retraction bounds (2.1) of Proposition 2.2 (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.5):
for every `x ∈ M` and every tangent vector `u ∈ T_xM`, the point `R_x(u)` lies on `M` and
`‖R_x(u) − x‖ ≤ α‖u‖`, `‖R_x(u) − x − u‖ ≤ β‖u‖²`.

**Formalization Note.** `M ⊆ ℝⁿ` is any set and `T_xM` is `tangentSpace M x`, the span of the
tangent cone of `M` at `x` (for an embedded submanifold, its tangent space). `R x u` stands for
`R_x(u)`; only its values on tangent vectors are constrained. The paper's setting (a smooth
retraction on a compact submanifold) satisfies this predicate for some `α, β > 0` by
Proposition 2.2 ([7, Appendix B]); the analysis of §3 uses the retraction only through it. -/
def RetrBounds {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) : Prop :=
  ∀ x ∈ M, ∀ u ∈ tangentSpace M x,
    R x u ∈ M ∧ ‖R x u - x‖ ≤ α * ‖u‖ ∧ ‖R x u - x - u‖ ≤ β * ‖u‖ ^ 2

end ManIAL


