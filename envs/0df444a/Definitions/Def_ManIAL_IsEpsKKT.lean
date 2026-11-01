-- Prove2me | Definitions.Def_ManIAL_IsEpsKKT
-- name    : ManIAL_IsEpsKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:18.712986+00:00
-- url     : https://prove2.me/theorems/bc24c0b9-941b-41fa-9f03-8655eca9241b
-- title:
--   $\epsilon$-KKT point pair (Definition 3.1)
-- statement:
--   For problem (1.1), $\min_{x\in\mathcal M} f(x)+h(\mathcal Ax)$, a triple $(x,y,z)$ with $x\in\mathcal M$ and $y,z\in\mathbb R^m$ is an **$\epsilon$-KKT point pair** if
--
--   $$
--   \|P_{T_x\mathcal M}(\nabla f(x)-\mathcal A^*z)\|\le\epsilon,\qquad \operatorname{dist}(-z,\partial h(y))\le\epsilon,\qquad \|\mathcal Ax-y\|\le\epsilon .
--   $$
--
--   These are the three KKT conditions (3.3) of the split problem $\min f(x)+h(y)$ s.t. $\mathcal Ax=y$, each relaxed to tolerance $\epsilon$; $x$ is then called an $\epsilon$-stationary point. This is the accuracy notion in which all complexity results of the mission are stated.
--
--   **Formalization Note** $\mathcal A^*$ is the adjoint of the linear map $\mathcal A$. The condition $\operatorname{dist}(-z,\partial h(y))\le\epsilon$ is written as: some $g\in\partial h(y)$ has $\|z+g\|\le\epsilon$. For a real-valued convex $h$ the set $\partial h(y)$ is nonempty and compact, so the distance is attained and the two forms agree. $\partial h(y)$ is the published convex subdifferential `KallMayerSLP.KKT.subdifferential`, $\{g:\langle g,y'-y\rangle\le h(y')-h(y)\ \forall y'\}$.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Definition 3.1, display (3.4), p.7

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_KallMayerSLP_KKT_subdifferential

open ProjLikeRetr.Retractor

namespace ManIAL

/-- ϵ-KKT point pair, Definition 3.1 (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, display (3.4), p.7)
for problem (1.1) `min_{x ∈ M} f(x) + h(Ax)`: `x ∈ M` and
`‖P_{T_xM}(∇f(x) − A*z)‖ ≤ ϵ`, `dist(−z, ∂h(y)) ≤ ϵ`, `‖Ax − y‖ ≤ ϵ`.

**Formalization Note.** `P_{T_xM}` is the orthogonal projection onto `tangentSpace M x` and
`A*` is `ContinuousLinearMap.adjoint A`. `dist(−z, ∂h(y)) ≤ ϵ` is written
`∃ g ∈ ∂h(y), ‖z + g‖ ≤ ϵ` (the distance from `−z` to `g` is `‖z + g‖`). Here `∂h(y)` is the
published `KallMayerSLP.KKT.subdifferential`, the full convex subdifferential; for a real-valued
convex `h` on `ℝᵐ` it is nonempty and compact, so the distance is attained. The existential form
also avoids Lean's `Metric.infDist _ ∅ = 0`. -/
def IsEpsKKT {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y z : EuclideanSpace ℝ (Fin m)) : Prop :=
  x ∈ M ∧
    ‖(tangentSpace M x).starProjection (gradient f x - ContinuousLinearMap.adjoint A z)‖ ≤ ε ∧
    (∃ g ∈ KallMayerSLP.KKT.subdifferential h y, ‖z + g‖ ≤ ε) ∧
    ‖A x - y‖ ≤ ε

end ManIAL


