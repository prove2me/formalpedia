-- Prove2me | Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature
-- name    : ExpConeIPM_Curvature_NegativeCurvature
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:42.944843+00:00
-- url     : https://prove2.me/theorems/55d87c77-1186-4f0e-b5f7-bdd98de6a23c
-- title:
--   Third directional derivative $F'''(x)[u]$ and negative curvature of a barrier
-- statement:
--   Let $F : \mathbb{R}^n \to \mathbb{R}$ and let $F''(x)$ be its Hessian, viewed as a linear map of $\mathbb{R}^n$. The **third directional derivative** of $F$ at $x$ in the direction $u$ is the symmetric linear map
--
--   $$
--   F'''(x)[u] = \frac{d}{dt} F''(x + tu)\Big|_{t=0},
--   $$
--
--   and $F'''(x)[u, v, v] = \langle F'''(x)[u]\, v, v\rangle$.
--
--   Let $K \subseteq \mathbb{R}^n$ be a cone. A barrier $F$ of $K$ is said to have **negative curvature** if for all $x \in \operatorname{int}(K)$ and for $u \in K$
--
--   $$
--   F'''(x)[u] \preceq 0,
--   $$
--
--   that is, $\langle F'''(x)[u]\, v, v\rangle \le 0$ for every $v \in \mathbb{R}^n$ (negative semidefiniteness in the Loewner order). The direction $u$ ranges over the closed cone $K$ itself.
--
--   Barriers of symmetric cones have negative curvature, and a barrier is self-scaled if and only if it and its conjugate both have negative curvature (Nesterov–Tunçel). The notion separates the cones on which the Nesterov–Todd theory of scaling points applies from the nonsymmetric ones.
--
--   **Formalization Note** $F''$ is `SelfScaledIPM.ShortStep.hess F`, the derivative of the gradient (published definition), and $F'''(x)[u]$ is `fderiv ℝ (hess F) x u`, a continuous linear map of `EuclideanSpace ℝ (Fin n)`. The Loewner order is stated through the quadratic form, for all $v$.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 356 (definition of negative curvature) and p. 368, A.3 (definition of F'''(x)[u])

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

/-!
# Negative curvature of a barrier (Dahl–Andersen 2022, §5, p. 356)

Dahl, Andersen, *A primal-dual interior-point algorithm for nonsymmetric exponential-cone
optimization*, Math. Program. 194 (2022), p. 356 (the definition) and p. 368, A.3 (the meaning of
`F'''(x)[u]`).

`F'''(x)[u] = d/dt F''(x + tu)|_{t=0}` (A.3, p. 368) is the derivative at `x`, in the direction `u`,
of the Hessian map `x ↦ F''(x)` (`SelfScaledIPM.ShortStep.hess`, the derivative of the gradient). It
is a linear map `ℝⁿ → ℝⁿ`; its quadratic form `⟪F'''(x)[u] v, v⟫` is the trilinear form
`F'''(x)[u, v, v]`. The Loewner relation `F'''(x)[u] ⪯ 0` (negative semidefinite) is stated through
this quadratic form, for every `v`.
-/

/-- The third directional derivative `F'''(x)[u] = d/dt F''(x + tu)|_{t=0}` (A.3, p. 368): the
derivative at `x` of the Hessian map `hess F`, applied to the direction `u`. -/
noncomputable def thirdDeriv {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (SelfScaledIPM.ShortStep.hess F) x u

/-- **Negative curvature** (§5, p. 356): a barrier `F` of the cone `K` has negative curvature if
for all `x ∈ int(K)` and for `u ∈ K`, `F'''(x)[u] ⪯ 0`, i.e. `⟪F'''(x)[u] v, v⟫ ≤ 0` for every `v`.
The direction `u` ranges over the closed cone `K` (not over `ℝⁿ`, not over `int K`). -/
def HasNegativeCurvature {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ interior K, ∀ u ∈ K, ∀ v : EuclideanSpace ℝ (Fin n), ⟪thirdDeriv F x u v, v⟫_ℝ ≤ 0

end ExpConeIPM.Curvature


