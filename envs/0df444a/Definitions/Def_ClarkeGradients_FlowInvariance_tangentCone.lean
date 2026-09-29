-- Prove2me | Definitions.Def_ClarkeGradients_FlowInvariance_tangentCone
-- name    : ClarkeGradients_FlowInvariance_tangentCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:38:10.976645+00:00
-- url     : https://prove2.me/theorems/d44bc395-dcda-4adb-8f16-ae9e657685b0
-- title:
--   Definition (3.6) — the Clarke tangent cone T_E(e)
-- statement:
--   Let $E\subseteq\mathbb R^n$ and $e\in\mathbb R^n$. The **tangent cone** to $E$ at $e$ is the cone dual to the normal cone $N_E(e)$ of Definition (3.1):
--
--   $$
--   T_E(e)=\{\zeta\in\mathbb R^n:\ \zeta\cdot v\le 0\ \text{for all } v\in N_E(e)\}.
--   $$
--
--   A vector $v$ is **tangent** to $E$ at $e$ if $v\in T_E(e)$, and a set of vectors is tangent if each of its elements is. $T_E(e)$ is always a closed convex cone. Theorem (4.4) shows it is exactly the notion of tangency that characterizes the sets invariant under a Lipschitz differential inclusion.
--
--   **Formalization Note** This is the Clarke tangent cone, defined through the Clarke normal cone. It is *not* Mathlib's `tangentConeAt`, which is the Bouligand (contingent) cone: the two differ, for instance, at the corner of a non-convex set, and substituting one for the other changes Theorem (4.4). The definition is total; the hypotheses "$E$ closed and nonempty, $e\in E$" are carried by the theorems.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 256, Definition (3.6)

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Definition (3.6): the (Clarke) *tangent cone* `T_E(e)` to `E` at `e` is the
cone dual to `N_E(e)`: `T_E(e) = {ζ : ζ · v ≤ 0 for all v in N_E(e)}`.
This is not Mathlib's `tangentConeAt` (the Bouligand/contingent cone). -/
def tangentCone {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) (e : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {ζ | ∀ v ∈ normalCone E e, inner ℝ ζ v ≤ 0}

end ClarkeGradients.FlowInvariance


