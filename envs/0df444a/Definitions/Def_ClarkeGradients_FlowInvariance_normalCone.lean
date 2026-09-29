-- Prove2me | Definitions.Def_ClarkeGradients_FlowInvariance_normalCone
-- name    : ClarkeGradients_FlowInvariance_normalCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:37:25.183805+00:00
-- url     : https://prove2.me/theorems/480a17a6-f29c-4ac7-9416-8594dd4a9075
-- title:
--   Definition (3.1) — the Clarke cone of normals N_E(e)
-- statement:
--   Let $E\subseteq\mathbb R^n$ and $e\in\mathbb R^n$, and write $d_E(x)=\inf\{|x-e'|:e'\in E\}$ for the Euclidean distance from $x$ to $E$. The **cone of normals** to $E$ at $e$ is
--
--   $$
--   N_E(e)=\operatorname{cl}\,\{p\in\mathbb R^n:\ s\,p\in\partial d_E(e)\ \text{for some } s\in(0,\infty)\},
--   $$
--
--   where $\partial d_E(e)$ is the generalized gradient (1.1) of the distance function at $e$ and $\operatorname{cl}$ denotes closure. A vector $p$ is **normal** to $E$ at $e$ if $p\in N_E(e)$.
--
--   The paper uses this definition for $E$ closed and nonempty and $e\in E$; there $N_E(e)$ is a closed convex cone. For convex $E$ it coincides with the normal cone of convex analysis, and for a $C^1$ manifold with the usual normal space, but for general closed sets it is a new object. Its dual, the tangent cone (3.6), is what characterizes flow-invariance in Theorem (4.4).
--
--   **Formalization Note** $d_E$ is `Metric.infDist · E`. The definition is total; the hypotheses "$E$ closed and nonempty, $e\in E$" are carried by the theorems. For $E=\emptyset$, Mathlib's `infDist` is identically $0$, so the definition gives $N_\emptyset(e)=\{0\}$; this case never arises in the mission's theorems.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 254, Definition (3.1)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Definition (3.1): the *cone of normals* `N_E(e)` to `E` at `e` is the closure
of the set `{p ∈ ℝⁿ : s p ∈ ∂d_E(e) for some s ∈ (0, ∞)}`, where `d_E(x) = Metric.infDist x E`
is the Euclidean distance from `x` to `E` and `∂` is the generalized gradient (1.1).
(The paper uses it for `E` closed and nonempty and `e ∈ E`; those hypotheses are carried by the
theorems.) -/
def normalCone {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) (e : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  closure {p | ∃ s : ℝ, 0 < s ∧
    s • p ∈ Shared.generalizedGradient (fun y => Metric.infDist y E) e}

end ClarkeGradients.FlowInvariance


