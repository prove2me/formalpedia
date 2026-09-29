-- Prove2me | Definitions.Def_ClarkeGradients_FlowInvariance_IsLipschitzMultifunction
-- name    : ClarkeGradients_FlowInvariance_IsLipschitzMultifunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:39:32.033819+00:00
-- url     : https://prove2.me/theorems/439e3993-e4a1-4231-b004-26043e116362
-- title:
--   Definition (4.2) — Lipschitz multifunction
-- statement:
--   A multifunction $X$ from $\mathbb R^n$ to $\mathbb R^n$ is **Lipschitz** if there is a constant $K$ with the following property: given any $x_1,x_2\in\mathbb R^n$ and a point $v_1\in X(x_1)$, there exists $v_2\in X(x_2)$ such that
--
--   $$
--   |v_1-v_2|\le K\,|x_1-x_2|.
--   $$
--
--   For closed-valued $X$ this says that $X$ is Lipschitz in the Hausdorff metric on closed sets; if $X$ is single-valued it is the usual Lipschitz condition. It is the regularity hypothesis of Theorem (4.4).
--
--   **Formalization Note** $K$ is a real number and is not required to be nonnegative, as in the paper; when some value $X(x_1)$ is nonempty and $n\ge 1$, the condition with $x_1\ne x_2$ forces $K\ge 0$. The constant is global (one $K$ for all $x_1,x_2$), not local.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), pp. 259–260, Definition (4.2)

import Mathlib

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Definition (4.2): the multifunction `X` is *Lipschitz* if there is a constant
`K` such that, given any `x₁, x₂ ∈ ℝⁿ` and a point `v₁ ∈ X(x₁)`, there exists `v₂ ∈ X(x₂)` with
`|v₁ - v₂| ≤ K |x₁ - x₂|`. -/
def IsLipschitzMultifunction {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ K : ℝ, ∀ x₁ x₂ : EuclideanSpace ℝ (Fin n), ∀ v₁ ∈ X x₁, ∃ v₂ ∈ X x₂,
    ‖v₁ - v₂‖ ≤ K * ‖x₁ - x₂‖

end ClarkeGradients.FlowInvariance


