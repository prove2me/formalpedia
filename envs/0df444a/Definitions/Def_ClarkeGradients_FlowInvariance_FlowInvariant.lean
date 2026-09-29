-- Prove2me | Definitions.Def_ClarkeGradients_FlowInvariance_FlowInvariant
-- name    : ClarkeGradients_FlowInvariance_FlowInvariant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:40:39.197454+00:00
-- url     : https://prove2.me/theorems/585ed976-3782-4ed3-8785-c319c8836612
-- title:
--   Definition (4.3) — flow-invariant set
-- statement:
--   Let $X$ be a multifunction from $\mathbb R^n$ to $\mathbb R^n$ and $F\subseteq\mathbb R^n$. The set $F$ is **flow-invariant** for $X$ if every trajectory (4.1) for $X$ with initial value in $F$ remains in $F$:
--
--   $$
--   x \text{ a trajectory for } X,\ x(0)\in F\ \Longrightarrow\ x(t)\in F\ \text{for all } t\in[0,1].
--   $$
--
--   Theorem (4.4) characterizes the closed flow-invariant sets of a Lipschitz multifunction by a tangency condition.
--
--   **Formalization Note** The paper defines flow-invariance for a closed set $F$ ("The closed subset $F$ of $R^n$ is flow-invariant for $X$ if …"); here the definition is stated for every $F$ and closedness is a hypothesis of every theorem that uses it. The paper's "$x(t)\in F$ for $t\ge 0$" means $t\in[0,1]$, since trajectories are defined on $[0,1]$.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 260, Definition (4.3)

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_IsTrajectory

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Definition (4.3): `F` is *flow-invariant* for `X` if every trajectory `x` for
`X` (in the sense of (4.1)) with `x(0) ∈ F` satisfies `x(t) ∈ F` for all `t ∈ [0, 1]`.
(The paper defines this for closed `F`; closedness is carried by the theorems.) -/
def FlowInvariant {n : ℕ} (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (F : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x : ℝ → EuclideanSpace ℝ (Fin n), IsTrajectory X x → x 0 ∈ F →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x t ∈ F

end ClarkeGradients.FlowInvariance


