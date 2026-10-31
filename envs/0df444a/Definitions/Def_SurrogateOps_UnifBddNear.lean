-- Prove2me | Definitions.Def_SurrogateOps_UnifBddNear
-- name    : SurrogateOps_UnifBddNear
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:01.952576+00:00
-- url     : https://prove2.me/theorems/45b30901-cc1c-4f04-8be9-4f97d704d523
-- title:
--   Definition 3, pp.3–4 — a class of models uniformly bounded near $x_0$
-- statement:
--   A class of real-valued models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ on $E$ is uniformly bounded near $x_0$ if there is a scalar $M\ge0$ such that
--
--   $$
--   |\tilde f_\Delta(x)|\le M\qquad\text{for all }\Delta\in(0,\bar\Delta]\text{ and all }x\in B_\Delta(x_0).
--   $$
--
--   Here $B_\Delta(x_0)$ is the closed ball whose radius is the model's own index. The bound is the same for every model of the class.
--
--   **Formalization Note** The page states this for a class of models of $f\in C^0$; the condition does not involve $f$, so $f$ is not an argument. Corollary 5 applies it to the classes $\{\|\nabla\tilde f_\Delta\|\}$ and $\{\|\nabla^2\tilde f_\Delta\|\}$.
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Definition 3, pp.3–4

import Mathlib

namespace SurrogateOps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A class of models `{f̃_Δ}_{(0,Δ̄]}` is uniformly bounded near `x0`: the bound holds on the closed
ball `B_Δ(x0)` whose radius is the model's own index `Δ`.
Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Definition 3, pp.3–4.

**Formalization Note.** The page states Definition 3 for a real-valued class; `Corollary 5` applies
it to `{‖∇f̃_Δ‖}` and `{‖∇²f̃_Δ‖}`, so the Lean definition takes any class `fm : ℝ → E → ℝ`, and the
corollaries pass `fun Δ x => ‖fderiv ℝ (fm Δ) x‖` and its Hessian analogue. -/
def UnifBddNear (fm : ℝ → E → ℝ) (x0 : E) (Δbar : ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |fm Δ x| ≤ M

end SurrogateOps


