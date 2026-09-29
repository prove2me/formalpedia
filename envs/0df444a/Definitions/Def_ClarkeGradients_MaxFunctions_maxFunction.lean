-- Prove2me | Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction
-- name    : ClarkeGradients_MaxFunctions_maxFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:41:35.174428+00:00
-- url     : https://prove2.me/theorems/f7f39cec-3915-49eb-81c1-a447ef7ce852
-- title:
--   The max function f(x) = max{g(x, u) : u ∈ U} and its maximizer set M(x)
-- statement:
--   Let $U$ be a set and $g:\mathbb R^n\times U\to\mathbb R$. The **max function** of $g$ is
--
--   $$
--   f(x)=\max\{g(x,u):u\in U\},
--   $$
--
--   and the **maximizer set** at $x$ is $M(x)=\{u\in U:\ g(x,u)=f(x)\}$.
--
--   These are the objects of Theorem (2.1). Under that theorem's hypotheses ($U$ nonempty and sequentially compact, $g$ upper semicontinuous and locally Lipschitz in $x$) the maximum is attained, so $M(x)$ is nonempty.
--
--   **Formalization Note** $g$ is curried, `g : ℝⁿ → U → ℝ`. The maximum is written as the supremum `⨆ u, g x u`; in Lean this is $0$ when the family is unbounded above or $U$ is empty, so the theorems carry the hypotheses ($U$ nonempty, (a), (b)) under which it is attained, and conclusion (3) of Theorem (2.1) is stated with `IsGreatest`, which asserts attainment.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 251, Theorem (2.1)

import Mathlib

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Theorem (2.1): the max function `f(x) = max {g(x, u) : u ∈ U}`, written as
the supremum `⨆ u, g x u` (under the hypotheses of Theorem (2.1) it is attained). -/
noncomputable def maxFunction {n : ℕ} {U : Type*} (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ u, g x u

/-- Clarke (1975), Theorem (2.1)(3): `M(x) = {u ∈ U : g(x, u) = f(x)}`, the set of maximizers. -/
def maximizers {n : ℕ} {U : Type*} (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set U :=
  {u | g x u = maxFunction g x}

end ClarkeGradients.MaxFunctions


