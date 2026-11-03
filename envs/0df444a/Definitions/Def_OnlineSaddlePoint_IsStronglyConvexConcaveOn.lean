-- Prove2me | Definitions.Def_OnlineSaddlePoint_IsStronglyConvexConcaveOn
-- name    : OnlineSaddlePoint_IsStronglyConvexConcaveOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:19.820045+00:00
-- url     : https://prove2.me/theorems/65127381-4e67-45cf-8f0b-7a2c867ee88b
-- title:
--   $H$-strongly convex-concave function on $X\times Y$
-- statement:
--   Let $H\in\mathbb R$. A function $\mathcal L : X\times Y\to\mathbb R$ is **$H$-strongly convex-concave** if, for every fixed $y_0\in Y$, $x\mapsto\mathcal L(x,y_0)$ is $H$-strongly convex on $X$, and, for every fixed $x_0\in X$, $y\mapsto\mathcal L(x_0,y)$ is $H$-strongly concave on $Y$. Here $g$ is $H$-strongly convex on $X$ if $X$ is convex and
--
--   $$
--   g(ax_1+bx_2)\le a\,g(x_1)+b\,g(x_2)-ab\,\frac H2\|x_1-x_2\|^2
--   $$
--
--   for all $x_1,x_2\in X$ and $a,b\ge0$ with $a+b=1$; $g$ is $H$-strongly concave if $-g$ is $H$-strongly convex.
--
--   Strong convexity-concavity makes the saddle point of the cumulative game unique and forces consecutive Follow-the-Leader iterates to be close.
--
--   **Formalization Note** The paper's definition is the subgradient form $f(x_1)\ge f(x_2)+\nabla f(x_2)^\top(x_1-x_2)+\frac H2\|x_1-x_2\|^2$. It implies the chord form used here (Mathlib's `StrongConvexOn`/`StrongConcaveOn`), so this predicate is the weaker of the two.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, §3, p.5

import Mathlib

namespace OnlineSaddlePoint

/-- **`H`-strongly convex-concave function.** Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, §3,
p.5: "we say a function `𝓛(x, y)` is `H`-strongly convex-concave if for any fixed `y₀ ∈ Y`, the
function `𝓛(x, y₀)` is `H`-strongly convex in `x`, and for any fixed `x₀ ∈ X`, the function
`𝓛(x₀, y)` is `H`-strongly concave in `y`."

**Formalization Note.** `H`-strong convexity is Mathlib's `StrongConvexOn X H g`: `X` is convex and
`g(a x₁ + b x₂) ≤ a g(x₁) + b g(x₂) − a b (H/2)‖x₁ − x₂‖²` for `x₁, x₂ ∈ X`, `a, b ≥ 0`,
`a + b = 1`; strong concavity is `StrongConcaveOn`. The paper's p.5 definition is the subgradient
form `f(x₁) ≥ f(x₂) + ∇f(x₂)ᵀ(x₁ − x₂) + (H/2)‖x₁ − x₂‖²`, which implies Mathlib's (apply it at the
base point `a x₁ + b x₂` and average), so this predicate is a weaker hypothesis. -/
def IsStronglyConvexConcaveOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set E) (Y : Set F) (H : ℝ)
    (f : E → F → ℝ) : Prop :=
  (∀ y ∈ Y, StrongConvexOn X H (fun x => f x y)) ∧ (∀ x ∈ X, StrongConcaveOn Y H (fun y => f x y))

end OnlineSaddlePoint


