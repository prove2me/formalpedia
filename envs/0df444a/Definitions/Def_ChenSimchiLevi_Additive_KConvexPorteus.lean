-- Prove2me | Definitions.Def_ChenSimchiLevi_Additive_KConvexPorteus
-- name    : ChenSimchiLevi_Additive_KConvexPorteus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:22:19.69133+00:00
-- url     : https://prove2.me/theorems/24395a4c-96ce-48cd-bc0e-efd6459868a4
-- title:
--   Definition 2.2 — $k$-convexity in Porteus's form (5)
-- statement:
--   Let $k \in \mathbb R$ and $f : \mathbb R \to \mathbb R$. Following Definition 2.2 of Chen and Simchi-Levi (2004), which goes back to Porteus (1971), $f$ is called **$k$-convex** if for all $x_0 \le x_1$ and every $\lambda \in [0,1]$,
--
--   $$
--   f\big((1-\lambda)x_0 + \lambda x_1\big) \le (1-\lambda) f(x_0) + \lambda f(x_1) + \lambda k. \qquad (5)
--   $$
--
--   A function $f$ is **$k$-concave** if $-f$ is $k$-convex.
--
--   Unlike ordinary convexity, (5) is not symmetric in $x_0$ and $x_1$: the penalty $\lambda k$ is weighted by the coefficient of the right end point $x_1$. For $k = 0$ the condition is ordinary convexity. This form of $k$-convexity is the one the paper uses to prove that the profit-to-go function of the additive-demand pricing and inventory problem is $k$-concave; it is equivalent to the derivative-free form (4) of Definition 2.1 (platform definition `BertsekasKConvex`).
--
--   **Formalization Note.** The paper restricts to $k \ge 0$. The definition here is stated for every real $k$; taking $\lambda = 1$ shows that a $k$-convex function in this sense can exist only if $k \ge 0$.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 889, Definition 2.2, (5)

import Mathlib

namespace ChenSimchiLevi.Additive

/-- Definition 2.2 of Chen–Simchi-Levi (2004), p. 889 (Porteus's form of `k`-convexity):
a real-valued function `f` is `k`-convex if for any `x₀ ≤ x₁` and `λ ∈ [0, 1]`,
`f((1 - λ) x₀ + λ x₁) ≤ (1 - λ) f(x₀) + λ f(x₁) + λ k`   (5).
The order `x₀ ≤ x₁` is part of the definition: (5) is not symmetric in `x₀` and `x₁`. -/
def KConvexPorteus (k : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x₀ x₁ lam : ℝ, x₀ ≤ x₁ → lam ∈ Set.Icc (0 : ℝ) 1 →
    f ((1 - lam) * x₀ + lam * x₁) ≤ (1 - lam) * f x₀ + lam * f x₁ + lam * k

end ChenSimchiLevi.Additive


