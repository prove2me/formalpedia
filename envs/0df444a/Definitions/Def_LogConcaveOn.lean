-- Prove2me | Definitions.Def_LogConcaveOn
-- name    : LogConcaveOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-11T21:35:59.422843+00:00
-- url     : https://prove2.me/theorems/5618ba2d-1599-4a52-88e6-65a06037d285
-- title:
--   Log-concave function on a set
-- statement:
--   **Log-concavity of a nonnegative function on a set**, in the power form that permits the value zero.
--
--   Let $E$ be a real vector space (or any additive commutative monoid with a real scalar action), let $s \subseteq E$ and let $f : E \to \mathbb{R}$. Then $f$ is *log-concave on $s$* when $f \ge 0$ on $s$ and
--
--   $$f(x)^{a}\, f(y)^{b} \;\le\; f(ax + by) \qquad \text{for all } x, y \in s \text{ and all } a, b \ge 0 \text{ with } a + b = 1 .$$
--
--   Where $f$ is strictly positive this is exactly concavity of $\log f$, i.e. $\log f(ax+by) \ge a\log f(x) + b\log f(y)$; writing it with powers instead of logarithms keeps the definition meaningful when $f$ vanishes, which is essential because the densities of interest — the uniform density on a convex body, for instance — are zero outside a set.
--
--   Log-concave functions are closed under products, marginals and convolution, and include the Gaussian, exponential, uniform, Beta, Dirichlet and Wishart densities as well as indicator functions of convex sets. Prékopa's theorem, the goal of this mission, is the closure property under marginalization.
--
--   **Formalization Note** The predicate is stated for a general `E` with `[AddCommMonoid E] [SMul ℝ E]` so that it applies to products such as $\mathbb{R}^n \times \mathbb{R}^m$; the powers are real `rpow`, for which $0^{a} = 0$ when $a > 0$ and $0^{0} = 1$. Convexity of `s` is *not* required by the predicate — the combination $ax + by$ is constrained even when it falls outside `s` — so the definition is intended for, and only well behaved on, convex `s`. Source: B&V §3.5.1, p. 104.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 104, §3.5.1 (definition of a log-concave function). Formalized in the zero-permitting power form f(x)^a f(y)^b <= f(ax+by), which agrees with concavity of log f where f > 0 and stays meaningful where f vanishes

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- **Log-concave function on a set** (B&V §3.5.1, extended to allow zero values
via the `rpow` form): `f ≥ 0` on `s` and
`f x ^ a * f y ^ b ≤ f (a • x + b • y)` for all convex weights.
Note: the predicate does not require `s` to be convex; it is intended for (and
only well-behaved on) convex `s` — the combination point `a • x + b • y` is
constrained even when it lies outside `s`. -/
def LogConcaveOn {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (s : Set E) (f : E → ℝ) : Prop :=
  (∀ x ∈ s, 0 ≤ f x) ∧
  ∀ x ∈ s, ∀ y ∈ s, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f x ^ a * f y ^ b ≤ f (a • x + b • y)

end ConvexOptimization


