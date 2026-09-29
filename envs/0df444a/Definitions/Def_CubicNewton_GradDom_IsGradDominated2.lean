-- Prove2me | Definitions.Def_CubicNewton_GradDom_IsGradDominated2
-- name    : CubicNewton_GradDom_IsGradDominated2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:26:10.904985+00:00
-- url     : https://prove2.me/theorems/90c0f47c-767f-4080-b9af-c60bfcc3f384
-- title:
--   Gradient domination of degree two (Polyak–Łojasiewicz condition) on $F$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ and let $f$ be differentiable on $F$ with gradient $f'(x)$. The function $f$ is **gradient dominated of degree $2$** on $F$, with constant $\tau_f$ and minimizer $x^*$, if $x^* \in F$ is a global minimizer of $f$ on $F$, $\tau_f > 0$, and
--   $$f(x) - f(x^*) \le \tau_f\,\|f'(x)\|^2 \qquad \text{for all } x \in F .$$
--   This is Definition 3 of the paper with degree $p = 2$, inequality (4.7); for $p = 2$ the class goes back to Polyak (1963) and is now usually called the Polyak–Łojasiewicz condition. The global minimum need not be unique, and $f(x^*)$ does not depend on which minimizer is chosen. Strongly convex functions with parameter $\gamma$ belong to the class with $\tau_f = 1/(2\gamma)$ (Example 2), and so do sums of squares of a system of equations with uniformly non-degenerate Jacobian (Example 3), whose minima are in general not isolated.
--
--   **Formalization Note** The gradient is a map `g`; "attains a global minimum" is read over $F$, the set on which the paper's $f$ lives. Under the standing assumption that $F$ contains the level set $\{x : f(x) \le f(x_0)\}$ this is the same as a global minimum over $\mathbb{R}^n$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 191, Section 4.2, Definition 3, inequality (4.7) with p = 2

import Mathlib

namespace CubicNewton.GradDom

/-- Gradient domination of degree `p = 2` (Nesterov–Polyak 2006, Section 4.2, p. 191,
Definition 3 with `p = 2`): `f` attains its global minimum over `F` at `xs ∈ F`, the constant
`τ` (the paper's `τ_f`) is positive, and for every `x ∈ F`
`f(x) − f(x*) ≤ τ_f ‖f′(x)‖²`  (4.7),
with `g x` in the role of `f′(x)`. -/
def IsGradDominated2 {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (τ : ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  xs ∈ F ∧ (∀ y ∈ F, f xs ≤ f y) ∧ 0 < τ ∧ ∀ x ∈ F, f x - f xs ≤ τ * ‖g x‖ ^ 2

end CubicNewton.GradDom


