-- Prove2me | Definitions.Def_ZeroOneSimplex_IsShadowPath
-- name    : ZeroOneSimplex_IsShadowPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:56.574585+00:00
-- url     : https://prove2.me/theorems/798f5a29-a036-4dcf-8d7b-5673d5922791
-- title:
--   Shadow rule steps and Shadow rule paths
-- statement:
--   Let $Q\subseteq\mathbb R^n$, $c$ an objective and $v$ an auxiliary vector. From a vertex $x$, a **Shadow rule step** moves to a $v$-improving neighbor $x'\in N_v(x)$ maximizing the slope
--   $$
--   \frac{c^\top(u-x)}{v^\top(u-x)}\qquad\text{over } u\in N_v(x);
--   $$
--   ties may be broken arbitrarily. All denominators are positive.
--
--   A **Shadow rule path** is a sequence of vertices $x^0,\dots,x^k$ in which each vertex is a Shadow rule step from the previous one and no $x^i$ with $i<k$ is a $c$-maximum of $Q$: the rule stops once it reaches an optimal solution.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Definition 3, p.13

import Mathlib
import Definitions.Def_ZeroOneSimplex_IsEdge

set_option autoImplicit false

namespace ZeroOneSimplex

/-- **Shadow rule step** (arXiv:2111.14050v1, Definition 3, p.13): from the vertex `x` the rule
moves to a `v`-improving neighbor `x'` of `x` that maximizes the slope
`cᵀ(u − x) / vᵀ(u − x)` over all `u ∈ N_v(x)`. Ties may be broken arbitrarily (p.13).

**Formalization Note.** Every denominator `vᵀ(u − x)` with `u ∈ N_v(x)` is positive, so the
division is never applied to `0`. -/
def IsShadowStep {n : ℕ} (Q : Set (Fin n → ℝ)) (c v x x' : Fin n → ℝ) : Prop :=
  x' ∈ improvingNbrs Q v x ∧
    ∀ u ∈ improvingNbrs Q v x, c ⬝ᵥ (u - x) / v ⬝ᵥ (u - x) ≤ c ⬝ᵥ (x' - x) / v ⬝ᵥ (x' - x)

/-- **A path of the Shadow rule** (arXiv:2111.14050v1, Definition 3, p.13): vertices
`x 0, …, x k` of `Q`, each obtained from the previous one by a Shadow rule step for `(c, v)`.
The rule constructs a path "to an optimal LP solution", so it stops at a `c`-maximum: no
`x i` with `i < k` maximizes `c` on `Q`. -/
def IsShadowPath {n : ℕ} (Q : Set (Fin n → ℝ)) (c v : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (k : ℕ) : Prop :=
  x 0 ∈ Set.extremePoints ℝ Q ∧
    ∀ i < k, ¬ IsMaximizer Q c (x i) ∧ IsShadowStep Q c v (x i) (x (i + 1))

end ZeroOneSimplex


