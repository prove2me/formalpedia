-- Prove2me | Definitions.Def_CubicNewton_StarConvex_IsStarConvexFn
-- name    : CubicNewton_StarConvex_IsStarConvexFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:23:17.925347+00:00
-- url     : https://prove2.me/theorems/88557120-7f73-4f83-9f46-50a4224808c1
-- title:
--   Star-convex function (Nesterov–Polyak Definition 1)
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}$. Write $X^*$ for the set of global minimizers of $f$ over $\mathbb{R}^n$. The function $f$ is **star-convex** (relative to $F$) if $X^*$ is nonempty and, for every $x^* \in X^*$, every $x \in F$ and every $\alpha \in [0, 1]$,
--
--   $$f(\alpha x^* + (1 - \alpha) x) \le \alpha f(x^*) + (1 - \alpha) f(x).$$
--
--   Every convex function with a global minimizer is star-convex, but star-convexity is much weaker: for instance $f(x) = |x|(1 - e^{-|x|})$ on $\mathbb{R}$ is star-convex and not convex. It is the problem class on which the cubic regularization of Newton method converges at the rate $O(1/k^2)$ in function value (Theorem 4).
--
--   **Formalization Note** Definition 1 in the paper introduces $x$ both as "any $x \in \mathbb{R}^n$" and, in display (4.1), as "$\forall x \in \mathcal F$"; the formalization uses the display's quantifier $x \in F$, which is the weaker requirement on $f$. This is a property of a function, unrelated to Mathlib's `StarConvex`, which is a property of sets.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 188, Section 4.1, Definition 1, Eq. (4.1)

import Mathlib

namespace CubicNewton.StarConvex

/-- Star-convex function (Nesterov–Polyak 2006, Section 4.1, p. 188, Definition 1, (4.1)).
`f` is star-convex relative to `F` if its set `X*` of global minimizers over the whole space is
nonempty, and for every global minimizer `x*`, every `x ∈ F` and every `α ∈ [0, 1]`,
`f(α x* + (1 − α) x) ≤ α f(x*) + (1 − α) f(x)`.
The point `x` ranges over `F`, as in the display (4.1). This is a property of a function, not
Mathlib's `StarConvex` (a property of sets). -/
def IsStarConvexFn {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∃ xs : EuclideanSpace ℝ (Fin n), ∀ y, f xs ≤ f y) ∧
    ∀ xs : EuclideanSpace ℝ (Fin n), (∀ y, f xs ≤ f y) →
      ∀ x ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1,
        f (α • xs + (1 - α) • x) ≤ α * f xs + (1 - α) * f x

end CubicNewton.StarConvex


