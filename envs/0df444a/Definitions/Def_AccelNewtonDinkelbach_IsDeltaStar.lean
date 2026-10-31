-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_IsDeltaStar
-- name    : AccelNewtonDinkelbach_IsDeltaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:37.169214+00:00
-- url     : https://prove2.me/theorems/896ecf17-078b-4b52-8737-76dfd0780f47
-- title:
--   The point $\delta^*=\max(\{\delta: f(\delta)=0\}\cup\arg\max f)$
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function that has a root or attains its maximum. The point
--
--   $$\delta^*=\max\bigl(\{\delta: f(\delta)=0\}\cup\arg\max f(\delta)\bigr)$$
--
--   is the largest root of $f$ if $f$ has a root, and otherwise the largest maximizer of $f$. The predicate says that a given real number $\delta^*$ is this greatest element: it belongs to the union of the roots and the maximizers of $f$, and every root and every maximizer is at most $\delta^*$.
--
--   The Newton–Dinkelbach method returns $\delta^*$ when $f$ has a root and certifies $f(\delta^*)<0$ otherwise; all distances in its analysis are measured to $\delta^*$.
--
--   **Formalization Note** Roots and maximizers lie in `dom` (the paper's $f$ is $-\infty$ outside and proper). The paper's "max" is a greatest element, so assuming this predicate is exactly the paper's assumption that $\delta^*$ is well defined.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6

import Mathlib

namespace AccelNewtonDinkelbach

/-- **The point `δ* = max({δ : f(δ) = 0} ∪ arg max f(δ))`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6: "In this paper, we make the mild
assumption that f has a root or attains its maximum. Consequently, the point
δ∗ := max({δ : f(δ) = 0} ∪ arg max f(δ)) is well-defined. It is the largest root of f if f has a
root. Otherwise, it is the largest maximizer of f."

`IsDeltaStar dom f δstar` says that `δstar` is the greatest element of the union of the roots of
`f` in `dom` and the maximizers of `f` over `dom`.

**Formalization Note** `(dom, f)` encodes a proper concave `f : ℝ → ℝ̄` (see `superdiff`): roots
and maximizers of the paper's `f` lie in `dom(f)`, because `f` is `−∞` outside and proper. The
paper's `max` is a greatest element, so this predicate is the paper's definition; assuming it as a
hypothesis is the paper's assumption that `δ*` is well defined. -/
def IsDeltaStar (dom : Set ℝ) (f : ℝ → ℝ) (δstar : ℝ) : Prop :=
  IsGreatest ({x | x ∈ dom ∧ f x = 0} ∪ {x | x ∈ dom ∧ ∀ y ∈ dom, f y ≤ f x}) δstar

end AccelNewtonDinkelbach


