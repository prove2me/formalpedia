-- Prove2me | Definitions.Def_CubicNewton_Nonconvex_Supplement_IsGloballyNondegenerate
-- name    : CubicNewton_Nonconvex_Supplement_IsGloballyNondegenerate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:58:31.93677+00:00
-- url     : https://prove2.me/theorems/2540e8f0-813c-4d11-9556-5652d75db455
-- title:
--   Definition 2 — globally non-degenerate optimal set
-- statement:
--   Let $F\subseteq\mathbb R^n$, let $f:\mathbb R^n\to\mathbb R$, let $X^*$ be the set of global minimizers of $f$ and $f^*$ the global minimal value. The optimal set $X^*$ is **globally non-degenerate** with constant $\gamma$ if $X^*$ is nonempty, $\gamma>0$, and for every $x\in F$
--   $$f(x)-f^*\ \ge\ \frac{\gamma}{2}\,\rho^2(x,X^*),$$
--   where $\rho(x,X^*)$ is the Euclidean distance from $x$ to the whole set $X^*$. The set $X^*$ need not be a singleton or convex; for example $f(x)=(\|x\|^2-1)^2$ has $X^*=\{\|x\|=1\}$. This quadratic-growth condition is the hypothesis of Theorem 5.
--
--   **Formalization Note** $X^*$ is the set of global minimizers over all of $\mathbb R^n$, as in the published Definition 1 predicate, and $f^*$ is written as $f(x^*)$ for any $x^*\in X^*$. The distance is `Metric.infDist`.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 190, Definition 2, (4.3)

import Mathlib

namespace CubicNewton.Nonconvex.Supplement

/-- Globally non-degenerate optimal set (Nesterov–Polyak 2006, Section 4.1, p. 190,
Definition 2, (4.3)). Write `X* = {z : ∀ y, f z ≤ f y}` for the set of global minimizers of `f`
and `f* = f(x*)` for the global minimal value. The optimal set is globally non-degenerate with
constant `γ` if `X*` is nonempty, `γ > 0`, and for every `x ∈ F`
`f(x) − f* ≥ (γ/2) ρ²(x, X*)`,
where `ρ(x, X*)` is the Euclidean distance from `x` to the whole set `X*` (`Metric.infDist`).
The value `f*` is written as `f xs` for an arbitrary global minimizer `xs`; all of them have the
same value. -/
def IsGloballyNondegenerate {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ : ℝ) : Prop :=
  (∃ xs : EuclideanSpace ℝ (Fin n), ∀ y, f xs ≤ f y) ∧
    0 < γ ∧ ∀ x ∈ F, ∀ xs : EuclideanSpace ℝ (Fin n), (∀ y, f xs ≤ f y) →
      γ / 2 * Metric.infDist x {z | ∀ y, f z ≤ f y} ^ 2 ≤ f x - f xs

end CubicNewton.Nonconvex.Supplement


