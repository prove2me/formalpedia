-- Prove2me | Definitions.Def_GeoSemialgCSP_IsGeometric
-- name    : GeoSemialgCSP_IsGeometric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:42.916494+00:00
-- url     : https://prove2.me/theorems/fe37f605-ecd7-4a10-9c7b-040292668f20
-- title:
--   Geometric predicate (Definition 1.1)
-- statement:
--   A $k$-ary predicate $P$ on $(\mathbb R^d)^k$ with accepting set $S$ is **geometric** if
--
--   1. it is invariant under positive scalings and common translations: for every $\lambda>0$ and $t\in\mathbb R^d$,
--   $$P(\lambda x_1+t,\dots,\lambda x_k+t)=P(x_1,\dots,x_k);$$
--   2. its satisfying tuples are stable under small perturbations: if $P(x_1,\dots,x_k)=1$, there is $r=r(x_1,\dots,x_k)>0$ such that $P(\hat x_1,\dots,\hat x_k)=1$ whenever $\|x_i-\hat x_i\|_2\le r$ for all $i$.
--
--   Together with semialgebraicity this is the class of predicates the paper proves approximation resistant.
--
--   **Formalization Note** Property 1 is an equivalence (both sides are $\{0,1\}$-valued and equal). The balls in property 2 are closed, as printed.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Definition 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E

namespace GeoSemialgCSP

/-- **Geometric predicate.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Definition 1.1, printed p.2 (PDF p.3).

A `k`-ary predicate with accepting set `S ⊆ (ℝ^d)^k` is *geometric* if
1. `P(λx₁ + t, …, λx_k + t) = P(x₁, …, x_k)` for every `λ > 0` and `t ∈ ℝ^d` (invariance under
   positive scalings and common translations), and
2. every satisfying tuple `x` has an `r > 0` such that `P(x̂) = 1` whenever `‖xᵢ − x̂ᵢ‖₂ ≤ r` for
   all `i`.

**Formalization Note.** (1) is an equivalence (the page has `=`). The scale is called `c` because
`λ` is reserved in Lean. In (2) the balls are closed, as printed, and `dist` on `E d` is `‖·‖₂`.
Semialgebraicity is the separate predicate `IsSemialgebraicPred`. -/
def IsGeometric {k d : ℕ} (S : Set (Fin k → E d)) : Prop :=
  (∀ c : ℝ, 0 < c → ∀ t : E d, ∀ x : Fin k → E d, ((fun j => c • x j + t) ∈ S ↔ x ∈ S)) ∧
  (∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ ∀ y : Fin k → E d, (∀ j, dist (x j) (y j) ≤ r) → y ∈ S)

end GeoSemialgCSP


