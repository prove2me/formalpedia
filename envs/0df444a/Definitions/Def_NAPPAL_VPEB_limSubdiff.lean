-- Prove2me | Definitions.Def_NAPPAL_VPEB_limSubdiff
-- name    : NAPPAL_VPEB_limSubdiff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:07.942885+00:00
-- url     : https://prove2.me/theorems/66a4ffae-b9bd-450b-a6fd-684ff064eb81
-- title:
--   Limiting subdifferential $\partial f(\bar x)$
-- statement:
--   Let $X$ be a real inner product space and $f : X \to [-\infty, +\infty]$. For $\bar x \in \operatorname{dom} f$, the **limiting subdifferential** (the "subdifferential" of the paper) is
--   $$\partial f(\bar x) = \{\xi \in X : \exists\, x_n \to \bar x,\ f(x_n) \to f(\bar x),\ \xi_n \in \partial_F f(x_n),\ \xi_n \to \xi\},$$
--   and $\partial f(\bar x) = \emptyset$ when $f(\bar x) = +\infty$.
--
--   With the convention $\operatorname{dist}(0, \emptyset) = +\infty$ (p. 5), the residual $\operatorname{dist}(0, \partial \mathcal L_\gamma(w))$ is the stationarity measure of the paper.
--
--   **Formalization Note** Convergence $f(x_n) \to f(\bar x)$ is in the extended reals. Distances to these sets are taken with `Metric.infEDist`, which is $+\infty$ on the empty set.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, Definition 2.1(iii), pp. 5–6

import Mathlib
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff

open scoped InnerProductSpace Topology

namespace NAPPAL.VPEB

/-- **Limiting subdifferential** (Definition 2.1(iii)).
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, Definition 2.1(iii), pp. 5–6: "The limiting-subdifferential ([14]), or simply the
subdifferential for short, of ψ at x̄ ∈ dom(ψ) – denoted by ∂ψ(x̄) – is defined as:
∂ψ(x̄) := {ξ ∈ Rn : ∃xn → x̄, ψ(xn) → ψ(x̄), ξn ∈ ∂Fψ(xn) → ξ}."

`ξ ∈ limSubdiff f x` iff `f x ≠ ⊤` and there are sequences `xⱼ → x` with `f xⱼ → f x` (in
`EReal`) and `ξⱼ ∈ ∂_F f(xⱼ)` with `ξⱼ → ξ`.

**Formalization Note.** For `x ∉ dom f` the set is empty, as in the paper (∂ψ(x̄) is only
defined at `x̄ ∈ dom ψ`, and `∂_F ψ(x̄) = ∅` off the domain). The distance to the empty set is
`+∞` (p. 5), which is why every distance in this mission is `Metric.infEDist` in `ℝ≥0∞`. -/
def limSubdiff {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x : X) : Set X :=
  {ξ | f x ≠ ⊤ ∧ ∃ xs ξs : ℕ → X, Filter.Tendsto xs Filter.atTop (𝓝 x) ∧
    Filter.Tendsto (fun j => f (xs j)) Filter.atTop (𝓝 (f x)) ∧
    (∀ j, ξs j ∈ frechetSubdiff f (xs j)) ∧ Filter.Tendsto ξs Filter.atTop (𝓝 ξ)}

end NAPPAL.VPEB


