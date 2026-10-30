-- Prove2me | Definitions.Def_NAPPAL_VPEB_frechetSubdiff
-- name    : NAPPAL_VPEB_frechetSubdiff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:40.460391+00:00
-- url     : https://prove2.me/theorems/2684306e-9865-4a8e-bb1f-23536b5f1111
-- title:
--   Fréchet subdifferential $\partial_F f(\bar x)$
-- statement:
--   Let $X$ be a real inner product space and $f : X \to [-\infty, +\infty]$, with domain $\operatorname{dom} f = \{x : f(x) < +\infty\}$. For $\bar x \in \operatorname{dom} f$, the **Fréchet subdifferential** $\partial_F f(\bar x)$ is the set of all $\xi \in X$ with
--   $$\liminf_{x \to \bar x,\ x \ne \bar x} \frac{f(x) - f(\bar x) - \langle \xi, x - \bar x \rangle}{\|x - \bar x\|} \ \ge\ 0 ,$$
--   equivalently: for every $\varepsilon > 0$, $f(x) \ge f(\bar x) + \langle \xi, x - \bar x\rangle - \varepsilon \|x - \bar x\|$ for all $x$ near $\bar x$. If $\bar x \notin \operatorname{dom} f$ then $\partial_F f(\bar x) = \emptyset$.
--
--   The Fréchet subdifferential is the building block of the limiting subdifferential used throughout the paper.
--
--   **Formalization Note** Lean uses the $\varepsilon$-form; its equivalence with the liminf form at points of the domain is proved in the mission's verification file. No lower semicontinuity of $f$ is assumed.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, Definition 2.1(i)–(ii), p. 5

import Mathlib

open scoped InnerProductSpace Topology

namespace NAPPAL.VPEB

/-- **Fréchet subdifferential** (Definition 2.1(ii)).
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, Definition 2.1(ii), p. 5: "For each x̄ ∈ dom(ψ), the Fréchet subdifferential of ψ at x̄ –
denoted by ∂Fψ(x̄) – is the set of all vector ξ ∈ Rn satisfying
lim inf_{x≠x̄, x→x̄} (1/‖x − x̄‖)[ψ(x) − ψ(x̄) − ⟨ξ, x − x̄⟩] ≥ 0. If x̄ ∉ dom(ψ), then ∂Fψ(x̄) = ∅."
Definition 2.1(i): "The domain of ψ … is {x ∈ Rn : ψ(x) < +∞}."

For `f : X → EReal` on a real inner product space `X`, `ξ ∈ frechetSubdiff f x` iff `f x ≠ ⊤`
(i.e. `x ∈ dom f`) and for every `ε > 0`, for all `y` near `x`,
`f x + ⟨ξ, y − x⟩ − ε‖y − x‖ ≤ f y`.

**Formalization Note.** The ε-form is equivalent to the liminf form whenever `f x` is finite (for
`y ≠ x` divide by `‖y − x‖`; at `y = x` the inequality is `f x ≤ f x`); the equivalence is proved
in `Solutions/verification/NAPPAL_VPEB_sanity.lean`. The paper states the definition for proper
l.s.c. `ψ : Rn → R ∪ {+∞}`; the formula is used here for any `f` with values in `EReal` and on any
real inner product space (the paper applies it on `Rn × Rd × Rm`). No lower semicontinuity is
bundled. -/
def frechetSubdiff {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x : X) : Set X :=
  {ξ | f x ≠ ⊤ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ y in 𝓝 x, f x + ((⟪ξ, y - x⟫_ℝ - ε * ‖y - x‖ : ℝ) : EReal) ≤ f y}

end NAPPAL.VPEB


