-- Prove2me | Definitions.Def_NAPPAL_VPEB_HasKLAt
-- name    : NAPPAL_VPEB_HasKLAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:32.908731+00:00
-- url     : https://prove2.me/theorems/af8bdc10-aa6b-483d-a1af-c5a4d09e5769
-- title:
--   Kurdyka–Łojasiewicz inequality at $\bar x$ with exponent $\theta$ and constants $\eta, \nu, \kappa_2$
-- statement:
--   Let $X$ be a real inner product space, $f : X \to [-\infty, +\infty]$, $\bar x \in X$ and $\theta, \eta, \nu, \kappa_2 \in \mathbb{R}$. The function $f$ satisfies the **KL inequality at $\bar x$ with exponent $\theta$ and constants $\eta, \nu, \kappa_2$** if
--   $$[f(x) - f(\bar x)]^\theta \le \kappa_2\, \operatorname{dist}(0, \partial f(x)) \quad \text{for all } x \in \mathfrak B(\bar x; \eta, \nu),$$
--   where $\mathfrak B(\bar x; \eta, \nu) = \{x : \|x - \bar x\| < \eta,\ f(\bar x) < f(x) < f(\bar x) + \nu\}$ and $\partial$ is the limiting subdifferential. The KL property of Definition 6.1 asks this for some $\eta, \nu, \kappa_2 > 0$.
--
--   The KL property with exponent $1/2$ is the hypothesis of Proposition 6.1, which turns it into the error bound VP-EB along NAPP-AL.
--
--   **Formalization Note** $\operatorname{dist}(0, \cdot)$ takes values in $[0, +\infty]$ with $\operatorname{dist}(0, \emptyset) = +\infty$, and the inequality is compared in $[0, +\infty]$. On the region both $f(x)$ and $f(\bar x)$ are finite. No lower semicontinuity of $f$ is part of the definition.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §6, p. 22 (the set 𝔅(w̄; η, ν) and Definition 6.1)

import Mathlib
import Definitions.Def_NAPPAL_VPEB_limSubdiff

namespace NAPPAL.VPEB

/-- **The Kurdyka–Łojasiewicz inequality at `x̄` with exponent `θ` and constants `η, ν, κ₂`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §6, p. 22: "For given positive numbers η and ν, let us define
𝔅(w̄; η, ν) = 𝔹(w̄; η) ∩ {w ∈ Rn × Rd × Rm : Λ∗ < Lγ(w) < Λ∗ + ν}." and Definition 6.1
(Kurdyka-Łojasiewicz property [1, 10]): "The proper lower semicontinuous function 𝓕 is said to
satisfy the Kurdyka-Lojasiewicz (KL) property at x̄ with exponent θ ∈ (0, 1), if there exist
η > 0, ν > 0, and κ2 > 0 such that the following inequality holds:
[𝓕(x) − 𝓕(x̄)]^θ ≤ κ2 dist(0, ∂𝓕(x)), ∀x ∈ 𝔅(x̄; η, ν)."

`HasKLAt f x̄ θ η ν κ₂` says: for every `x` with `‖x − x̄‖ < η` and `f(x̄) < f(x) < f(x̄) + ν`,
`(f(x) − f(x̄))^θ ≤ κ₂ · dist(0, ∂f(x))`, where `∂` is the limiting subdifferential.

**Formalization Note.**
1. The constants `η, ν, κ₂` are arguments; Definition 6.1's property is
   `∃ η > 0, ∃ ν > 0, ∃ κ₂ > 0, HasKLAt f x̄ θ η ν κ₂`, and Proposition 6.1 names them.
2. `𝔹(x̄; η)` is the open ball (p. 19) and `Λ* = 𝓕(x̄)` (Definition 5.1, p. 19).
3. `dist(0, S)` is `Metric.infEDist 0 S` in `[0, +∞]`, so that `dist(0, ∅) = +∞` (p. 5); the
   right side is computed in `ℝ≥0∞`. In the region both `f x` and `f x̄` are finite, so
   `(f x − f x̄).toReal` is the exact difference.
4. No lower semicontinuity or properness of `f` is bundled (paper.md item 11): the definition is
   the inequality alone. -/
def HasKLAt {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (xbar : X) (θ η ν κ₂ : ℝ) : Prop :=
  ∀ x : X, ‖x - xbar‖ < η → f xbar < f x → f x < f xbar + (ν : EReal) →
    ENNReal.ofReal ((f x - f xbar).toReal ^ θ) ≤
      ENNReal.ofReal κ₂ * Metric.infEDist (0 : X) (limSubdiff f x)

end NAPPAL.VPEB


