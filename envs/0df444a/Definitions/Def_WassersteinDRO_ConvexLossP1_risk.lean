-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_risk
-- name    : WassersteinDRO_ConvexLossP1_risk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:53.808052+00:00
-- url     : https://prove2.me/theorems/567a0795-43ae-44bf-ab67-6df537481bd3
-- title:
--   Risk $\mathcal R(\mathbb Q, \ell) = \mathbb E^{\mathbb Q}[\ell(\xi)]$ with the infeasibility convention
-- statement:
--   Let $\mathbb Q$ be a measure on a measurable space $E$ and let $\ell : E \to [-\infty, +\infty]$ be a loss function. Write $\ell^+ = \max(\ell, 0)$ and $\ell^- = \max(-\ell, 0)$. The **risk** of $\ell$ under $\mathbb Q$ is
--   $$\mathcal R(\mathbb Q, \ell) = \mathbb E^{\mathbb Q}[\ell(\xi)] = \begin{cases} +\infty & \text{if } \int \ell^+ \, \mathrm d\mathbb Q = +\infty, \\ \int \ell^+ \, \mathrm d\mathbb Q - \int \ell^- \, \mathrm d\mathbb Q & \text{otherwise.} \end{cases}$$
--
--   In particular the expectation is $+\infty$ whenever the expectations of the positive and negative parts are both infinite ("infeasibility trumps unboundedness"), so the risk is defined for every measurable loss and takes values in $[-\infty, +\infty]$.
--
--   **Formalization Note** The positive and negative parts are integrated as nonnegative extended reals (Lebesgue integral of `EReal.toENNReal`), never with the Bochner integral. The case split is necessary because in `EReal` the difference $\infty - \infty$ evaluates to $-\infty$, the opposite of the paper's convention.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, eq. (1), p. 1, and the expectation convention, p. 2

import Mathlib

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **The risk `R(Q, ℓ) = E^Q[ℓ(ξ)]` with the paper's expectation convention.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, eq. (1), p. 1: "The risk of a decision ℓ ∈ L is defined as the expected loss under P, that is,
R(P, ℓ) = E^P[ℓ(ξ)]"; and p. 2: "To ensure that the expectations in (1) and (2) are defined for
all measurable loss functions, we set E^P[ℓ(ξ)] = ∞ whenever the expectations of the positive and
negative parts of ℓ(ξ) are both infinite. This convention means that infeasibility trumps
unboundedness."

`risk Q ℓ` is `+∞` if `∫ ℓ⁺ dQ = +∞`, and `∫ ℓ⁺ dQ − ∫ ℓ⁻ dQ ∈ [−∞, ∞)` otherwise, where
`ℓ⁺ = max(ℓ, 0)` and `ℓ⁻ = max(−ℓ, 0)`.

**Formalization Note.** The positive and negative parts are integrated as nonnegative extended reals
(`lintegral` of `EReal.toENNReal`), never with the Bochner integral (which returns `0` for a
non-integrable function). The explicit case split is needed because in `EReal`, `⊤ − ⊤ = ⊥`,
the opposite of the paper's convention; with the case split, `∫ ℓ⁺ = ∞` gives `+∞` whatever
`∫ ℓ⁻` is, and a finite `∫ ℓ⁺` with `∫ ℓ⁻ = ∞` gives `−∞`. -/
noncomputable def risk {E : Type*} [MeasurableSpace E] (Q : Measure E) (ℓ : E → EReal) : EReal :=
  if ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q = ⊤ then ⊤
  else ((∫⁻ ξ, (ℓ ξ).toENNReal ∂Q : ENNReal) : EReal) - ((∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q : ENNReal) : EReal)

end WassersteinDRO.ConvexLossP1


