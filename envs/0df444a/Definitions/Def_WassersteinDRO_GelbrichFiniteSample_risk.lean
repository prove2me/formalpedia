-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_risk
-- name    : WassersteinDRO_GelbrichFiniteSample_risk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:35.764568+00:00
-- url     : https://prove2.me/theorems/1476ef89-269f-49ef-9b80-0a0133dbf87b
-- title:
--   Risk $\mathcal R(\mathbb Q, \ell) = \mathbb E^{\mathbb Q}[\ell(\xi)]$ with the infeasibility convention
-- statement:
--   Let $\mathbb Q$ be a measure on a measurable space $E$ and let $\ell : E \to [-\infty, +\infty]$ be a loss function. Write $\ell^+ = \max(\ell, 0)$ and $\ell^- = \max(-\ell, 0)$. The **risk** of $\ell$ under $\mathbb Q$ is
--
--   $$\mathcal R(\mathbb Q, \ell) = \mathbb E^{\mathbb Q}[\ell(\xi)] = \begin{cases} +\infty & \text{if } \int \ell^+ \, \mathrm d\mathbb Q = +\infty, \\ \int \ell^+ \, \mathrm d\mathbb Q - \int \ell^- \, \mathrm d\mathbb Q & \text{otherwise.} \end{cases}$$
--
--   This is the paper's expected loss (1) together with its convention that $\mathbb E^{\mathbb P}[\ell(\xi)] = \infty$ whenever the expectations of the positive and negative parts are both infinite ("infeasibility trumps unboundedness"). The value lies in $[-\infty, +\infty]$ and is defined for every loss.
--
--   **Formalization Note** The positive and negative parts are integrated as nonnegative extended reals, never with the Bochner integral (which returns $0$ for non-integrable functions). The explicit case split is needed because $\top - \top = \bot$ in Lean's `EReal`. The same body appears in the unpublished sibling draft `WassersteinDRO.ConvexLossP1.risk`; it is restated here because drafts cannot import drafts.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, eq. (1), p. 1, and the expectation convention of §1, p. 2

import Mathlib

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The risk `R(Q, ℓ) = E^Q[ℓ(ξ)]` with the paper's expectation convention.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, eq. (1), p. 1: "The risk of a decision ℓ ∈ L is defined as the expected loss under P,
that is, R(P, ℓ) = E^P[ℓ(ξ)]"; and §1, p. 2: "To ensure that the expectations in (1) and (2) are
defined for all measurable loss functions, we set E^P[ℓ(ξ)] = ∞ whenever the expectations of the
positive and negative parts of ℓ(ξ) are both infinite. This convention means that infeasibility
trumps unboundedness."

`risk Q ℓ` is `+∞` if `∫ ℓ⁺ dQ = +∞`, and `∫ ℓ⁺ dQ − ∫ ℓ⁻ dQ ∈ [−∞, ∞)` otherwise, where
`ℓ⁺ = max(ℓ, 0)` and `ℓ⁻ = max(−ℓ, 0)`.

**Formalization Note.** The positive and negative parts are integrated as nonnegative extended
reals (`lintegral` of `EReal.toENNReal`), never with the Bochner integral (which returns `0` for
a non-integrable function). The explicit case split is needed because `⊤ − ⊤ = ⊥` in `EReal`,
the opposite of the paper's convention: with it, `∫ ℓ⁺ = ∞` gives `+∞` whatever `∫ ℓ⁻` is, and a
finite `∫ ℓ⁺` with `∫ ℓ⁻ = ∞` gives `−∞`. The body is the same as the unpublished sibling draft
`WassersteinDRO.ConvexLossP1.risk`; it is restated here because drafts cannot import drafts. -/
noncomputable def risk {E : Type*} [MeasurableSpace E] (Q : Measure E) (ℓ : E → EReal) : EReal :=
  if ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q = ⊤ then ⊤
  else ((∫⁻ ξ, (ℓ ξ).toENNReal ∂Q : ENNReal) : EReal) - ((∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q : ENNReal) : EReal)

end WassersteinDRO.GelbrichFiniteSample


