-- Prove2me | Definitions.Def_RiskFunctionals_Deviation_MinimalLoss
-- name    : RiskFunctionals_Deviation_MinimalLoss
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:08.395379+00:00
-- url     : https://prove2.me/theorems/3a3e44c3-df93-47d0-9024-90d0a67400ad
-- title:
--   The Fenchel conjugate $h^*$, the expectation $\mathbb E[h^*(Z)]$, and the minimal loss functional $\mathcal D(Y)=\min\{\mathbb E[h(Y-a)] : a\in\mathbb R\}$
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be a function and $(\Omega,\mathcal F,\mathbb P)$ a probability space.
--
--   1. The **Fenchel conjugate** of $h$ is
--   $$h^*(v)=\sup\{uv-h(u) : u\in\mathbb R\},\qquad v\in\mathbb R,$$
--   a value in $(-\infty,+\infty]$. For instance $h(u)=|u|$ has $h^*(v)=0$ for $|v|\le1$ and $h^*(v)=+\infty$ otherwise.
--   2. For a random variable $Z$, **$\mathbb E[h^*(Z)]<\infty$** means that $h^*(Z)$ is finite almost surely and integrable; then $\mathbb E[h^*(Z)]$ is its expectation.
--   3. For a non-negative convex $h$ with $h(0)=0$, the **minimal loss functional** of a random variable $Y$ is
--   $$\mathcal D(Y)=\min\{\mathbb E[h(Y-a)] : a\in\mathbb R\}. \tag{2.109}$$
--   It is the smallest expected loss of predicting $Y$ by a constant $a$ under the loss $h$.
--
--   Minimal loss functionals include the variance ($h(v)=v^2$), the mean absolute deviation from the median ($h(v)=|v|$) and the average value-at-risk deviation ($h(v)=[v]^++\frac{1-\alpha}{\alpha}[v]^-$).
--
--   **Formalization Note** $h^*$ is a supremum in the extended reals `EReal`, so it is $+\infty$ where the book's supremum is unbounded; it is never $-\infty$. $\mathbb E[h^*(Z)]$ is a real number, the Bochner integral of the real part of $h^*(Z)$; it is meaningful only under the predicate "$\mathbb E[h^*(Z)]<\infty$", which every theorem imposes on the $Z$ it ranges over. $\mathcal D(Y)$ is defined as an **infimum** in $[0,+\infty]$ of the lower Lebesgue integrals $\int h(Y-a)\,d\mathbb P$ (for $h\ge0$ this is $\mathbb E[h(Y-a)]$, possibly $+\infty$): the book's "min" presupposes that the infimum is attained, which fails for instance for $h(v)=[v]^+$ and $Y$ unbounded above, where the infimum $0$ is not attained. The definition itself does not require $h\ge 0$; the theorems do.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 107, §2.5.5, Eq. (2.109); p. 109, Theorem 2.75 (Fenchel conjugate); p. 272, Proposition B.3

import Mathlib

namespace RiskFunctionals.Deviation

open MeasureTheory

/-- The Fenchel conjugate `h*(v) = sup {u v − h(u) : u ∈ ℝ}` of a real function `h`
(Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 109,
Theorem 2.75; p. 271, Appendix B), as a supremum in `EReal`: it is `+∞` where the supremum is
unbounded (e.g. `h(u) = |u|` has `h*(v) = +∞` for `|v| > 1`), and never `−∞`. -/
noncomputable def fenchelConj (h : ℝ → ℝ) (v : ℝ) : EReal :=
  ⨆ u : ℝ, ((u * v - h u : ℝ) : EReal)

/-- `𝔼[h*(Z)] < ∞` (p. 272, Proposition B.3; p. 110, proof of Theorem 2.75): `h*(Z)` is finite
almost surely and the real random variable `h*(Z)` is integrable. -/
def HasFiniteExpectedConj {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℝ)
    (Z : Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, fenchelConj h (Z ω) ≠ ⊤) ∧ Integrable (fun ω => (fenchelConj h (Z ω)).toReal) P

/-- The expectation `𝔼[h*(Z)]` of the conjugate evaluated at `Z`, as a real number. It is the
book's value whenever `HasFiniteExpectedConj P h Z` holds, which every theorem using it assumes
for the `Z` it ranges over. -/
noncomputable def expectedConj {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℝ)
    (Z : Ω → ℝ) : ℝ :=
  ∫ ω, (fenchelConj h (Z ω)).toReal ∂P

/-- The minimal loss functional (p. 107, §2.5.5, (2.109)),
`𝒟(Y) = min {𝔼[h(Y − a)] : a ∈ ℝ}`, for a non-negative convex loss `h` with `h(0) = 0`.
Rendered as an infimum in `[0, ∞]` of the lower Lebesgue integrals `∫⁻ h(Y − a) dP` (which equal
`𝔼[h(Y − a)]` for `h ≥ 0`, and are `+∞` when that expectation is infinite). The book's `min`
presupposes attainment, which fails e.g. for `h(v) = [v]⁺` and `Y` unbounded above; attainment
is not part of the definition. -/
noncomputable def minimalLoss {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℝ)
    (Y : Ω → ℝ) : ENNReal :=
  ⨅ a : ℝ, ∫⁻ ω, ENNReal.ofReal (h (Y ω - a)) ∂P

end RiskFunctionals.Deviation


