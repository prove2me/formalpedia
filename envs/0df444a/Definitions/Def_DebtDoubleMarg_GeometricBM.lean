-- Prove2me | Definitions.Def_DebtDoubleMarg_GeometricBM
-- name    : DebtDoubleMarg_GeometricBM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:12.036017+00:00
-- url     : https://prove2.me/theorems/6d3dd9a9-c4b2-420d-9f88-85140e26eff2
-- title:
--   Geometric Brownian motion, its first passage from below, the discount factor $e^{-r\tilde\tau}$ and the root $\beta_1$
-- statement:
--   Let $W=(W_t)_{t\ge0}$ be a real process on a probability space $(\Omega,\mathcal F,P)$ (a standard Brownian motion in every theorem of this mission), and let $\mu,\sigma,r\in\mathbb R$.
--
--   1. **Geometric Brownian motion.** For an initial level $X$,
--   $$x^X(t,\omega)=X\exp\Big(\big(\mu-\tfrac{\sigma^2}{2}\big)t+\sigma W_t(\omega)\Big),\qquad t\ge0,$$
--   the solution of $dx=\mu x\,dt+\sigma x\,dW$ with $x(0)=X$.
--   2. **First passage from below.** For a level $\tilde X$,
--   $$\tilde\tau(\tilde X;X)(\omega)=\inf\{t\ge0 : x^X(t,\omega)\ge\tilde X\}\in[0,\infty],$$
--   with $\inf\emptyset=\infty$.
--   3. **Discount factor** $D(\tilde X;X)=e^{-r\tilde\tau(\tilde X;X)}$, set to $0$ on $\{\tilde\tau=\infty\}$, and its expectation $\mathbb E[D(\tilde X;X)]=\int_\Omega D\,dP$.
--   4. **The root $\beta_1$**, the larger root of $\tfrac12\sigma^2\beta^2+(\mu-\tfrac12\sigma^2)\beta-r=0$, written by the quadratic formula:
--   $$\beta_1=\frac12-\frac{\mu}{\sigma^2}+\sqrt{\Big(\frac{\mu}{\sigma^2}-\frac12\Big)^2+\frac{2r}{\sigma^2}}.$$
--
--   These are the demand process of §2.1, the hitting time of §2.3 and the discount factor of the timing problems (2), $V_F$ and $V_D$ (p.6), and the constant $\beta_1$ of Proposition 1 (p.7). The expected discount factor is the source of every factor $(X/X_F)^{\beta_1}$ in the paper.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$, the index set of Mathlib's `IsBrownianReal`. The hitting time is an infimum in $[0,\infty]$ taken path by path. The formula for $\beta_1$ is meaningful for $\sigma\ne0$; that it is the larger root is proved in the goal theorem, not assumed.
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.1 p.4 (gBm), §2.3 p.6 (τ̃ and (2)), Proposition 1 p.7 (β₁)

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **The larger root `β₁` of the fundamental quadratic** `½σ²β² + (µ − ½σ²)β − r = 0`,
written by the quadratic formula:
`β₁ = ½ − µ/σ² + √((µ/σ² − ½)² + 2r/σ²)`.

Huberts, Wen, Dawid, Huisman, Kort, *Double Marginalization Because of External Financing:
Capacity Investment Under Uncertainty*, Management Science (2025), doi:10.1287/mnsc.2023.01152,
Proposition 1, p.7 ("β1 > 1 is the larger root of ½σ²β² + (µ − ½σ²)β − r = 0").

**Formalization Note** The formula is the `+` branch of the quadratic formula after dividing by
`½σ²`; it is meaningful for `σ ≠ 0`, and the theorems of this mission assume `σ > 0`, `r > 0`,
under which the discriminant is positive. That it is a root, the larger one, and exceeds `1`
(when `r > µ`) is asserted by the goal theorem, not assumed here. -/
noncomputable def beta1 (μ σ r : ℝ) : ℝ :=
  1 / 2 - μ / σ ^ 2 + Real.sqrt ((μ / σ ^ 2 - 1 / 2) ^ 2 + 2 * r / σ ^ 2)

/-- **Geometric Brownian motion started at `X`**: given a real process `W` (a standard Brownian
motion in every theorem of this mission),
`x^X(t, ω) = X · exp((µ − σ²/2) t + σ W_t(ω))`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.1, p.4:
"dx(t) = µx(t)dt + σx(t)dω(t)", "denote by X the initial value of the demand level (i.e.,
X = x(0) > 0)".

**Formalization Note** The stochastic differential equation is encoded by its unique strong
solution, the explicit exponential above. Time is `ℝ≥0`, the index set of Mathlib's
`ProbabilityTheory.IsBrownianReal`. The same `W` drives every initial level `X`. -/
noncomputable def gbm (μ σ : ℝ) {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (X : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  X * Real.exp ((μ - σ ^ 2 / 2) * (t : ℝ) + σ * W t ω)

/-- **First passage from below**
`τ̃(X̃; X)(ω) = inf {t ≥ 0 | x^X(t, ω) ≥ X̃} ∈ [0, ∞]`, with `inf ∅ = ∞`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3, p.6: "Define
function τ̃(X̃;X) = inf{t ≥ 0|x(t) ≥ X̃; x(0) = X} (i.e., the first time that gBm process x(t)
hits X̃ from below)".

**Formalization Note** The infimum is taken pathwise in `ℝ≥0∞`, so a path that never reaches
`X̃` has `τ̃ = ∞` (`⊤`). -/
noncomputable def firstPassageUp (μ σ : ℝ) {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (Xt X : ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : Xt ≤ gbm μ σ W X t ω), (t : ℝ≥0∞)

/-- **Discount factor at the first passage** `e^{−r τ̃(X̃; X)}`, equal to `0` on the event
`τ̃ = ∞`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (2), p.6: the factor
`e^{−r τ̃(X_F; x(0))}` of the firm's timing problem and of `V_F`, `V_D`.

**Formalization Note** `e^{−r·∞} = 0` for `r > 0`, which is the convention used here: if the
level is never reached, nothing is ever received. -/
noncomputable def passageDiscount (μ σ r : ℝ) {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (Xt X : ℝ)
    (ω : Ω) : ℝ :=
  if firstPassageUp μ σ W Xt X ω < ⊤ then
    Real.exp (-(r * (firstPassageUp μ σ W Xt X ω).toReal))
  else 0

/-- **Expected discount factor** `E₀[e^{−r τ̃(X̃; X)}]`, the Bochner integral of
`passageDiscount` against `P`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (2), p.6 and `V_F`,
`V_D`, p.6.

**Formalization Note** The integrand takes values in `[0, 1]`; its integrability is a property
of `W` (a.s. continuous paths make it a.e. measurable), proved in the theorems, not assumed. -/
noncomputable def expectedPassageDiscount (μ σ r : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (Xt X : ℝ) : ℝ :=
  ∫ ω, passageDiscount μ σ r W Xt X ω ∂P

end DebtDoubleMarg


