-- Prove2me | Definitions.Def_DataDrivenNV_WMS_Setting
-- name    : DataDrivenNV_WMS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:05:14.505127+00:00
-- url     : https://prove2.me/theorems/92e8c0fe-049c-4e87-b56c-3f0551a93a21
-- title:
--   §2–§4, pp. 7–16 — densities, cdf, b/(b+h) quantile q*, absolute mean spread Δ, supergradient of log f, the extremal density (12) and z* of (11)
-- statement:
--   This file fixes the objects of §3–§4 of Levi, Perakis and Uichanco for a demand $D$ with a density.
--
--   1. A **probability density function** is a measurable $f:\mathbb R\to\mathbb R$ with $f\ge 0$ everywhere, $f$ integrable and $\int_{\mathbb R} f(x)\,dx = 1$.
--   2. Its **cdf** is $F(t)=\int_{(-\infty,t]} f(x)\,dx$.
--   3. For $\beta\in(0,1)$ the **$\beta$ quantile** is
--   $$q^* = \inf\{q\in\mathbb R : F(q)\ge \beta\};$$
--   the paper uses $\beta=b/(b+h)$, the newsvendor critical ratio (§2, p. 7).
--   4. The **absolute mean spread** (Definition 1, p. 10) at $t$ is
--   $$\Delta(t)=E(D\mid D\ge t)-E(D\mid D\le t)=\frac{\int_{[t,\infty)} x f(x)\,dx}{1-F(t)}-\frac{\int_{(-\infty,t]} x f(x)\,dx}{F(t)} .$$
--   The **weighted mean spread** (Definition 2, p. 11) is $\Delta(q^*)f(q^*)$; it is written out directly in the theorems.
--   5. $\gamma_1\in\partial\log f(t)$ (§4.1, p. 14) means that $\gamma_1$ is a supergradient at $t$ of the concave function $\log f$ on its domain $\{f>0\}$:
--   $$\log f(x)\le \log f(t)+\gamma_1(x-t)\quad\text{for every } x \text{ with } f(x)>0 .$$
--   6. For $\gamma_0>0$, $\gamma_1\neq 0$, the **extremal density** (12), p. 15, is
--   $$\tilde f(x)=\gamma_0 e^{\gamma_1(x-q)}\ \text{ on } [\underline x,\overline x],\qquad \tilde f(x)=0 \text{ elsewhere},$$
--   with $\underline x = q+\frac1{\gamma_1}\log\!\big(1-\frac{\gamma_1}{\gamma_0}\frac{b}{b+h}\big)$ and $\overline x = q+\frac1{\gamma_1}\log\!\big(1+\frac{\gamma_1}{\gamma_0}\frac{h}{b+h}\big)$.
--   7. The **optimal value of problem (11)** in the case $\gamma_1/\gamma_0\in(-\frac{b+h}{h},\frac{b+h}{b})$ (proof of Proposition 2, p. 16) is
--   $$z^*=\frac{\gamma_0}{\gamma_1^2}\Big[\Big(\frac{b+h}{h}+\frac{\gamma_1}{\gamma_0}\Big)\log\Big(1+\frac{\gamma_1}{\gamma_0}\frac{h}{b+h}\Big)+\Big(\frac{b+h}{b}-\frac{\gamma_1}{\gamma_0}\Big)\log\Big(1-\frac{\gamma_1}{\gamma_0}\frac{b}{b+h}\Big)\Big].$$
--
--   These objects are shared by every statement of the mission: Lemmas 1–4, Propositions 1–2 and the closed form of $z^*$.
--
--   **Formalization Note** Log-concavity (Definition 3, p. 13) is the published `ConvexOptimization.LogConcaveOn Set.univ f` (power form $f(x)^a f(y)^{1-a}\le f(ax+(1-a)y)$, which permits zeros), not concavity of `Real.log ∘ f`, which would read $\log 0$ as $0$. The paper writes "subgradients" of the concave function $\log f$; the superdifferential is meant and is what is encoded. The conditional means are ratios of integrals; the denominators $F(t)$ and $1-F(t)$ are positive at the $\beta$ quantile for $\beta\in(0,1)$, and theorems with a free point $t$ assume $0<F(t)<1$. The quantile is an `sInf`; for a pdf and $\beta\in(0,1)$ the set is nonempty and bounded below, so it is the true infimum, and $F(q^*)=\beta$ by continuity of $F$. The endpoints of (12) and $z^*$ are defined by the printed formulas; they are used only for $\gamma_1\neq0$ and $\gamma_1/\gamma_0$ in the open interval, where every logarithm has a positive argument and every division a nonzero denominator.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 7 (q*), p. 10 Definition 1, p. 11 Definition 2, p. 13 Definition 3, p. 14 §4.1 and (11), p. 15 (12), p. 16 (z* in the proof of Proposition 2)

import Mathlib
import Definitions.Def_LogConcaveOn

namespace DataDrivenNV.WMS

open MeasureTheory

/-- `f : ℝ → ℝ` is a probability density function: measurable, nonnegative everywhere,
integrable, with total mass `1`. -/
def IsPdf (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f ∧ ∫ x, f x = 1

/-- The cdf of the density `f`: `F(t) = ∫_{(-∞, t]} f(x) dx`. -/
noncomputable def cdfOf (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Set.Iic t, f x

/-- The `β` quantile of the density `f` (§2, p. 7, with `β = b/(b+h)`):
`q* = inf { q : F(q) ≥ β }`. For a pdf and `0 < β < 1` the set is nonempty and bounded below,
so this is the true infimum. -/
noncomputable def quantileOf (f : ℝ → ℝ) (β : ℝ) : ℝ :=
  sInf {q : ℝ | β ≤ cdfOf f q}

/-- The absolute mean spread (Definition 1, p. 10) of the law with density `f` at `t`:
`Δ(t) = E(D | D ≥ t) − E(D | D ≤ t)`, each conditional mean written as a ratio of integrals
(`P(D ≥ t) = 1 − F(t)` since the law has a density). -/
noncomputable def ams (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ x in Set.Ici t, x * f x) / (1 - cdfOf f t) - (∫ x in Set.Iic t, x * f x) / cdfOf f t

/-- `γ₁ ∈ ∂ log f(t)` (§4.1, p. 14): `γ₁` is a supergradient of the concave function `log f` at `t`,
on its domain `{x | f x > 0}`: `log f(x) ≤ log f(t) + γ₁ (x − t)` whenever `f(x) > 0`. -/
def IsLogSupergradient (f : ℝ → ℝ) (t γ₁ : ℝ) : Prop :=
  ∀ x, 0 < f x → Real.log (f x) ≤ Real.log (f t) + γ₁ * (x - t)

/-- The left endpoint `x̲ = q + (1/γ₁) log(1 − (γ₁/γ₀)(b/(b+h)))` of (12), p. 15. -/
noncomputable def tildeLo (b h q γ₀ γ₁ : ℝ) : ℝ :=
  q + 1 / γ₁ * Real.log (1 - γ₁ / γ₀ * (b / (b + h)))

/-- The right endpoint `x̄ = q + (1/γ₁) log(1 + (γ₁/γ₀)(h/(b+h)))` of (12), p. 15. -/
noncomputable def tildeHi (b h q γ₀ γ₁ : ℝ) : ℝ :=
  q + 1 / γ₁ * Real.log (1 + γ₁ / γ₀ * (h / (b + h)))

/-- The extremal density (12), p. 15: `f̃(x) = γ₀ e^{γ₁ (x − q)}` on `[x̲, x̄]`, and `0` elsewhere. -/
noncomputable def tildeF (b h q γ₀ γ₁ : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc (tildeLo b h q γ₀ γ₁) (tildeHi b h q γ₀ γ₁))
    (fun x => γ₀ * Real.exp (γ₁ * (x - q)))

/-- The optimal value `z*_{q*,γ₀,γ₁}` of problem (11) in the case
`γ₁/γ₀ ∈ (−(b+h)/h, (b+h)/b)` (proof of Proposition 2, p. 16). -/
noncomputable def zStar (b h γ₀ γ₁ : ℝ) : ℝ :=
  γ₀ / γ₁ ^ 2 *
    (((b + h) / h + γ₁ / γ₀) * Real.log (1 + γ₁ / γ₀ * (h / (b + h))) +
      ((b + h) / b - γ₁ / γ₀) * Real.log (1 - γ₁ / γ₀ * (b / (b + h))))

end DataDrivenNV.WMS


