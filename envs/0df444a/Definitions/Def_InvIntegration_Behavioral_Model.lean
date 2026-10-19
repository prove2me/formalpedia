-- Prove2me | Definitions.Def_InvIntegration_Behavioral_Model
-- name    : InvIntegration_Behavioral_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:19.644119+00:00
-- url     : https://prove2.me/theorems/3429c1b2-0649-409b-aabd-99c852190fa8
-- title:
--   §3–§5.1, pp. 5–13 — two-period newsvendor with strategic consumers: normal markets, threshold valuation (1), profit (2), Π (3), fill rate, equilibrium (Definition 1), behavioral value (6)
-- statement:
--   This file sets up the base model of Aflaki and Swinney's *Inventory Integration with Rational Consumers* (§3–§5.1).
--
--   **Data.** A firm buys inventory at unit cost $c$ before a selling season of two periods, sells at the full price $p$ in period 1 and at the clearance price $s$ in period 2. Consumers have valuations $v$ with density $g$ supported on $(v_l, v_h)$ and distribution function $G(x)=\int_{-\infty}^{x} g$, $\bar G = 1-G$; a unit bought in period 2 is worth $\delta v$. The **standing assumptions** of §§3–5 are
--   $$s<c<p,\qquad 0<\delta\le 1,\qquad \delta p>s,\qquad v_l<p<v_h,\qquad \mu>0,$$
--   $g\ge 0$ integrable with $\int g = 1$, $g=0$ off $(v_l,v_h)$ and every nonempty subinterval of $(v_l,v_h)$ has positive probability, and $\hat z$ is the standard normal quantile with $\Phi(\hat z) = (p-c)/(p-s)$.
--
--   **Markets.** A market with mean $m$ and standard deviation $\mathrm{sd}$ has normal demand $D\sim N(m,\mathrm{sd}^2)$. The multichannel system is a market $N(\mu,\sigma^2)$ (both markets are identical); the integrated system is the market $N(2\mu, 2(1+\rho)\sigma^2)$, whose standard deviation is $\sqrt{2(1+\rho)}\,\sigma$.
--
--   **Objects.**
--   1. Threshold valuation (1): $v^*(\xi) = \min\bigl(v_h, \max\bigl(\tfrac{p-\xi s}{1-\xi\delta}, p\bigr)\bigr)$, equal to $v_h$ when $\xi\delta \ge 1$ (where the fraction is $+\infty$).
--   2. Profit (2) given the belief $\tilde v$: $\pi(q) = \mathbb E\bigl[(p-s)\min(q, \bar G(\tilde v)D) - (c-s)q\bigr]$.
--   3. Newsvendor profit (3): $\Pi(m,\mathrm{sd}) = (p-c)m - (p-s)\,\mathrm{sd}\,L(\hat z) - (c-s)\hat z\,\mathrm{sd}$ with $L(\hat z) = \int_{\hat z}^\infty (t-\hat z)\phi(t)\,dt$.
--   4. Second-period fill rate (the ratio adopted on p. 13):
--   $$\xi_2(q,v) = \frac{\mathbb E\bigl[\min\bigl((q-\bar G(v)D)^+,\ (G(v)-G(s/\delta))^+D\bigr)\bigr]}{(G(v)-G(s/\delta))^+\,m}.$$
--   5. Equilibrium (Definition 1, beliefs rational): $(q,v,\xi)$ with $q$ maximizing $\pi$ under the belief $\tilde v = v$, $v = v^*(\xi)$, and $\xi = \xi_2(q,v)$.
--   6. Behavioral value of integration, the second term of (6):
--   $$\frac{G(v^*_m)-G(v^*_I)}{\bar G(v^*_m)}\times\frac{\Pi\bigl(2\mu,\sqrt{2(1+\rho)}\,\sigma\bigr)}{2\Pi(\mu,\sigma)}.$$
--   7. $\sigma_{\max} = \mu(p-c)/\bigl((p-s)\phi(\hat z)\bigr)$, the positive root of $\sigma\mapsto\Pi(\mu,\sigma)$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note.** Two hypotheses are added to the page's: $v_l<p$ (footnote 4 claims $G(v^*)>G(s/\delta)$, which fails if $p\le v_l$), and $\delta>0$ made explicit ($G(s/\delta)$ is used on p. 8). The multichannel system is encoded as one market, taken once (symmetric by Proposition 3); the integrated demand is given by its law, as in Proposition 2 (ii). The fill rate keeps the sign of the normal demand, as in the paper's (14), so it can be negative. All integrands are continuous with linear growth and hence integrable against the Gaussian laws; for $\mathrm{sd}=0$ the demand law is the Dirac mass at $m$. Everything is in $\mathbb R$.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), pp. 5–13 (PDF 5–13), §3, §4, Definition 1, eqs. (1)–(6), p. 13 fill-rate convention

import Mathlib

namespace InvIntegration.Behavioral

open MeasureTheory ProbabilityTheory

/-- The primitive data of the base model of Aflaki & Swinney (§3, pp. 5–9): full price `p`, unit cost `c`,
clearance price `s`, depreciation factor `δ`, the support `(vl, vh)` and density `g` of consumer valuations,
the mean market size `μ`, and the newsvendor z-statistic `zh` (ẑ, with Φ(ẑ) = (p − c)/(p − s)).
The market standard deviation σ and the correlation ρ are not fields: the theorems vary them.

Conventions (disclosed): the multichannel system is represented by one market with demand law N(μ, σ²),
taken once, because the two markets are identically distributed and the equilibrium is symmetric
(Proposition 3); the integrated system is the market with demand law N(2μ, 2(1 + ρ)σ²), the law of
D₁ + D₂ that the paper uses in Proposition 2 (ii) and (6). The functions integrated in `profit` and in the
numerator of `fill2` are continuous and of linear growth, hence integrable against every Gaussian law, so
the Bochner integrals below are the genuine expectations. -/
structure Params where
  p : ℝ
  c : ℝ
  s : ℝ
  δ : ℝ
  vl : ℝ
  vh : ℝ
  μ : ℝ
  g : ℝ → ℝ
  zh : ℝ

/-- Valuation distribution function `G(x) = ∫_{(-∞, x]} g`. -/
noncomputable def G (P : Params) (x : ℝ) : ℝ := ∫ t in Set.Iic x, P.g t

/-- `Ḡ(x) = 1 − G(x)`. -/
noncomputable def Gbar (P : Params) (x : ℝ) : ℝ := 1 - G P x

/-- The standing assumptions of §§3–5 (pp. 5–9): `s < c < p` (p. 6); `δ ∈ (0, 1]` (p. 7, with `δ > 0`
made explicit because `G(s/δ)` is used on p. 8); `δp > s` and `vh > p` (p. 8); `vl < p` (added, needed by
footnote 4); `μ > 0`; `g` an integrable probability density supported throughout `(vl, vh)` (every
nonempty interior interval has positive mass); and `Φ(ẑ) = (p − c)/(p − s)` (p. 9). -/
def Params.Standing (P : Params) : Prop :=
  P.s < P.c ∧ P.c < P.p ∧
  0 < P.δ ∧ P.δ ≤ 1 ∧ P.s < P.δ * P.p ∧
  P.vl < P.p ∧ P.p < P.vh ∧ 0 < P.μ ∧
  Integrable P.g ∧ (∀ x, 0 ≤ P.g x) ∧
  (∀ x, x ∉ Set.Ioo P.vl P.vh → P.g x = 0) ∧
  (∀ a b : ℝ, P.vl < a → b < P.vh → a < b → 0 < ∫ t in Set.Ioo a b, P.g t) ∧
  ∫ t, P.g t = 1 ∧
  cdf (gaussianReal 0 1) P.zh = (P.p - P.c) / (P.p - P.s)

/-- The demand law N(m, sd²) of a market with mean `m` and standard deviation `sd`
(for `sd = 0` this is the Dirac law at `m`). -/
noncomputable def demandLaw (m sd : ℝ) : Measure ℝ := gaussianReal m (sd ^ 2).toNNReal

/-- The standard normal loss function `L(ẑ) = ∫_ẑ^∞ (t − ẑ) φ(t) dt` (p. 9). -/
noncomputable def lossN (P : Params) : ℝ :=
  ∫ t in Set.Ioi P.zh, (t - P.zh) * gaussianPDFReal 0 1 t

/-- `Π(m, sd) = (p − c)m − (p − s)·sd·L(ẑ) − (c − s)·ẑ·sd`, eq. (3), p. 9. -/
noncomputable def Pi (P : Params) (m sd : ℝ) : ℝ :=
  (P.p - P.c) * m - (P.p - P.s) * sd * lossN P - (P.c - P.s) * P.zh * sd

/-- Firm's expected profit (2), p. 9, in a market with demand law N(m, sd²), when the firm believes the
critical valuation is `vt` and stocks `q`:
`E[(p − s) min(q, Ḡ(vt) D) − (c − s) q]`. -/
noncomputable def profit (P : Params) (m sd vt q : ℝ) : ℝ :=
  ∫ x, ((P.p - P.s) * min q (Gbar P vt * x) - (P.c - P.s) * q) ∂ demandLaw m sd

/-- The critical valuation map (1), p. 8: `v*(ξ) = min(vh, max((p − ξs)/(1 − ξδ), p))`.
When `ξδ ≥ 1` the page's fraction is `+∞` (at `ξ = δ = 1`), and the value is `vh`. -/
noncomputable def vstar (P : Params) (ξ : ℝ) : ℝ :=
  if 1 ≤ ξ * P.δ then P.vh else min P.vh (max ((P.p - ξ * P.s) / (1 - ξ * P.δ)) P.p)

/-- Second-period fill rate as adopted on p. 13: `E[period-2 sales] / E[period-2 demand]`, where
period-2 demand is `(G(v) − G(s/δ))⁺ D`, the inventory left for period 2 is `(q − Ḡ(v) D)⁺`, and
period-2 sales are their minimum (the sign of the normal demand `D` is kept, as in (14)). -/
noncomputable def fill2 (P : Params) (m sd q v : ℝ) : ℝ :=
  let d2 := max (G P v - G P (P.s / P.δ)) 0
  (∫ x, min (max (q - Gbar P v * x) 0) (d2 * x) ∂ demandLaw m sd) / (d2 * m)

/-- Definition 1, p. 10, in a market with demand law N(m, sd²), with the rational-belief clauses 3
(`ṽ = v`) and 4 (`ξ̃ = ξ(q, v)`) substituted: `q` maximizes the profit given the belief `v`, `v` is the
consumers' critical valuation (1) given the belief `ξ`, and `ξ` is the actual second-period fill rate. -/
def IsEquilibrium (P : Params) (m sd q v ξ : ℝ) : Prop :=
  (∀ q' : ℝ, profit P m sd v q' ≤ profit P m sd v q) ∧ v = vstar P ξ ∧ ξ = fill2 P m sd q v

/-- Standard deviation `√(2(1 + ρ)) σ` of the integrated demand `D₁ + D₂`. -/
noncomputable def sdI (σ ρ : ℝ) : ℝ := Real.sqrt (2 * (1 + ρ)) * σ

/-- The behavioral value of integration, the second term of (6), p. 12:
`(G(v*m) − G(v*I))/Ḡ(v*m) × Π(2μ, √(2(1 + ρ))σ)/(2Π(μ, σ))`. -/
noncomputable def behavioralValue (P : Params) (σ ρ vm vI : ℝ) : ℝ :=
  (G P vm - G P vI) / Gbar P vm * (Pi P (2 * P.μ) (sdI σ ρ) / (2 * Pi P P.μ σ))

/-- `σ_max = μ(p − c)/((p − s)φ(ẑ))`, the positive root of `σ ↦ Π(μ, σ)`. -/
noncomputable def sigmaMax (P : Params) : ℝ :=
  P.μ * (P.p - P.c) / ((P.p - P.s) * gaussianPDFReal 0 1 P.zh)

end InvIntegration.Behavioral


