-- Prove2me | Definitions.Def_SinglePointPricing_Det_Setting
-- name    : SinglePointPricing_Det_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:19.841158+00:00
-- url     : https://prove2.me/theorems/48e78761-40a3-4cbb-83e6-c6c1e1afbcea
-- title:
--   §2–§3, pp. 8–14, 22 — value laws G, ccdf F̄(p) = P(v ≥ p), opt(F), R(Ψ,F), R(P′,F), P_d, Γ_α, α-strong regularity, F_α(w,q), Lambert W, β_q, ρ
-- statement:
--   The model of Allouah, Bahamou and Besbes: one seller, one buyer, one good. The buyer's value $v \ge 0$ has a law $F$ unknown to the seller.
--
--   1. **Value laws.** A value law is a probability measure $\mu$ on $\mathbb R$ with $\mu((-\infty,0)) = 0$. Its **ccdf** is $\overline F(p) = \mu([p,\infty)) = P(v \ge p)$. The class $\mathcal G$ of (2.2) consists of the value laws with $0 < \mathbb E[v] < \infty$.
--   2. **Revenue and oracle.** Posting the price $p$ earns $\mathrm{Rev}(p\mid \overline F) = p\,\overline F(p)$, and the oracle revenue (2.1) is
--   $$\mathrm{opt}(F) = \sup_{p \ge 0} p\,\overline F(p).$$
--   3. **Mechanisms.** A mechanism is a law $\Psi$ of posted prices on $[0,\infty)$; $\mathcal P_d = \{\delta_\gamma : \gamma \ge 0\}$ are the deterministic ones. The performance of $\Psi$ against $F$ is $R(\Psi,F) = \int \mathrm{Rev}(p\mid\overline F)\,d\Psi(p) / \mathrm{opt}(F)$, and the maximin ratio of a class $\mathcal P'$ against a class $\mathcal F$ is
--   $$\mathcal R(\mathcal P',\mathcal F) = \sup_{\Psi\in\mathcal P'}\ \inf_{F\in\mathcal F} R(\Psi,F).$$
--   4. **Generalized Pareto tails.** $\Gamma_\alpha(v) = (1+(1-\alpha)v)^{-1/(1-\alpha)}$ for $\alpha\in[0,1)$ and $\Gamma_1(v) = e^{-v}$; $\Gamma_\alpha^{-1}(q) = (q^{-(1-\alpha)}-1)/(1-\alpha)$, resp. $-\log q$, is its inverse on $(0,1]$.
--   5. **α-strong regularity** ($\alpha = 0$: regular; $\alpha = 1$: monotone hazard rate): $\Gamma_\alpha^{-1}\circ\overline F$ is convex on $\{v \ge 0 : \overline F(v) > 0\}$. The class of the paper is
--   $$\mathcal F_\alpha(w,q) = \{F \in \mathcal G : F \text{ is } \alpha\text{-strongly regular},\ \overline F(w) = q\}.$$
--   6. **Lambert function and the constants of Theorem 2.** $W(x)$ is the unique $w \ge 0$ with $we^w = x$ ($x \ge 0$); $\beta_q(x) = 1 - \frac{1}{\log(q^{-1})}\big(W(x) + \frac1{W(x)} - 2\big)$ and $\rho(q) = \beta_q\big(\tfrac1{\log(q^{-1})}\big)\, e \log(q^{-1})\, e^{-\log(q^{-1})\beta_q(1/\log(q^{-1}))}$.
--
--   These are the objects of the goal theorem (Theorem 2) and of the fundamental reduction (Theorem 1).
--
--   **Formalization Note** The ccdf is the closed tail $\mu([p,\infty))$: the paper's data is the fraction of values *greater than or equal to* $w$ (p. 2) and its revenue is $\int p\,\mathbf 1\{v\ge p\}\,dF$ (p. 9); this matters at atoms, which the worst cases have. α-strong regularity is stated as convexity of $\Gamma_\alpha^{-1}\circ\overline F$, which is equivalent to the paper's density form (non-decreasing $(1-\alpha)v - \overline F(v)/f(v)$; the "non-increasing" printed on p. 11 is a slip) and, like the paper, allows an atom at the top of the support; no absolute continuity is imposed. Suprema and infima are `sSup`/`sInf` on ℝ; the sets they are applied to in the mission are nonempty and bounded. For $x<0$, `lambertW` returns the junk value 0, never used.
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, §2, pp. 8–11 (eqs. (2.1), (2.2), α-strong regularity, F_α(w, I)); §3, p. 13 (Γ_α); Theorem 2, p. 22 (W, β_q, ρ)

import Mathlib

namespace SinglePointPricing.Det

noncomputable section

open MeasureTheory

/-- §2, p. 9: the complementary cumulative distribution function `F̄(p) = P(v ≥ p)` of a value law
`μ` on `ℝ`, taken as the **closed** tail `μ([p, ∞))` (p. 2: "values … greater than or equal to w";
p. 9: `Rev(p|F̄) = ∫ p 1{v ≥ p} dF(v) = p F̄(p)`). -/
def sf (μ : Measure ℝ) (p : ℝ) : ℝ := (μ (Set.Ici p)).toReal

/-- (2.2), p. 10: the class `G` of value laws: probability measures supported in `[0, ∞)` with
finite and non-zero expectation (the data constraint `F̄(w) ∈ I` is added in `FClass`). -/
def InG (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ Integrable (fun v : ℝ => v) μ ∧ 0 < ∫ v, v ∂μ

/-- (2.1), p. 9: the oracle revenue `opt(F) = sup_{p ≥ 0} p F̄(p)`. -/
def opt (μ : Measure ℝ) : ℝ := sSup ((fun p : ℝ => p * sf μ p) '' Set.Ici 0)

/-- p. 13: `Γ_α(v) = (1 + (1 − α) v)^{−1/(1−α)}` for `α ∈ [0, 1)` and `e^{−v}` for `α = 1`. -/
def GammaA (α v : ℝ) : ℝ :=
  if α = 1 then Real.exp (-v) else (1 + (1 - α) * v) ^ (-(1 / (1 - α)))

/-- p. 13: the inverse `Γ_α^{−1}` of `Γ_α`, on `(0, 1]`: `(q^{−(1−α)} − 1)/(1 − α)` for `α ∈ [0, 1)`
and `−log q` for `α = 1`. (Only used at arguments in `(0, 1]`; the paper's `Γ_α^{−1}(0) = +∞` never
arises.) -/
def GammaAInv (α q : ℝ) : ℝ :=
  if α = 1 then -Real.log q else (q ^ (-(1 - α)) - 1) / (1 - α)

/-- p. 11 and App. A, p. App-1: `α`-strong regularity, stated as convexity of `Γ_α^{−1} ∘ F̄` on
`{v ≥ 0 | F̄(v) > 0}`. This is equivalent to the paper's density form (positive density on the
support except possibly an atom at its maximum, `(1 − α)v − F̄(v)/f(v)` non-decreasing); no absolute
continuity is required, so an atom at the top of the support is allowed, as on p. 11. -/
def IsAlphaSR (α : ℝ) (μ : Measure ℝ) : Prop :=
  ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} (fun v => GammaAInv α (sf μ v))

/-- p. 11: `F_α(w, q) = {F ∈ G(w, {q}) : F is α-strongly regular}`, the α-strongly regular value
laws with conversion rate `F̄(w) = q` at the price `w`. -/
def FClass (α w q : ℝ) : Set (Measure ℝ) :=
  {μ | InG μ ∧ IsAlphaSR α μ ∧ sf μ w = q}

/-- p. 9: the class `P` of (randomized) pricing mechanisms: laws of posted prices on `[0, ∞)`. -/
def IsMech (Ψ : Measure ℝ) : Prop :=
  IsProbabilityMeasure Ψ ∧ Ψ (Set.Iio 0) = 0

/-- p. 10: the deterministic mechanisms `P_d = {δ_γ : γ ≥ 0}`. -/
def Pd : Set (Measure ℝ) := {Ψ | ∃ γ : ℝ, 0 ≤ γ ∧ Ψ = Measure.dirac γ}

/-- p. 9: the performance `R(Ψ, F) = ∫ Rev(p|F̄) dΨ(p) / opt(F)` of the mechanism `Ψ` against `F`. -/
def ratio (Ψ μ : Measure ℝ) : ℝ := (∫ p, p * sf μ p ∂Ψ) / opt μ

/-- p. 10: the maximin ratio `R(P′, 𝓕) = sup_{Ψ ∈ P′} inf_{F ∈ 𝓕} R(Ψ, F)`. -/
def maximin (P' 𝓕 : Set (Measure ℝ)) : ℝ :=
  sSup ((fun Ψ => sInf (ratio Ψ '' 𝓕)) '' P')

/-- p. 22: the Lambert function `W`, the inverse of `x ↦ x e^x` on `[0, +∞)`: for `x ≥ 0`,
`lambertW x` is the unique `w ≥ 0` with `w e^w = x` (junk value `0` for `x < 0`). -/
def lambertW (x : ℝ) : ℝ :=
  open Classical in
  if h : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = x then Classical.choose h else 0

/-- p. 22: `β_q(x) = 1 − (1/log(q^{−1})) (W(x) + 1/W(x) − 2)`. -/
def betaQ (q x : ℝ) : ℝ :=
  1 - (lambertW x + 1 / lambertW x - 2) / Real.log q⁻¹

/-- p. 22: `ρ(q) = β_q(1/log(q^{−1})) e log(q^{−1}) e^{−log(q^{−1}) β_q(1/log(q^{−1}))}`. -/
def rhoQ (q : ℝ) : ℝ :=
  betaQ q (1 / Real.log q⁻¹) * Real.exp 1 * Real.log q⁻¹ *
    Real.exp (-(Real.log q⁻¹) * betaQ q (1 / Real.log q⁻¹))

end

end SinglePointPricing.Det


