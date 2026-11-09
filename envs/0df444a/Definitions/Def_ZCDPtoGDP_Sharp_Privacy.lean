-- Prove2me | Definitions.Def_ZCDPtoGDP_Sharp_Privacy
-- name    : ZCDPtoGDP_Sharp_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:46:38.403817+00:00
-- url     : https://prove2.me/theorems/e62f170d-381c-4e45-9592-0606b04804f2
-- title:
--   §2 — Rényi divergence, zCDP, tests, trade-off functions, $G_\mu$, GDP and randomized response
-- statement:
--   A **mechanism** is a Markov kernel $M$ from an input measurable space $X$ to an output measurable space $(\Omega,\mathcal F)$, together with a symmetric neighbouring relation $\sim$ on $X$. For neighbouring inputs write $P=M(x)$ and $Q=M(x')$.
--
--   1. **Rényi divergence.** For probability measures $P,Q$ on $\Omega$, let $\nu=P+Q$ and $p=dP/d\nu$, $q=dQ/d\nu$. For an order $\eta>1$,
--   $$D_\eta(P\|Q)=\frac{1}{\eta-1}\log\int_\Omega p^\eta q^{1-\eta}\,d\nu\in[0,+\infty].$$
--   The integrand is evaluated with the convention $0^{1-\eta}=+\infty$, so $D_\eta(P\|Q)=+\infty$ whenever $P$ is not absolutely continuous with respect to $Q$.
--   2. **Zero-concentrated DP** (Definition 2). $M$ is $\rho$-zCDP if $D_\eta(M(x)\|M(x'))\le\rho\eta$ for every neighbouring pair $x\sim x'$ and every $\eta>1$.
--   3. **Tests and the trade-off function.** A test is a measurable $\phi:\Omega\to[0,1]$; its type I error is $\mathbb E_P\phi$ and its power $\mathbb E_Q\phi$. For $\alpha\in[0,1]$,
--   $$T(P,Q)(\alpha)=\inf\{1-\mathbb E_Q\phi:\ \phi\text{ a test},\ \mathbb E_P\phi\le\alpha\}.$$
--   4. **Gaussian curve.** With $\Phi$ the standard normal CDF and $\Phi^{-1}$ its inverse on $(0,1)$, $G_\mu(\alpha)=\Phi(\Phi^{-1}(1-\alpha)-\mu)$ for $\alpha\in(0,1)$, and $G_\mu(0)=1$, $G_\mu(1)=0$ (the conventions $\Phi^{-1}(1)=+\infty$, $\Phi^{-1}(0)=-\infty$).
--   5. **Gaussian DP** (Definition 3). $M$ is $\mu$-GDP if $T(M(x),M(x'))(\alpha)\ge G_\mu(\alpha)$ for every $x\sim x'$ and every $\alpha\in[0,1]$.
--   6. **Randomized response.** $\mathrm{Bern}(p)$ is the law on $\{0,1\}$ with mass $p$ at $1$. For $t\ge0$, $\mathrm{RR}_t$ maps $\{0,1\}$ to $\{0,1\}$, outputting its input with probability $\sigma(t)=(1+e^{-t})^{-1}$ and the other bit with probability $\sigma(-t)$, so $\mathrm{RR}_t(0)=\mathrm{Bern}(\sigma(-t))$ and $\mathrm{RR}_t(1)=\mathrm{Bern}(\sigma(t))$. Its neighbouring relation is $0\sim1$.
--
--   These are the objects compared by the sharp zCDP-to-GDP conversion: zCDP bounds Rényi divergences at every order, GDP bounds every hypothesis test by the Gaussian curve.
--
--   **Formalization Note** The Rényi divergence is valued in `EReal`, with a lower Lebesgue integral of an $[0,\infty]$-valued integrand, so no non-integrable integral defaults to $0$. $\{0,1\}$ is `Bool` with `true` $=1$. The trade-off infimum is a real infimum over a set that is nonempty for $\alpha\ge0$ (it contains $\phi\equiv0$) and bounded below by $0$. $\Phi^{-1}(p)$ is $\inf\{x:p\le\Phi(x)\}$, the true inverse on $(0,1)$; it is only used on $(0,1)$. $\mathrm{Bern}(p)$ is a probability measure for $p\in[0,1]$, the only arguments it receives.
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, §2: model p. 4, Rényi divergence p. 4, Definition 2 p. 4, tests and trade-off function pp. 4–5, G_μ and Definition 3 p. 5, §2.2 randomized response p. 5; endpoint conventions Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞, p. 13

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-! # §2 of Chen–Pandey–Awan: zCDP, trade-off functions, GDP and randomized response

Source: Chen, Pandey, Awan, *Optimal Conversion from Zero-Concentrated to Gaussian
Differential Privacy*, STOC 2027 submission #235, §2, pp. 4–5; endpoint conventions p. 13. -/

/-- Rényi divergence of order `η` (p. 4):
`D_η(P‖Q) = (η-1)⁻¹ log ∫ p^η q^{1-η} dν`, with `ν = P + Q` and `p, q` the
Radon–Nikodym densities of `P, Q` with respect to `ν`.  The integrand is computed in
`ℝ≥0∞`, so `0 ^ (1 - η) = ∞` for `η > 1`: for probability measures the integral,
hence `D_η`, is `+∞` whenever `P` is not absolutely continuous w.r.t. `Q`.
It can also be `+∞` when `P ≪ Q`, if the positive likelihood-ratio moment diverges.
The value lies in `EReal`; the real factor `(η - 1)⁻¹` is positive for `η > 1`. -/
noncomputable def renyiDiv {Ω : Type*} [MeasurableSpace Ω] (η : ℝ) (P Q : Measure Ω) : EReal :=
  (((η - 1)⁻¹ : ℝ) : EReal) *
    ENNReal.log (∫⁻ ω, (P.rnDeriv (P + Q) ω) ^ η * (Q.rnDeriv (P + Q) ω) ^ (1 - η) ∂(P + Q))

/-- Definition 2 (p. 4): `M` is `ρ`-zCDP for the neighbouring relation `adj` if for every
ordered neighbouring pair `x ∼ x'` and every order `η > 1`, `D_η(M x ‖ M x') ≤ ρ η`. -/
def IsZCDP {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] (adj : X → X → Prop)
    (M : Kernel X Ω) (ρ : ℝ) : Prop :=
  ∀ x x', adj x x' → ∀ η : ℝ, 1 < η → renyiDiv η (M x) (M x') ≤ ((ρ * η : ℝ) : EReal)

/-- A (randomized) test (p. 4): a measurable `φ : Ω → [0,1]`, rejecting with probability
`φ ω`.  Its type I error is `∫ φ dP` and its power `∫ φ dQ`. -/
def IsTest {Ω : Type*} [MeasurableSpace Ω] (φ : Ω → ℝ) : Prop :=
  Measurable φ ∧ ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1

/-- Trade-off function (pp. 4–5): `T(P,Q)(α) = inf {1 - E_Q φ : φ a test, E_P φ ≤ α}`.
For `α ≥ 0` the index set contains `φ ≡ 0`, and for a probability measure `Q` every value
is `≥ 0`, so the real infimum is the true infimum.  It is only used for `α ∈ [0,1]`. -/
noncomputable def tradeOff {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) (α : ℝ) : ℝ :=
  ⨅ φ : {φ : Ω → ℝ // IsTest φ ∧ ∫ ω, φ ω ∂P ≤ α}, (1 - ∫ ω, φ.1 ω ∂Q)

/-- The standard normal CDF `Φ`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard normal quantile `Φ⁻¹`, as the (generalized) inverse
`Φ⁻¹(p) = inf {x : p ≤ Φ x}`.  Since `Φ` is a continuous strictly increasing bijection
`ℝ → (0,1)`, for `p ∈ (0,1)` this is the unique `x` with `Φ x = p`.  Outside `(0,1)` the
value is not meaningful; every use below is either restricted to `(0,1)` or replaced by the
paper's endpoint conventions `Φ⁻¹(0) = -∞`, `Φ⁻¹(1) = +∞` (p. 13). -/
noncomputable def stdNormalQuantile (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ stdNormalCDF x}

/-- The Gaussian trade-off curve `G_μ(α) = Φ(Φ⁻¹(1 - α) - μ)` (p. 5), with the endpoint
values `G_μ(0) = 1` and `G_μ(1) = 0` given by the conventions `Φ⁻¹(1) = +∞`, `Φ⁻¹(0) = -∞`,
`Φ(±∞) ∈ {1, 0}` (p. 13).  (Values for `α ∉ [0,1]` are never used.) -/
noncomputable def gaussTradeOff (μ α : ℝ) : ℝ :=
  if α ≤ 0 then 1 else if 1 ≤ α then 0 else stdNormalCDF (stdNormalQuantile (1 - α) - μ)

/-- Definition 3 (p. 5): `M` is `μ`-GDP if for every neighbouring `x ∼ x'` and every
`α ∈ [0,1]`, `T(M x, M x')(α) ≥ G_μ(α)`. -/
def IsGDP {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] (adj : X → X → Prop)
    (M : Kernel X Ω) (μ : ℝ) : Prop :=
  ∀ x x', adj x x' → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    gaussTradeOff μ α ≤ tradeOff (M x) (M x') α

/-- `Bern(p)` on `{0,1} = Bool` (`true` = 1): mass `p` at `true` and `1 - p` at `false`.
It is a probability measure for `p ∈ [0,1]`, the only arguments it is used with. -/
noncomputable def bern (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- Binary randomized response `RR_t` (§2.2, p. 5) on input/output space `{0,1} = Bool`:
on input `x` it outputs `x` with probability `σ(t)` and `1 - x` with probability `σ(-t)`,
so `RR_t(0) = Bern(σ(-t))` and `RR_t(1) = Bern(σ(t))`. -/
noncomputable def randResp (t : ℝ) : Kernel Bool Bool where
  toFun x := if x then bern (Real.sigmoid t) else bern (Real.sigmoid (-t))
  measurable' := measurable_of_countable _

/-- The neighbouring relation of randomized response: `0 ∼ 1` (Hamming distance one on a
single bit), i.e. `x ∼ x'` iff `x ≠ x'`. -/
def rrAdj (x x' : Bool) : Prop := x ≠ x'

end ZCDPtoGDP.Sharp


