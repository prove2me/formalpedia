-- Prove2me | Definitions.Def_ModelFreeBounds_Duality_Market
-- name    : ModelFreeBounds_Duality_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:50.66843+00:00
-- url     : https://prove2.me/theorems/9542f909-614c-4c56-8b61-72be1adc0277
-- title:
--   §2, pp. 5–6 — one-period market with bid–ask spreads: π(y) (2.1), Assumption 2.1, ϕ(f) (2.2), Q, Δ (EC.4.1), C (EC.4.2), Γ_ν, extended expectation
-- statement:
--   This file fixes the one-period, model-free market of Neufeld, Papapantoleon and Xiang.
--
--   Let $\Omega$ be a Polish space with its Borel $\sigma$-algebra and fix $m\in\mathbb N$. A **market** consists of payoff functions $g_1,\dots,g_m:\Omega\to\mathbb R$ (collected in $g:\Omega\to\mathbb R^m$), bid prices $\underline\pi_1,\dots,\underline\pi_m$ and ask prices $\overline\pi_1,\dots,\overline\pi_m$. The **standing assumptions** are that every $g_j$ is Borel measurable and $\underline\pi_j\le\overline\pi_j$.
--
--   1. **Cost of a static position** (2.1). For $y\in\mathbb R^m$, with $y_j^+=\max\{y_j,0\}$ and $y_j^-=\max\{-y_j,0\}$,
--   $$\pi(y)=\sum_{j=1}^m y_j^+\,\overline\pi_j-y_j^-\,\underline\pi_j ,$$
--   so long positions are bought at the ask and short positions are sold at the bid. The payoff of the position is $\langle y,g\rangle(\omega)=\sum_j y_j g_j(\omega)$.
--   2. **No-arbitrage** (Assumption 2.1). For every $y\in\mathbb R^m$: if $\langle y,g\rangle(\omega)-\pi(y)\ge0$ for every $\omega\in\Omega$, then $\langle y,g\rangle(\omega)-\pi(y)=0$ for every $\omega\in\Omega$.
--   3. **Superhedging price** (2.2). For $f:\Omega\to\mathbb R$,
--   $$\phi(f)=\inf\{c+\pi(y): c\in\mathbb R,\ y\in\mathbb R^m,\ c+\langle y,g\rangle\ge f \text{ on }\Omega\}\in[-\infty,\infty],$$
--   with $\inf\emptyset=+\infty$.
--   4. **Pricing measures**. $\mathcal Q$ is the set of Borel probability measures $\mu$ on $\Omega$ under which every $g_j$ is integrable and $\underline\pi_j\le\int_\Omega g_j\,d\mu\le\overline\pi_j$ for $j=1,\dots,m$.
--   5. **The box** (EC.4.1) $\Delta=[\underline\pi_1,\overline\pi_1]\times\cdots\times[\underline\pi_m,\overline\pi_m]\subset\mathbb R^m$.
--   6. **Super-replicable payoffs at zero cost** (EC.4.2) $\mathcal C=\{\langle y,g\rangle-\pi(y):y\in\mathbb R^m\}-\mathcal L^0_+$, where $\mathcal L^0_+$ is the set of Borel measurable $h:\Omega\to\mathbb R$ with $h(\omega)\ge0$ for every $\omega$.
--   7. **Moment sets** (Appendix EC.4). For a Borel $f$ and a probability measure $\nu$, $\widetilde{\mathcal P}_\nu$ is the set of Borel probability measures $\mu$ with $\nu\ll\mu$ and $\int_\Omega|f|+\sum_j|g_j|\,d\mu<\infty$, and $\Gamma_\nu=\{\int_\Omega g\,d\mu:\mu\in\widetilde{\mathcal P}_\nu\}\subset\mathbb R^m$; $\widetilde{\mathcal P}$ and $\Gamma$ are the same without the condition $\nu\ll\mu$.
--   8. **Extended integral**. For a function $f$ that need not be integrable, $\int_\Omega f\,d\mu=\int f^+d\mu-\int f^-d\mu\in[-\infty,\infty]$, with $\infty-\infty=-\infty$.
--
--   These objects are the vocabulary of the superhedging duality $\phi(f)=\sup_{\mu\in\mathcal Q}\int_\Omega f\,d\mu$ (Theorem 2.4) and of the two lemmas of Appendix EC.4 on which its proof rests.
--
--   **Formalization Note** Indices run over `Fin m` and vectors are functions `Fin m → ℝ`. $\phi(f)$ is an infimum in `EReal`. The paper writes $\int f\,d\mu$ without fixing a convention for non-integrable $f$; the extended integral here uses $\infty-\infty=-\infty$ (Bouchard–Nutz's convention, which the paper says its proofs adapt). In $\mathcal Q$, integrability of each $g_j$ is part of the definition, since the real bounds on $\int g_j\,d\mu$ presuppose it. Integrability of $|f|+\sum_j|g_j|$ is written as integrability of $f$ and of every $g_j$, which is equivalent. The topology of $\Omega$ is not used by the definitions; the theorems carry the Polish and Borel assumptions.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, §2, eq. (2.1), Assumption 2.1, eq. (2.2) and the definition of Q, pp. 5–6; Appendix EC.4, eqs. (EC.4.1)–(EC.4.2), p. ec15–ec16, and Lemma EC.4.2, p. ec18

import Mathlib

namespace ModelFreeBounds.Duality

open MeasureTheory

/-- §2 (p. 5): a one-period market with `m` traded derivatives. The payoff vector is
`g : Ω → ℝ^m` (`g ω j = g_j(ω)`), the bid prices are `bid j = π̲_j` and the ask prices are
`ask j = π̄_j`. -/
structure Market (Ω : Type*) (m : ℕ) where
  /-- payoffs `g_j : Ω → ℝ`, `j = 1, …, m` (indexed by `Fin m`). -/
  g : Ω → Fin m → ℝ
  /-- bid prices `π̲_j`. -/
  bid : Fin m → ℝ
  /-- ask prices `π̄_j`. -/
  ask : Fin m → ℝ

namespace Market

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (M : Market Ω m)

/-- Standing assumptions of §2 (p. 5): every `g_j` is Borel measurable and `π̲_j ≤ π̄_j`. -/
structure Standing : Prop where
  measurable_g : ∀ j, Measurable (fun ω => M.g ω j)
  bid_le_ask : ∀ j, M.bid j ≤ M.ask j

/-- (2.1): `π(y) = Σ_j (y_j⁺ π̄_j − y_j⁻ π̲_j)`, the cost of the static position `y`
(long positions are bought at the ask, short positions are sold at the bid). -/
noncomputable def cost (y : Fin m → ℝ) : ℝ :=
  ∑ j, (max (y j) 0 * M.ask j - max (-y j) 0 * M.bid j)

/-- `⟨y, g⟩(ω) = Σ_j y_j g_j(ω)`. -/
def pay (y : Fin m → ℝ) (ω : Ω) : ℝ :=
  ∑ j, y j * M.g ω j

/-- Assumption 2.1 (No-Arbitrage), point-wise on all of `Ω`:
`⟨y, g⟩ − π(y) ≥ 0` everywhere implies `⟨y, g⟩ − π(y) = 0` everywhere. -/
def NoArbitrage : Prop :=
  ∀ y : Fin m → ℝ, (∀ ω, 0 ≤ M.pay y ω - M.cost y) → ∀ ω, M.pay y ω - M.cost y = 0

/-- (2.2): `ϕ(f) = inf {c + π(y) : c ∈ ℝ, y ∈ ℝ^m, c + ⟨y, g⟩ ≥ f}`, an infimum in `[−∞, ∞]`
(the infimum of the empty set is `+∞`). The constraint holds at every `ω ∈ Ω`. -/
noncomputable def superhedgingPrice (f : Ω → ℝ) : EReal :=
  sInf {x : EReal | ∃ (c : ℝ) (y : Fin m → ℝ),
    (∀ ω, f ω ≤ c + M.pay y ω) ∧ x = ((c + M.cost y : ℝ) : EReal)}

/-- `Q = {μ ∈ P(Ω) : π̲_j ≤ ∫ g_j dμ ≤ π̄_j, j = 1, …, m}` (p. 6). The real bounds on
`∫ g_j dμ` presuppose that `g_j` is `μ`-integrable, which is part of the defining condition. -/
def pricingMeasures : Set (Measure Ω) :=
  {μ | IsProbabilityMeasure μ ∧ ∀ j, Integrable (fun ω => M.g ω j) μ ∧
    M.bid j ≤ ∫ ω, M.g ω j ∂μ ∧ ∫ ω, M.g ω j ∂μ ≤ M.ask j}

/-- (EC.4.1): the box `Δ = [π̲_1, π̄_1] × ⋯ × [π̲_m, π̄_m] ⊂ ℝ^m`. -/
def box : Set (Fin m → ℝ) :=
  Set.univ.pi (fun j => Set.Icc (M.bid j) (M.ask j))

/-- (EC.4.2): `C = {⟨y, g⟩ − π(y) : y ∈ ℝ^m} − L⁰₊`, where `L⁰₊` is the set of Borel measurable
functions `h : Ω → ℝ` with `h(ω) ≥ 0` for every `ω`. -/
def superReplicable : Set (Ω → ℝ) :=
  {k | ∃ (y : Fin m → ℝ) (h : Ω → ℝ), Measurable h ∧ (∀ ω, 0 ≤ h ω) ∧
    k = fun ω => M.pay y ω - M.cost y - h ω}

/-- Lemma EC.4.2 (p. ec18): `Γ_ν = {∫ g dμ : μ ∈ P̃_ν}` with
`P̃_ν = {μ ∈ P(Ω) : ν ≪ μ, ∫ |f| + Σ_j |g_j| dμ < ∞}`. -/
def momentSet (f : Ω → ℝ) (ν : Measure Ω) : Set (Fin m → ℝ) :=
  {x | ∃ μ : Measure Ω, IsProbabilityMeasure μ ∧ ν ≪ μ ∧ Integrable f μ ∧
    (∀ j, Integrable (fun ω => M.g ω j) μ) ∧ x = fun j => ∫ ω, M.g ω j ∂μ}

/-- p. ec16: `Γ = {∫ g dμ : μ ∈ P̃}` with `P̃ = {μ ∈ P(Ω) : ∫ |f| + Σ_j |g_j| dμ < ∞}`. -/
def momentSetAll (f : Ω → ℝ) : Set (Fin m → ℝ) :=
  {x | ∃ μ : Measure Ω, IsProbabilityMeasure μ ∧ Integrable f μ ∧
    (∀ j, Integrable (fun ω => M.g ω j) μ) ∧ x = fun j => ∫ ω, M.g ω j ∂μ}

end Market

/-- `∫_Ω f dμ` for a function `f : Ω → ℝ` that need not be integrable:
`∫ f⁺ dμ − ∫ f⁻ dμ ∈ [−∞, ∞]`, with the convention `∞ − ∞ = −∞` (`EReal` subtraction). -/
noncomputable def expect {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (f ω) ∂μ : ENNReal) : EReal) -
    ((∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ : ENNReal) : EReal)

end ModelFreeBounds.Duality


