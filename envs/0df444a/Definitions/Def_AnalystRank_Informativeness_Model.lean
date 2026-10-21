-- Prove2me | Definitions.Def_AnalystRank_Informativeness_Model
-- name    : AnalystRank_Informativeness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:22.767864+00:00
-- url     : https://prove2.me/theorems/b1032a80-7aac-4712-a7f1-d0679eff9b19
-- title:
--   Two-analyst forecasting contest: correlated binary signals (1)–(2), rank payoff (3), benchmark payoff, symmetric equilibrium, most informative equilibrium, informativeness Π (6)
-- statement:
--   This file fixes the model of §2, §3 and §5 of Banerjee's paper.
--
--   1. **State and prior.** The state is $\omega\in\{H,L\}$ with $\Pr(H)=q$. For informativeness, $H=1$ and $L=0$, so $\mathrm{Var}(\omega)=q(1-q)$.
--   2. **Signals.** Each analyst $i\in\{1,2\}$ observes $s_i\in\{h,l\}$ with precision $\gamma=\Pr(s_i=\omega\mid\omega)$. With correlation parameter $\rho$ and $\chi:=\rho\gamma(1-\gamma)$ (equation (2)), the joint law (1) assigns to each ordered pair of signals
--   $$\Pr(s_i,s_j\mid\omega)=\begin{cases}\gamma^2+\chi & s_i=s_j=\omega,\\ (1-\gamma)^2+\chi & s_i=s_j\neq\omega,\\ \gamma(1-\gamma)-\chi & s_i\neq s_j .\end{cases}$$
--   3. **Strategies.** A symmetric strategy is $\sigma=(\sigma^h,\sigma^l)$, where $\sigma^h=\Pr(m_i=\hat h\mid s_i=h)$ and $\sigma^l=\Pr(m_i=\hat l\mid s_i=l)$. Both analysts use it.
--   4. **Payoffs.** The rank payoff (3) pays $w_1$ to the only correct forecaster, $w_2$ to the only incorrect one, and $w_0$ to both when the forecasts coincide. Payoff convexity (4) is $\varphi=W_1/W_2$ with $W_1=w_1-w_0$ and $W_2=w_0-w_2$. The benchmark payoff of §3.1 is $1$ for a correct forecast and $0$ otherwise, whatever the other analyst does.
--   5. **Expected payoffs.** For a payoff $u$, $U_i(m\mid s)=E_{\omega,m_j}[u(m,m_j,\omega)\mid s_i=s]$ is computed by Bayes' rule from the prior, the joint signal law and the opponent's strategy $\sigma$. The net payoffs of (A.1) are $\Delta U^h=U_i(\hat h\mid h)-U_i(\hat l\mid h)$ and $\Delta U^l=U_i(\hat l\mid l)-U_i(\hat h\mid l)$.
--   6. **Equilibrium** (Definition 1). $\sigma$ is a symmetric equilibrium if $\sigma\in[0,1]^2$, $\sigma^h\ge 1-\sigma^l$ (the restriction of p. 9), and, for each signal, the prescribed probability of a truthful forecast maximises the expected payoff over every probability $x\in[0,1]$, given that the other analyst plays $\sigma$. The rank game and the benchmark game each have their own equilibrium set.
--   7. **Most informative equilibrium** (Definition 2). An equilibrium that is coordinatewise at least every equilibrium of the same game.
--   8. **Forecast informativeness** (Definition 3). With $\Pr(m_i,m_j\mid\omega)=\sum_{s_i,s_j}\Pr(s_i,s_j\mid\omega)\Pr(m_i\mid s_i)\Pr(m_j\mid s_j)$ and posterior variance $\mathrm{Var}(\omega\mid m_i,m_j)=\Pr(H\mid m_i,m_j)\Pr(L\mid m_i,m_j)$,
--   $$\Pi(\sigma)=\frac{\mathrm{Var}(\omega)}{E_{m_i,m_j}[\mathrm{Var}(\omega\mid m_i,m_j)]}-1 .$$
--   9. **Separation threshold** (B.2): $q_{\min}=\gamma-\chi\,\dfrac{\varphi-1}{(1-\gamma)\varphi+\gamma}$, written $\check q_{\min}$ when $\varphi>1$ and $\hat q_{\min}$ when $\varphi<1$.
--
--   Every equilibrium statement of the mission is built from these primitives. The best-response conditions use the conditional expectations themselves, not the closed forms (A.13)–(A.14).
--
--   **Formalization Note** States, signals and forecasts are `Bool` (`true` = H, h, ĥ). A strategy is a pair `σ : ℝ × ℝ`. Expected payoffs divide by $\Pr(s_i=s)$, which is positive for $q\in(0,1)$ and $\gamma\in(1/2,1)$. A forecast pair of probability $0$ gets posterior $\Pr(H\mid\cdot)=0$ (Lean's $x/0=0$) and contributes $0$ to the expected posterior variance, as in the paper. The benchmark uses $\pi_a=1$, $\pi_{na}=0$, a positive rescaling of the paper's $\pi_a=W>0$ that does not change best responses. The model makes no assumption on the parameters; the theorems state $q\in(0,1)$, $\gamma\in(1/2,1)$, $\rho\in[0,1]$ and $w_1>w_0>w_2$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), pp. 6–10, 24, 30, 34, §2 (1)–(4), §3 Definitions 1–2, §3.1, §5 Definition 3 (6), Appendix A (A.1), Appendix B (B.2)

import Mathlib

namespace AnalystRank.Informativeness

open Set

/-! Two-analyst forecasting contest of Banerjee (2017 working paper), §2–§3 and §5.
States, signals and forecasts are encoded as `Bool`: `true` = H / h / ĥ, `false` = L / l / l̂. -/

/-- Conditional covariance of the two signals, (2): `χ = ρ γ (1 - γ)`. -/
noncomputable def chi (γ ρ : ℝ) : ℝ := ρ * γ * (1 - γ)

/-- Prior law of the state: `Pr(H) = q`, `Pr(L) = 1 - q`. -/
noncomputable def prior (q : ℝ) (ω : Bool) : ℝ := if ω then q else 1 - q

/-- Joint law of the two signals given the state, (1)–(2), one ordered cell `(sᵢ, sⱼ)` at a time:
`γ² + χ` if both signals equal the state, `(1-γ)² + χ` if both differ from it, and
`γ(1-γ) - χ` for each of the two cells with `sᵢ ≠ sⱼ`. -/
noncomputable def sigLaw (γ ρ : ℝ) (ω si sj : Bool) : ℝ :=
  if si = sj then (if si = ω then γ ^ 2 + chi γ ρ else (1 - γ) ^ 2 + chi γ ρ)
  else γ * (1 - γ) - chi γ ρ

/-- Forecast kernel of the symmetric strategy `σ = (σʰ, σˡ)`: `Pr(m | s)`, where
`σʰ = Pr(ĥ | h)` and `σˡ = Pr(l̂ | l)`. -/
def fcast (σ : ℝ × ℝ) (s m : Bool) : ℝ :=
  if s then (if m then σ.1 else 1 - σ.1) else (if m then 1 - σ.2 else σ.2)

/-- Rank payoff (3): `w₀` on a tie (`mᵢ = mⱼ`), `w₁` for the unique correct forecast,
`w₂` for the unique incorrect forecast. Arguments: own forecast, other forecast, state. -/
def rankPay (w1 w0 w2 : ℝ) (mi mj ω : Bool) : ℝ :=
  if mi = mj then w0 else if mi = ω then w1 else w2

/-- Benchmark payoff (§3.1) with `πₐ = 1`, `πₙₐ = 0`: own accuracy only. -/
def benchPay (mi _mj ω : Bool) : ℝ := if mi = ω then 1 else 0

/-- Payoff convexity (4): `φ = W₁ / W₂` with `W₁ = w₁ - w₀`, `W₂ = w₀ - w₂`. -/
noncomputable def phi (w1 w0 w2 : ℝ) : ℝ := (w1 - w0) / (w0 - w2)

/-- Marginal probability `Pr(sᵢ = s)` of an analyst's signal. -/
noncomputable def sigProb (q γ ρ : ℝ) (s : Bool) : ℝ :=
  ∑ ω : Bool, ∑ sj : Bool, prior q ω * sigLaw γ ρ ω s sj

/-- Expected payoff `Uᵢ(m | s) = E_{ω, mⱼ}[u(m, mⱼ, ω) | sᵢ = s]` (Definition 1 (5), (A.1)) when the
other analyst plays `σ`, computed by Bayes' rule from the prior and the joint signal law. -/
noncomputable def condPay (pay : Bool → Bool → Bool → ℝ) (q γ ρ : ℝ) (σ : ℝ × ℝ) (s m : Bool) : ℝ :=
  (∑ ω : Bool, ∑ sj : Bool,
      prior q ω * sigLaw γ ρ ω s sj * ∑ mj : Bool, fcast σ sj mj * pay m mj ω) / sigProb q γ ρ s

/-- Expected payoff of an analyst with signal `s` who forecasts truthfully (`m = s`) with
probability `x` and untruthfully with probability `1 - x`, against `σ`. -/
noncomputable def mixPay (pay : Bool → Bool → Bool → ℝ) (q γ ρ : ℝ) (σ : ℝ × ℝ) (s : Bool)
    (x : ℝ) : ℝ :=
  x * condPay pay q γ ρ σ s s + (1 - x) * condPay pay q γ ρ σ s (!s)

/-- Net expected payoff from a truthful versus an untruthful forecast, (A.1):
`ΔUʰ = Uᵢ(ĥ | h) - Uᵢ(l̂ | h)` for `s = true`, `ΔUˡ = Uᵢ(l̂ | l) - Uᵢ(ĥ | l)` for `s = false`. -/
noncomputable def dU (pay : Bool → Bool → Bool → ℝ) (q γ ρ : ℝ) (σ : ℝ × ℝ) (s : Bool) : ℝ :=
  condPay pay q γ ρ σ s s - condPay pay q γ ρ σ s (!s)

/-- Symmetric equilibrium (Definition 1, with the restriction `σʰ ≥ 1 - σˡ` of p. 9): `σ ∈ [0,1]²`,
`σʰ + σˡ ≥ 1`, and for each signal the prescribed mixing probability maximises the analyst's
expected payoff over all mixing probabilities in `[0,1]`, when the other analyst plays `σ`. -/
def IsSymEq (pay : Bool → Bool → Bool → ℝ) (q γ ρ : ℝ) (σ : ℝ × ℝ) : Prop :=
  σ.1 ∈ Icc (0 : ℝ) 1 ∧ σ.2 ∈ Icc (0 : ℝ) 1 ∧ 1 - σ.2 ≤ σ.1 ∧
  (∀ x ∈ Icc (0 : ℝ) 1, mixPay pay q γ ρ σ true x ≤ mixPay pay q γ ρ σ true σ.1) ∧
  (∀ x ∈ Icc (0 : ℝ) 1, mixPay pay q γ ρ σ false x ≤ mixPay pay q γ ρ σ false σ.2)

/-- The set of symmetric equilibria of the rank game (competition). -/
def rankEqSet (w1 w0 w2 q γ ρ : ℝ) : Set (ℝ × ℝ) := {σ | IsSymEq (rankPay w1 w0 w2) q γ ρ σ}

/-- The set of symmetric equilibria of the benchmark game (no competition). -/
def benchEqSet (q γ ρ : ℝ) : Set (ℝ × ℝ) := {σ | IsSymEq benchPay q γ ρ σ}

/-- Most informative equilibrium (Definition 2): an element of `E` that is coordinatewise at least
every element of `E`. -/
def IsMostInformative (E : Set (ℝ × ℝ)) (σ : ℝ × ℝ) : Prop :=
  σ ∈ E ∧ ∀ e ∈ E, e.1 ≤ σ.1 ∧ e.2 ≤ σ.2

/-- Law of the forecast pair given the state: `Pr(mᵢ, mⱼ | ω)` when both analysts play `σ`. -/
noncomputable def fcastPairLaw (γ ρ : ℝ) (σ : ℝ × ℝ) (ω mi mj : Bool) : ℝ :=
  ∑ si : Bool, ∑ sj : Bool, sigLaw γ ρ ω si sj * fcast σ si mi * fcast σ sj mj

/-- Unconditional probability `Pr(mᵢ, mⱼ)` of a forecast pair. -/
noncomputable def fcastPairProb (q γ ρ : ℝ) (σ : ℝ × ℝ) (mi mj : Bool) : ℝ :=
  ∑ ω : Bool, prior q ω * fcastPairLaw γ ρ σ ω mi mj

/-- Posterior probability `Pr(H | mᵢ, mⱼ)` by Bayes' rule (`0` on a forecast pair of probability `0`). -/
noncomputable def postHigh (q γ ρ : ℝ) (σ : ℝ × ℝ) (mi mj : Bool) : ℝ :=
  prior q true * fcastPairLaw γ ρ σ true mi mj / fcastPairProb q γ ρ σ mi mj

/-- Posterior variance `Var(ω | mᵢ, mⱼ) = Pr(H | ·) Pr(L | ·)` of `ω ∈ {1, 0}` (H = 1, L = 0). -/
noncomputable def postVar (q γ ρ : ℝ) (σ : ℝ × ℝ) (mi mj : Bool) : ℝ :=
  postHigh q γ ρ σ mi mj * (1 - postHigh q γ ρ σ mi mj)

/-- Expected posterior variance `E_{mᵢ, mⱼ}[Var(ω | mᵢ, mⱼ)]`. -/
noncomputable def expPostVar (q γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  ∑ mi : Bool, ∑ mj : Bool, fcastPairProb q γ ρ σ mi mj * postVar q γ ρ σ mi mj

/-- Forecast informativeness, Definition 3 (6): `Π = Var(ω) / E[Var(ω | mᵢ, mⱼ)] - 1`,
with `Var(ω) = q (1 - q)`. -/
noncomputable def informativeness (q γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  q * (1 - q) / expPostVar q γ ρ σ - 1

/-- Separation threshold (B.2): `q_min = γ - χ (φ - 1) / ((1 - γ) φ + γ)`
(`q̌_min` for `φ > 1`, `q̂_min` for `φ < 1`). -/
noncomputable def qmin (γ ρ φ : ℝ) : ℝ := γ - chi γ ρ * ((φ - 1) / ((1 - γ) * φ + γ))

end AnalystRank.Informativeness


