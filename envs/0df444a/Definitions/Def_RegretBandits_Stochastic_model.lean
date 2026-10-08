-- Prove2me | Definitions.Def_RegretBandits_Stochastic_model
-- name    : RegretBandits_Stochastic_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:03:24.525037+00:00
-- url     : https://prove2.me/theorems/b005412f-15c3-4b6f-b995-caa5764ff24b
-- title:
--   Stochastic bandit, moment condition (2.2), $\psi^*$, $(\psi^*)^{-1}$, $\hat\mu_{i,s}$ and pseudo-regret (2.1)
-- statement:
--   This file fixes the model of Chapter 2 of Bubeck and Cesa-Bianchi.
--
--   **Stochastic bandit.** There are $K$ arms $i\in\{1,\dots,K\}$. Rewards are represented as a *stack*: $X_{i,k}$ is the reward the forecaster receives the $(k+1)$-st time it pulls arm $i$ ($k=0,1,2,\dots$). The family $(X_{i,k})_{i,k}$ is mutually independent on a probability space $(\Omega,\mathbb P)$, the rewards of each arm are identically distributed, integrable, and $\mu_i=\mathbb E X_{i,0}$ is the mean of arm $i$. For every forecaster this produces the same joint law of arms and rewards as the protocol of the book, in which the reward of round $t$ is drawn from $\nu_{I_t}$ independently of the past.
--
--   **Moment condition (2.2).** A function $\psi:\mathbb R\to\mathbb R$ satisfies (2.2) for the bandit if $\psi$ is convex and for every arm $i$ and every $\lambda\ge 0$,
--   $$\ln \mathbb E\, e^{\lambda(X-\mathbb E X)}\le\psi(\lambda)\qquad\text{and}\qquad \ln\mathbb E\, e^{\lambda(\mathbb E X-X)}\le\psi(\lambda),$$
--   where $X$ is a reward of arm $i$; both expectations are required to be finite.
--
--   **Legendre–Fenchel transform and its inverse.** $\psi^*(\varepsilon)=\sup_{\lambda\in\mathbb R}(\lambda\varepsilon-\psi(\lambda))$, an extended real number (it may be $+\infty$). The inverse used by the algorithm is the generalized inverse
--   $$(\psi^*)^{-1}(y)=\inf\{\varepsilon\ge 0:\ \psi^*(\varepsilon)\ge y\}.$$
--   The set is nonempty because $\psi^*(\varepsilon)\ge\varepsilon-\psi(1)$, and it is bounded below by $0$.
--
--   **Sample mean and pseudo-regret.** $\hat\mu_{i,s}=\frac1s\sum_{k<s}X_{i,k}$ is the mean of the first $s$ rewards of arm $i$. For arms $I_1,I_2,\dots$ played by a forecaster, the pseudo-regret (2.1) is
--   $$\overline R_n=n\mu^*-\mathbb E\sum_{t=1}^n\mu_{I_t},\qquad \mu^*=\max_i\mu_i .$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** $\mu^*$ and the pull counts $T_i(t)$ come from the published `ImprovedLinBandits.UCBDelta.armModel`. Round $t+1$ plays `I (t+1) ω`; `I 0` is never used. $\hat\mu_{i,0}$ is the junk value $0$ and is never used.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 4 (protocol box), p. 8 Eq. (2.1), p. 10 Eq. (2.2) and the definitions of ψ* and μ̂_{i,s}

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel

namespace RegretBandits.Stochastic

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta

/-- The stochastic bandit with `K` arms of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, Ch. 2,
p. 8, and the protocol box of p. 4), in the "stack of rewards" representation: `X i k ω` is the
reward the forecaster receives at the `(k + 1)`-st pull of arm `i` (`k = 0, 1, 2, …`).
The family `(X i k)_{i, k}` is mutually independent, the rewards of one arm are identically
distributed, and `μ i` is the mean of arm `i`. Every forecaster induces the same joint law of
arms and rewards in this representation as in the book's protocol (the reward of a round is drawn
from `ν_{I_t}` independently of the past). -/
structure IsStochasticBandit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) : Prop where
  measurable : ∀ i k, Measurable (X i k)
  indep : iIndepFun (fun p : Fin K × ℕ => X p.1 p.2) P
  identDistrib : ∀ i k, IdentDistrib (X i k) (X i 0) P P
  integrable : ∀ i, Integrable (X i 0) P
  mean : ∀ i, ∫ ω, X i 0 ω ∂P = μ i

/-- The moment condition (2.2) of Bubeck and Cesa-Bianchi (p. 10) for a real random variable `Y`
with mean `m`: for every `λ ≥ 0` the moment generating functions of `Y - m` and `m - Y` at `λ` are
finite and `ln 𝔼 e^{λ(Y - 𝔼Y)} ≤ ψ(λ)`, `ln 𝔼 e^{λ(𝔼Y - Y)} ≤ ψ(λ)`. Finiteness is written as
integrability of the exponential (otherwise Lean's integral would be the junk value `0`). -/
def MomentCondition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ψ : ℝ → ℝ)
    (Y : Ω → ℝ) (m : ℝ) : Prop :=
  ∀ l : ℝ, 0 ≤ l →
    Integrable (fun ω => Real.exp (l * (Y ω - m))) P ∧
    Real.log (∫ ω, Real.exp (l * (Y ω - m)) ∂P) ≤ ψ l ∧
    Integrable (fun ω => Real.exp (l * (m - Y ω))) P ∧
    Real.log (∫ ω, Real.exp (l * (m - Y ω)) ∂P) ≤ ψ l

/-- The standing assumption (2.2) of Section 2.2 for a whole bandit: `ψ` is convex on the reals
and every arm's reward distribution satisfies the moment condition with this same `ψ`. -/
def SatisfiesMomentCondition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (ψ : ℝ → ℝ) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) : Prop :=
  ConvexOn ℝ Set.univ ψ ∧ ∀ i, MomentCondition P ψ (X i 0) (μ i)

/-- The Legendre–Fenchel transform `ψ*(ε) = sup_{λ ∈ ℝ} (λε - ψ(λ))` (p. 10), valued in the
extended reals, so that `ψ*(ε) = +∞` is represented faithfully. -/
noncomputable def legendreFenchel (ψ : ℝ → ℝ) (ε : ℝ) : EReal :=
  ⨆ l : ℝ, ((l * ε - ψ l : ℝ) : EReal)

/-- The generalized inverse `(ψ*)⁻¹(y) = inf {ε ≥ 0 : ψ*(ε) ≥ y}` used in the (α, ψ)-UCB index
(p. 10). For real-valued `ψ` the set is nonempty (`ψ*(ε) ≥ ε - ψ(1) → ∞`) and bounded below by
`0`, so the real infimum is a genuine infimum. -/
noncomputable def lfInv (ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ (y : EReal) ≤ legendreFenchel ψ ε}

/-- `μ̂_{i,s}`, the sample mean of the first `s` rewards obtained from arm `i` (p. 10):
`(1/s) ∑_{k < s} X i k`. At `s = 0` Lean returns the junk value `0`; it is never used there. -/
noncomputable def sampleMean {Ω : Type*} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (i : Fin K) (s : ℕ)
    (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range s, X i k ω) / (s : ℝ)

/-- The pseudo-regret (2.1), p. 8: `R̄_n = n μ* - 𝔼 ∑_{t=1}^n μ_{I_t}`, where round `t + 1` plays
arm `I (t + 1) ω` (the value `I 0` is never used) and `μ* = bestMean μ = max_i μ_i`. -/
noncomputable def pseudoRegretBar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K) (n : ℕ) : ℝ :=
  (n : ℝ) * bestMean μ - ∫ ω, ∑ t ∈ Finset.range n, μ (I (t + 1) ω) ∂P

end RegretBandits.Stochastic


