-- Prove2me | Definitions.Def_KaufmannTS_Bernoulli_Model
-- name    : KaufmannTS_Bernoulli_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:54.897984+00:00
-- url     : https://prove2.me/theorems/9bd9c3fb-ee86-4c1c-9705-760c0f7e9ed3
-- title:
--   §1–§3, pp. 1–5 — Bernoulli bandit with a unique optimal arm, Thompson Sampling, the KL-UCB and Bayes-UCB indices, and the terms A, B of (4)
-- statement:
--   This file fixes the objects of the Bernoulli Thompson Sampling analysis of Kaufmann, Korda and Munos.
--
--   **The bandit.** There are $K$ arms. Arm $a$ pays reward $1$ with probability $\mu_a$ and $0$ otherwise (the Bernoulli distribution $\mathcal B(\mu_a)$); every mean lies in $(0,1)$. The **Bernoulli instance** $\nu = \texttt{bernoulliInstance}(\mu)$ is the published Bernoulli bandit with these means.
--
--   **Thompson Sampling.** With a uniform prior on each $\mu_a$, the posterior of arm $a$ after $N_{a,t}$ draws with $S_{a,t}$ successes is $\mathrm{Beta}(S_{a,t}+1,\,N_{a,t}-S_{a,t}+1)$. In each round the algorithm draws one sample $\theta_{a,t}$ from every posterior and plays $A_t=\arg\max_a\theta_{a,t}$. The run is the published model $P=\texttt{tsLaw}(\nu)$, with samples $\theta_{a,t}$, played arms $A_t$, and pre-round counts $N_{a,t}$, $S_{a,t}$.
--
--   **Derived quantities.**
--
--   1. $\mu_2=\max_{a\neq 1}\mu_a$, the second-best mean.
--   2. $C_a = 32/(\mu_1-\mu_a)^2$ and $\delta_a=(\mu_1-\mu_a)/2$ (§3.3, p. 8).
--   3. The **KL-UCB index** of an arm with $S$ successes in $N$ draws at round $t$ and horizon $T$:
--   $$u = \sup\Big\{x\in[S/N,\,1) : N\,K(S/N,x)\le \ln t+\ln\ln T\Big\},$$
--   where $K(p,q)=p\ln(p/q)+(1-p)\ln\frac{1-p}{1-q}$ is the Bernoulli Kullback–Leibler divergence.
--   4. The **Bayes-UCB index** $q=Q\big(1-\tfrac{1}{t\ln T},\,\mathrm{Beta}(S+1,N-S+1)\big)$, the quantile of that order of the posterior.
--   5. The **under-estimation event** of the optimal arm at round $t$: $\theta_{1,t}\le\mu_1-\sqrt{6\ln t/N_{1,t}}$.
--   6. The two sums of display (4), for horizon $T$ and arm $a$:
--   $$A=\sum_{t=1}^{T}\mathbb P\Big(\theta_{1,t}\le\mu_1-\sqrt{\tfrac{6\ln t}{N_{1,t}}}\Big),\qquad B=\sum_{t=1}^{T}\mathbb P\Big(u_{a,t}>\mu_1-\sqrt{\tfrac{6\ln t}{N_{1,t}}},\ A_t=a\Big).$$
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** Lean arm $0$ is the paper's arm $1$, the optimal arm. Lean round $t$ is the paper's round $t+1$: $N_{a,t}$ and $S_{a,t}$ are the counts at the moment $\theta_{a,t}$ is drawn, and the paper's $\ln t$ at Lean round $t$ is $\ln(t+1)$. The published Thompson Sampling model is Algorithm 2 of Agrawal–Goyal, which feeds each reward $\tilde r$ to a Bernoulli trial of success probability $\tilde r$; on a Bernoulli instance $\tilde r\in\{0,1\}$, so the trial returns the reward almost surely and the posterior is exactly the paper's. Ties in the argmax go to the smallest index, a probability-zero event. Following the paper's convention (p. 4), $\sqrt{6\ln t/N_{1,t}}=\infty$ when $N_{1,t}=0$: the under-estimation event is then empty and the event of $B$ reduces to $A_t=a$. Because the real-valued $K(p,1)$ is a finite junk value (the paper's is $+\infty$), the KL-UCB supremum ranges over $x<1$; the paper leaves $u$ undefined when $N=0$ or $S=N$, and the definition sets $u=1$ there. The KL-UCB and Bayes-UCB indices are meaningful for $T\ge 3$ and $t\ge 1$, which is how every statement uses them. $\mu_2$ is a supremum over the finite set of arms $a\neq 0$, a maximum when $K\ge 2$.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, pp. 1–5 and 8: §1 (model, Eq. (1)), p. 2 (K(p, q)), §2 p. 3 (posterior, u_{a,t}, q_{a,t}), p. 4 (convention for N = 0), §3.2 display (4) p. 5, §3.3 p. 8 (C_a, δ_a)

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_AgrawalGoyalTS_TwoArmed_ThompsonSampling
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-! Kaufmann, Korda, Munos, *Thompson Sampling: An Asymptotically Optimal Finite Time Analysis*,
arXiv:1205.4217v2, §1–§3 (pp. 1–9).

Conventions used by every item of the mission:
* arms are `Fin K`; **Lean arm `0` is the paper's arm `1`** (the unique optimal arm);
* Thompson Sampling is the published run `tsLaw ν` of `AgrawalGoyalTS.TwoArmed` on the Bernoulli
  instance `ν = bernoulliInstance μ hμ`; on a Bernoulli instance its Bernoulli trial returns the
  observed reward almost surely, so its posterior is the paper's `Beta(S_{a,t}+1, N_{a,t}-S_{a,t}+1)`
  with a uniform prior;
* **Lean round `t` is the paper's round `t + 1`.** `tsPlays ω t a` and `tsSuccesses ω t a` count Lean
  rounds `0, …, t-1`: they are the paper's `N_{a,t}`, `S_{a,t}` at the moment `θ_{a,t}` is drawn, and
  the paper's `ln t` at that moment is `Real.log (t + 1)`. -/

/-- The Bernoulli bandit with means `μ a ∈ (0,1)` (§1, p. 1): arm `a` pays `1` with probability
`μ a` and `0` otherwise. -/
noncomputable def bernoulliInstance {K : ℕ} (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) : StochasticBandit K :=
  bernoulliBandit μ (fun a => Set.Ioo_subset_Icc_self (hμ a))

/-- `μ₂`, the largest mean among the suboptimal arms `a ≠ 0` (§2, p. 3, where the paper orders
`μ₁ > μ₂ ≥ … ≥ μ_K`). For `K ≥ 2` the index type is finite and nonempty, so this is a maximum. -/
noncomputable def secondBestMean {K : ℕ} [NeZero K] (μ : Fin K → ℝ) : ℝ :=
  ⨆ a : {a : Fin K // a ≠ 0}, μ a

/-- `C_a = 32 / (μ₁ - μ_a)²` (§3.3, p. 8). -/
noncomputable def satConst {K : ℕ} [NeZero K] (μ : Fin K → ℝ) (a : Fin K) : ℝ :=
  32 / (μ 0 - μ a) ^ 2

/-- `δ_a = (μ₁ - μ_a) / 2` (§3.3, p. 8). -/
noncomputable def satGap {K : ℕ} [NeZero K] (μ : Fin K → ℝ) (a : Fin K) : ℝ :=
  (μ 0 - μ a) / 2

/-- The KL-UCB index `u_{a,t}` of §2 (p. 3) for an arm with `S` successes in `N` draws, at
paper round `t` and horizon `T`:
`u = sup { x ∈ [S/N, 1) : N · K(S/N, x) ≤ ln t + ln ln T }`.
The supremum ranges over `x < 1` because the real-valued `bernoulliRelativeEntropy p 1` is a
finite junk value, whereas the paper's `K(p, 1)` is `+∞` for `p < 1`. The paper leaves the cases
`N = 0` and `S = N` undefined; this definition sets `u = 1` there. -/
noncomputable def klucbIdx (T t S N : ℕ) : ℝ :=
  if N = 0 ∨ S = N then 1 else
    sSup {x : ℝ | (S : ℝ) / N ≤ x ∧ x < 1 ∧
      (N : ℝ) * bernoulliRelativeEntropy ((S : ℝ) / N) x ≤ Real.log t + Real.log (Real.log T)}

/-- The Bayes-UCB index `q_{a,t} = Q(1 - 1/(t ln T), π_{a,t})` of §2 (p. 3): the quantile of order
`1 - 1/(t ln T)` of the posterior `Beta(S+1, N-S+1)` of an arm with `S` successes in `N` draws,
i.e. `inf { x : F^Beta_{S+1,N-S+1}(x) ≥ 1 - 1/(t ln T) }`. -/
noncomputable def bayesucbIdx (T t S N : ℕ) : ℝ :=
  sInf {x : ℝ | 1 - 1 / ((t : ℝ) * Real.log T) ≤
    betaCDF ((S : ℝ) + 1) (((N - S : ℕ) : ℝ) + 1) x}

/-- The under-estimation event of the optimal arm at Lean round `t` (paper round `t + 1`):
`θ_{1,t} ≤ μ₁ - √(6 ln t / N_{1,t})`, with the paper's convention (p. 4) that
`√(6 ln t / N_{1,t}) = ∞` when `N_{1,t} = 0`, so that the event is empty then. -/
def underEstEvent {K : ℕ} [NeZero K] (μ : Fin K → ℝ) (t : ℕ) : Set (TSOmega K) :=
  {ω | 0 < tsPlays ω t 0 ∧
    tsTheta ω t 0 ≤ μ 0 - Real.sqrt (6 * Real.log ((t : ℝ) + 1) / (tsPlays ω t 0 : ℝ))}

/-- Term `A` of display (4) (p. 5) with horizon `T`:
`A = ∑_{t=1}^{T} P(θ_{1,t} ≤ μ₁ - √(6 ln t / N_{1,t}))`, paper rounds `1, …, T` being Lean rounds
`0, …, T-1`. -/
noncomputable def termA {K : ℕ} [NeZero K] (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (T : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, tsLaw (bernoulliInstance μ hμ) (underEstEvent μ t)

/-- Term `B` of display (4) (p. 5) for arm `a` with horizon `T`:
`B = ∑_{t=1}^{T} P(u_{a,t} > μ₁ - √(6 ln t / N_{1,t}), A_t = a)`. With the convention
`√(6 ln t / 0) = ∞` (p. 4) the inequality holds automatically when `N_{1,t} = 0`. The index
`u_{a,t}` is `klucbIdx T t S_{a,t} N_{a,t}` at paper round `t` = Lean round `t - 1`. -/
noncomputable def termB {K : ℕ} [NeZero K] (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (a : Fin K) (T : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, tsLaw (bernoulliInstance μ hμ)
    {ω | tsArm ω t = a ∧
      (tsPlays ω t 0 = 0 ∨
        μ 0 - Real.sqrt (6 * Real.log ((t : ℝ) + 1) / (tsPlays ω t 0 : ℝ)) <
          klucbIdx T (t + 1) (tsSuccesses ω t a) (tsPlays ω t a))}

end KaufmannTS.Bernoulli


