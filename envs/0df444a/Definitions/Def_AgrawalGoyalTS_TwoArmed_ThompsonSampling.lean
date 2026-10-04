-- Prove2me | Definitions.Def_AgrawalGoyalTS_TwoArmed_ThompsonSampling
-- name    : AgrawalGoyalTS_TwoArmed_ThompsonSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:06:59.554225+00:00
-- url     : https://prove2.me/theorems/0e31d978-7baf-4238-9e28-09ddf9e1ae2d
-- title:
--   Thompson Sampling for general stochastic bandits (Algorithm 2) and its expected regret
-- statement:
--   Consider a stochastic bandit with $N\ge 1$ arms. Arm $i$ has a fixed reward distribution $D_i$ on $\mathbb R$ (in the paper, supported in $[0,1]$) with mean $\mu_i$; $\mu^*=\max_i\mu_i$ and $\Delta_i=\mu^*-\mu_i$.
--
--   **Algorithm 2 (Thompson Sampling for general stochastic bandits).** Start with $S_i=F_i=0$ for every arm. In each round $t=1,2,\dots$:
--   1. for each arm $i$, independently sample $\theta_i(t)\sim\mathrm{Beta}(S_i+1,F_i+1)$;
--   2. play $i(t)=\arg\max_i\theta_i(t)$ and observe a reward $\tilde r_t\sim D_{i(t)}$;
--   3. perform a Bernoulli trial with success probability $\tilde r_t$ and observe its outcome $r_t\in\{0,1\}$;
--   4. if $r_t=1$ set $S_{i(t)}\leftarrow S_{i(t)}+1$, otherwise $F_{i(t)}\leftarrow F_{i(t)}+1$.
--
--   **Probability space.** All randomness is drawn up front in three independent tables: $W(i,t,a,b)\sim\mathrm{Beta}(a+1,b+1)$, $X(i,t)\sim D_i$ and $V(i,t)\sim\mathrm{Uniform}[0,1]$, independent over all indices. In round $t$ the algorithm uses $\theta_i(t)=W(i,t,S_i(t),F_i(t))$, $\tilde r_t=X(i(t),t)$ and $r_t=\mathbf 1\{V(i(t),t)<\tilde r_t\}$. Since each round reads table entries that the past has not touched, given the past the $\theta_i(t)$ are independent $\mathrm{Beta}(S_i(t)+1,F_i(t)+1)$ variables, the reward is a fresh draw from $D_{i(t)}$, and $r_t$ is a Bernoulli$(\tilde r_t)$ trial — exactly Algorithm 2.
--
--   The file also defines $S_i(t)$, $F_i(t)$, $k_i(t)$ (the number of plays of arm $i$ before round $t$) and the expected regret in time $T$,
--   $$\mathbb E[\mathcal R(T)]=\mathbb E\Big[\sum_{t=1}^T(\mu^*-\mu_{i(t)})\Big].$$
--
--   **Formalization Note** Rounds are indexed from $0$ in Lean: Lean round $t$ is the paper's round $t+1$, and `tsPlays ω t i` counts the plays of arm $i$ in Lean rounds $0,\dots,t-1$. Ties in the arg max (a probability-zero event, since Beta laws are continuous) go to the smallest index. The regret is a lower Lebesgue integral in $[0,\infty]$ of the nonnegative per-round gaps, so no integrability side condition can make it a junk value. The bandit instance is the platform's `StochasticBandit` (a family of probability measures on $\mathbb R$, one per arm), with mean `banditArmMean` and gap `banditGap`.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 2 (§1.1, regret), p. 3 (§1.2, Algorithm 2)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AgrawalGoyalTS.TwoArmed

/-- Sample space of Thompson Sampling (Algorithm 2) on `N` arms. A point `ω = (W, X, V)` holds
three independent tables:
* `W (i, t, a, b)`: a `Beta(a+1, b+1)` draw, used as `θ_i` in round `t` when arm `i` has
  `S_i = a` successes and `F_i = b` failures;
* `X (i, t)`: a reward drawn from arm `i`'s distribution, used if arm `i` is played in round `t`;
* `V (i, t)`: a uniform `[0,1]` variable; the Bernoulli trial of round `t` succeeds iff
  `V (i(t), t) < r̃_t`, i.e. with success probability `r̃_t`.
Rounds are indexed `t = 0, 1, 2, …` (Lean round `t` is the paper's round `t + 1`). -/
abbrev TSOmega (N : ℕ) :=
  (Fin N × ℕ × ℕ × ℕ → ℝ) × (Fin N × ℕ → ℝ) × (Fin N × ℕ → unitInterval)

/-- The law of `ω` for the bandit instance `ν`: the product of the three i.i.d. tables. -/
noncomputable def tsLaw {N : ℕ} (ν : StochasticBandit N) : Measure (TSOmega N) :=
  (Measure.infinitePi
      (fun k : Fin N × ℕ × ℕ × ℕ => betaMeasure ((k.2.2.1 : ℝ) + 1) ((k.2.2.2 : ℝ) + 1))).prod
    ((Measure.infinitePi (fun k : Fin N × ℕ => ν.P k.1)).prod
      (Measure.infinitePi (fun _ : Fin N × ℕ => (volume : Measure unitInterval))))

/-- `arg max_i θ_i`, ties broken towards the smallest index. -/
noncomputable def argmaxMin {N : ℕ} [NeZero N] (θ : Fin N → ℝ) : Fin N :=
  if h : (Finset.univ.filter (fun i => ∀ j, θ j ≤ θ i)).Nonempty then
    (Finset.univ.filter (fun i => ∀ j, θ j ≤ θ i)).min' h
  else 0

/-- The counts `(S, F)` (successes, failures of the Bernoulli trials of each arm) at the start of
round `t`, i.e. after rounds `0, …, t-1` of Algorithm 2, starting from `S = F = 0`. -/
noncomputable def tsCounts {N : ℕ} [NeZero N] (ω : TSOmega N) :
    ℕ → (Fin N → ℕ) × (Fin N → ℕ)
  | 0 => (0, 0)
  | t + 1 =>
    let c := tsCounts ω t
    let a := argmaxMin (fun i => ω.1 (i, t, c.1 i, c.2 i))
    if ((ω.2.2 (a, t) : ℝ) < ω.2.1 (a, t)) then
      (Function.update c.1 a (c.1 a + 1), c.2)
    else
      (c.1, Function.update c.2 a (c.2 a + 1))

/-- `S_i(t)`: successes of arm `i` before round `t`. -/
noncomputable def tsSuccesses {N : ℕ} [NeZero N] (ω : TSOmega N) (t : ℕ) (i : Fin N) : ℕ :=
  (tsCounts ω t).1 i

/-- `F_i(t)`: failures of arm `i` before round `t`. -/
noncomputable def tsFailures {N : ℕ} [NeZero N] (ω : TSOmega N) (t : ℕ) (i : Fin N) : ℕ :=
  (tsCounts ω t).2 i

/-- `θ_i(t) ∼ Beta(S_i(t)+1, F_i(t)+1)`, the posterior sample of arm `i` in round `t`. -/
noncomputable def tsTheta {N : ℕ} [NeZero N] (ω : TSOmega N) (t : ℕ) (i : Fin N) : ℝ :=
  ω.1 (i, t, tsSuccesses ω t i, tsFailures ω t i)

/-- `i(t) = arg max_i θ_i(t)`, the arm played in round `t`. -/
noncomputable def tsArm {N : ℕ} [NeZero N] (ω : TSOmega N) (t : ℕ) : Fin N :=
  argmaxMin (tsTheta ω t)

/-- `r̃_t`, the reward observed in round `t`. -/
noncomputable def tsReward {N : ℕ} [NeZero N] (ω : TSOmega N) (t : ℕ) : ℝ :=
  ω.2.1 (tsArm ω t, t)

/-- `r_t`, the outcome of the Bernoulli trial with success probability `r̃_t` in round `t`. -/
noncomputable def tsCoin {N : ℕ} [NeZero N] (ω : TSOmega N) (t : ℕ) : Bool :=
  decide ((ω.2.2 (tsArm ω t, t) : ℝ) < tsReward ω t)

/-- `k_i(t)`: the number of rounds before round `t` in which arm `i` was played. -/
noncomputable def tsPlays {N : ℕ} [NeZero N] (ω : TSOmega N) (t : ℕ) (i : Fin N) : ℕ :=
  ((Finset.range t).filter (fun u => tsArm ω u = i)).card

/-- Expected regret in time `T` (p. 2): `E[R(T)] = E[∑_{t=1}^T (μ* - μ_{i(t)})]`, the
expectation under `tsLaw ν` of the sum of the gaps of the arms played in the first `T` rounds. -/
noncomputable def tsRegret {N : ℕ} [NeZero N] (ν : StochasticBandit N) (T : ℕ) : ENNReal :=
  ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal (banditGap ν (tsArm ω t)) ∂(tsLaw ν)

end AgrawalGoyalTS.TwoArmed


