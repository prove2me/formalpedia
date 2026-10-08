-- Prove2me | Definitions.Def_AgrawalGoyalTS_NArmed_ThompsonSampling
-- name    : AgrawalGoyalTS_NArmed_ThompsonSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:25:54.776644+00:00
-- url     : https://prove2.me/theorems/7f2ae5fa-4a41-4326-bd34-1045fb718d7d
-- title:
--   s(j), the successes in the first j plays of arm 1, and the gap Δ_i, for Thompson Sampling (Algorithm 2)
-- statement:
--   Fix $N$ arms. Arm $i$ has a reward distribution $\nu_i$ on $\mathbb R$ (a `StochasticBandit`) with mean $\mu_i$; arm $0$ in Lean is the paper's arm $1$. Write $\Delta_i=\mu_1-\mu_i$ for the gap of arm $i$ to arm $1$.
--
--   **Thompson Sampling (Algorithm 2, p. 3).** Start with $S_i=F_i=0$ for every arm. In each round $t$:
--
--   1. for every arm $i$, independently sample $\theta_i(t)\sim\mathrm{Beta}(S_i+1,F_i+1)$;
--   2. play $i(t)=\arg\max_i\theta_i(t)$ (ties, which have probability $0$, go to the smallest index) and observe a reward $\tilde r_t\sim\nu_{i(t)}$;
--   3. perform a Bernoulli trial with success probability $\tilde r_t$ and observe its outcome $r_t$;
--   4. if $r_t=1$ then $S_{i(t)}\gets S_{i(t)}+1$, else $F_{i(t)}\gets F_{i(t)}+1$.
--
--   **Probability space.** The run of Algorithm 2 is the shared model of this series (`AgrawalGoyalTS.TwoArmed.ThompsonSampling`): three independent tables $W(i,t,a,b)\sim\mathrm{Beta}(a+1,b+1)$ (used as $\theta_i(t)$ when arm $i$ has $S_i=a$, $F_i=b$ in round $t$), $X(i,t)\sim\nu_i$ (the reward if arm $i$ is played in round $t$) and $V(i,t)$ uniform on $[0,1]$ (the Bernoulli trial of round $t$ succeeds iff $V(i(t),t)<\tilde r_t$). It defines $S_i(t)$, $F_i(t)$, $\theta_i(t)$, $i(t)$, the play count $k_i(t)$ (plays of arm $i$ before round $t$) and the expected regret
--
--   $$\mathbb E[\mathcal R(T)]=\mathbb E\Big[\sum_{t=1}^{T}\big(\mu^*-\mu_{i(t)}\big)\Big],\qquad \mu^*=\max_i\mu_i .$$
--
--   This file adds the gap $\Delta_i=\mu_1-\mu_i$ and the random variable of pp. 6 and 17
--
--   $$s(j)=\#\{u:\ i(u)=1,\ k_1(u)<j,\ r_u=1\},$$
--
--   the number of successes of the Bernoulli trials in the **first $j$ plays of the first arm** (the paper's $\sum_{m=1}^{j}Z_{1,m}$, where $Z_{1,m}$ is the outcome of the $m$-th play of arm $1$). The algorithm runs for all rounds $t=1,2,\dots$, so these plays may lie beyond the horizon $T$; then $s(j)$ is $\mathrm{Binomial}(j,\mu_1)$, as with the paper's independent $Z_{1,m}$.
--
--   **Formalization Note** Lean rounds are $t=0,1,\dots$ (Lean round $t$ is the paper's round $t+1$). Arm $1$ is played infinitely often almost surely, so $s(j)$ counts exactly $j$ trials almost surely; on the null event where arm $1$ is played fewer than $j$ times in the whole infinite run, it counts all of that arm's successes. The count is a `Set.ncard` of a set with at most $j$ elements.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 2 (§1.1, regret), p. 3 (Algorithm 2), p. 6 (s(j), the successes in the first j plays of the first arm), p. 17 (App. C.4, Z_{i,m}), p. 18 (s(j) = Σ_{m=1}^j Z_{1,m})

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_NArmed_BetaBinomial
import Definitions.Def_AgrawalGoyalTS_TwoArmed_ThompsonSampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AgrawalGoyalTS.NArmed

/-- `s(j)` for arm `i` (p. 6, p. 17): the number of successes of the Bernoulli trials in the first
`j` plays of arm `i`, i.e. the number of rounds `u` at which arm `i` is played for the `m`-th
time with `m ≤ j` (`k_i(u) < j`) and the Bernoulli trial of that round succeeds. The run is
infinite, so these plays may lie beyond any horizon `T`; arm `i` is played at most `j` times with
`k_i(u) < j`, so the set is finite. The paper's `s(j)` is `stackSuccesses ω 0 j`. -/
noncomputable def stackSuccesses {N : ℕ} [NeZero N] (ω : AgrawalGoyalTS.TwoArmed.TSOmega N)
    (i : Fin N) (j : ℕ) : ℕ :=
  {u : ℕ | AgrawalGoyalTS.TwoArmed.tsArm ω u = i ∧ AgrawalGoyalTS.TwoArmed.tsPlays ω u i < j ∧
    AgrawalGoyalTS.TwoArmed.tsCoin ω u = true}.ncard

/-- `Δ_i = μ_1 - μ_i`, the gap of arm `i` to arm `0` (the paper's arm 1, the optimal arm). -/
noncomputable def gapTo0 {N : ℕ} [NeZero N] (ν : StochasticBandit N) (i : Fin N) : ℝ :=
  banditArmMean ν 0 - banditArmMean ν i

end AgrawalGoyalTS.NArmed


