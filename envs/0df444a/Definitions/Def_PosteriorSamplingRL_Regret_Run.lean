-- Prove2me | Definitions.Def_PosteriorSamplingRL_Regret_Run
-- name    : PosteriorSamplingRL_Regret_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T21:01:40.341498+00:00
-- url     : https://prove2.me/theorems/947497b9-6dc3-4bd7-82a3-a6d821dd1d7e
-- title:
--   §2–3, p. 3, (3), p. 5 — the PSRL run: posterior sampling, reset from ρ, rewards and transitions from M*; Δ_k, Δ̃_k, Regret(T)
-- statement:
--   This module formalizes the interaction protocol of §2 and the algorithm PSRL of §3 (posterior sampling for reinforcement learning), together with the regret.
--
--   A **PSRL run** lives on a probability space $(\Omega,\mathcal F,\mathbb P)$ and consists of measurable random elements: the true MDP $M^*$, the sampled MDPs $M_1,M_2,\dots$, and for each episode $k$ the states $s_{k,1},\dots,s_{k,\tau+1}$ and rewards $r_{k,1},\dots,r_{k,\tau}$. Episode $k$ follows $\mu_k=\mu^{M_k}$, where $\theta\mapsto\mu^\theta$ is a fixed measurable map choosing an optimal policy for every MDP: $a_{k,i}=\mu_k(s_{k,i},i)$. The history $H_{t_k}$ consists of all states, actions and rewards of the episodes before $k$. The run satisfies:
--
--   1. $M^*$ has distribution $f$ (the prior);
--   2. **posterior sampling:** conditionally on $M^*$, $M_1,\dots,M_{k-1}$ and $H_{t_k}$, the sample $M_k$ has the posterior law $\mathbb P(M^*\in\cdot\mid H_{t_k})$;
--   3. **reset:** conditionally on all of this and $M_k$, the first state $s_{k,1}$ of episode $k$ has law $\rho$;
--   4. **rewards:** conditionally on everything up to the current state, $r_{k,i}\sim R^{M^*}_{a_{k,i}}(s_{k,i})$;
--   5. **transitions:** conditionally on everything up to the current reward, $s_{k,i+1}\sim P^{M^*}_{a_{k,i}}(\cdot\mid s_{k,i})$.
--
--   With $\mu^*=\mu^{M^*}$, the regret of episode $k$, the sampled-MDP gap (3) and the cumulative regret are
--   $$
--   \Delta_k=\sum_{s}\rho(s)\big(V^{M^*}_{\mu^*,1}(s)-V^{M^*}_{\mu_k,1}(s)\big),\qquad
--   \tilde\Delta_k=\sum_{s}\rho(s)\big(V^{M_k}_{\mu_k,1}(s)-V^{M^*}_{\mu_k,1}(s)\big),
--   $$
--   $$
--   \mathrm{Regret}(T,\pi^{\mathrm{PS}}_\tau)=\sum_{k=1}^{\lceil T/\tau\rceil}\Delta_k .
--   $$
--   The module also defines the one-step Bellman error $(\mathcal T^{M_k}_{\mu_k(\cdot,i)}-\mathcal T^{M^*}_{\mu_k(\cdot,i)})V^{M_k}_{\mu_k,i+1}(s_{k,i})$ of (6), and the $\sigma$-algebras $\sigma(H_{t_k})$ and $\sigma(M^*,M_k)$.
--
--   These are the objects of Theorem 1 and of the steps of its proof.
--
--   **Formalization Note** Episodes and steps are 0-based: Lean episode `k` is the paper's episode $k+1$, and `st k j`, `j = 0, …, τ`, is the paper's $s_{t_k+j}$. Conditional laws are written as conditional expectations of indicators (`μ[1_E | 𝒢] =ᵐ[μ] …`). The paper leaves three features of the model implicit, and the run states them: the state is reset from $\rho$ at every episode start ($\Delta_k$ is defined with $\rho$, and §6 says "the state is reset every τ = 20 steps"); the state reached after the last action of an episode is observed (the Algorithm box observes $s_{t+1}$ at every step $j=1,\dots,\tau$); and the sampling step uses fresh randomness, so that given the history $M_k$ is independent of $M^*$ and of the earlier samples. Every random element and the selector are measurable, so the expectations in the theorems are not junk values. The posterior-sampling clause concerns indicators of $M_k$ only; its extension to functions of $(M,H_{t_k})$ is Lemma 1, a theorem of the mission.
-- source:
--   arXiv:1306.0940v5, §2, p. 3 (interaction, regret), §3, p. 3 (PSRL and the Algorithm box), (3), p. 5, (6), p. 6

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_MDP

namespace PosteriorSamplingRL.Regret

open MeasureTheory ProbabilityTheory

/-- The observations of one episode: the states `s_{k,0}, …, s_{k,τ}` (the last one is the state
reached after the last action), the actions `a_{k,0}, …, a_{k,τ-1}` and the rewards
`r_{k,0}, …, r_{k,τ-1}`. -/
abbrev EpisodeObs (S A τ : ℕ) := (Fin (τ + 1) → Fin S) × (Fin τ → Fin A) × (Fin τ → ℝ)

/-- The history `H_{t_k}` available at the start of (0-based) episode `k`: the observations of
episodes `0, …, k - 1`. -/
abbrev Hist (S A τ k : ℕ) := Fin k → EpisodeObs S A τ

variable {S A τ : ℕ} {Θ : Type} [MeasurableSpace Θ]

/-- The history `H_{t_k}` produced by the random elements `Msamp`, `st`, `rw` when episode `l` follows
`µ_l = sel (Msamp l)`: the states, actions `a_{l,j} = µ_l(s_{l,j}, j)` and rewards of episodes
`l < k`. -/
def histOf (sel : Θ → Policy S A τ) {Ω : Type} (Msamp : ℕ → Ω → Θ) (st : ℕ → Fin (τ + 1) → Ω → Fin S)
    (rw : ℕ → Fin τ → Ω → ℝ) (k : ℕ) (ω : Ω) : Hist S A τ k :=
  fun l => ((fun j => st l j ω), (fun j => sel (Msamp l ω) (st l j.castSucc ω) j),
    (fun j => rw l j ω))

/-- The information before the sampling step of episode `k`:
`σ(M*) ⊔ σ(M_0, …, M_{k-1}) ⊔ σ(H_{t_k})`. -/
abbrev beforeSigma (sel : Θ → Policy S A τ) {Ω : Type} (Mstar : Ω → Θ) (Msamp : ℕ → Ω → Θ)
    (st : ℕ → Fin (τ + 1) → Ω → Fin S) (rw : ℕ → Fin τ → Ω → ℝ) (k : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap Mstar inferInstance
    ⊔ (⨆ l < k, MeasurableSpace.comap (Msamp l) inferInstance)
    ⊔ MeasurableSpace.comap (histOf sel Msamp st rw k) inferInstance

/-- The information just before the reward of step `j` of episode `k`: everything before episode
`k`, the sample `M_k`, the states `s_{k,0}, …, s_{k,j}` and the rewards `r_{k,0}, …, r_{k,j-1}`. -/
abbrev preSigma (sel : Θ → Policy S A τ) {Ω : Type} (Mstar : Ω → Θ) (Msamp : ℕ → Ω → Θ)
    (st : ℕ → Fin (τ + 1) → Ω → Fin S) (rw : ℕ → Fin τ → Ω → ℝ) (k : ℕ) (j : Fin τ) :
    MeasurableSpace Ω :=
  beforeSigma sel Mstar Msamp st rw k
    ⊔ MeasurableSpace.comap (Msamp k) inferInstance
    ⊔ (⨆ i ≤ j.castSucc, MeasurableSpace.comap (st k i) inferInstance)
    ⊔ (⨆ i < j, MeasurableSpace.comap (rw k i) inferInstance)

/-- A run of posterior sampling for reinforcement learning (PSRL, arXiv:1306.0940v5, §2–3, p. 3,
and the Algorithm box) on a probability space `(Ω, μ)`, for the MDP family `F`, the initial
distribution `ρ`, the prior `f` and the optimal-policy map `sel : θ ↦ µ^θ`.
Episodes are 0-based (Lean episode `k` is the paper's episode `k + 1`), steps are 0-based.

* `Mstar` is the true MDP `M*`, with law `f`;
* `Msamp k` is the sampled MDP `M_k`; the policy of episode `k` is `µ_k = sel (Msamp k)`;
* `st k j` (`j = 0, …, τ`) are the states and `rw k j` (`j < τ`) the rewards of episode `k`;
  the actions are `a_{k,j} = µ_k(s_{k,j}, j)` (see `PSRLRun.act`).

The conditional laws are stated with conditional expectations of indicators:
1. `post_sample`: given everything before episode `k` (`M*`, `M_0, …, M_{k-1}` and `H_{t_k}`),
   `M_k` has the posterior law of `M*` given `H_{t_k}`;
2. `reset`: given that and `M_k`, the first state of episode `k` is drawn from `ρ`;
3. `reward`: given everything up to the current state, the reward has law `R^{M*}_{a}(s)`;
4. `transition`: given everything up to the current reward, the next state has law
   `P^{M*}_{a}(·|s)`. -/
structure PSRLRun (F : MDPFamily S A Θ) (ρ : Fin S → ℝ) (f : Measure Θ)
    (sel : Θ → Policy S A τ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) where
  Mstar : Ω → Θ
  Msamp : ℕ → Ω → Θ
  st : ℕ → Fin (τ + 1) → Ω → Fin S
  rw : ℕ → Fin τ → Ω → ℝ
  measurable_Mstar : Measurable Mstar
  measurable_Msamp : ∀ k, Measurable (Msamp k)
  measurable_st : ∀ k j, Measurable (st k j)
  measurable_rw : ∀ k j, Measurable (rw k j)
  /-- `f` is the distribution of `M*`. -/
  law_Mstar : μ.map Mstar = f
  /-- Posterior sampling: `M_k ∼ f(·|H_{t_k})`, with fresh randomness. -/
  post_sample : ∀ (k : ℕ) (B : Set Θ), MeasurableSet B →
    μ[(Msamp k ⁻¹' B).indicator (fun _ => (1 : ℝ)) | beforeSigma sel Mstar Msamp st rw k]
      =ᵐ[μ]
    μ[(Mstar ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (histOf sel Msamp st rw k) inferInstance]
  /-- Reset: the first state of every episode is drawn afresh from `ρ`. -/
  reset : ∀ (k : ℕ) (s : Fin S),
    μ[{ω | st k 0 ω = s}.indicator (fun _ => (1 : ℝ)) |
        beforeSigma sel Mstar Msamp st rw k ⊔ MeasurableSpace.comap (Msamp k) inferInstance]
      =ᵐ[μ] fun _ => ρ s
  /-- Rewards are drawn from `R^{M*}_{a_{k,j}}(s_{k,j})`. -/
  reward : ∀ (k : ℕ) (j : Fin τ) (B : Set ℝ), MeasurableSet B →
    μ[{ω | rw k j ω ∈ B}.indicator (fun _ => (1 : ℝ)) | preSigma sel Mstar Msamp st rw k j]
      =ᵐ[μ] fun ω =>
        (F.ν (st k j.castSucc ω) (sel (Msamp k ω) (st k j.castSucc ω) j) (Mstar ω) B).toReal
  /-- Transitions are drawn from `P^{M*}_{a_{k,j}}(·|s_{k,j})`. -/
  transition : ∀ (k : ℕ) (j : Fin τ) (s' : Fin S),
    μ[{ω | st k j.succ ω = s'}.indicator (fun _ => (1 : ℝ)) |
        preSigma sel Mstar Msamp st rw k j ⊔ MeasurableSpace.comap (rw k j) inferInstance]
      =ᵐ[μ] fun ω =>
        F.P (Mstar ω) (st k j.castSucc ω) (sel (Msamp k ω) (st k j.castSucc ω) j) s'

namespace PSRLRun

variable {F : MDPFamily S A Θ} {ρ : Fin S → ℝ} {f : Measure Θ} {sel : Θ → Policy S A τ}
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The action `a_{k,j} = µ_k(s_{k,j}, j)` with `µ_k = µ^{M_k}`. -/
def act (R : PSRLRun F ρ f sel μ) (k : ℕ) (j : Fin τ) (ω : Ω) : Fin A :=
  sel (R.Msamp k ω) (R.st k j.castSucc ω) j

/-- The history `H_{t_k}`: the states, actions and rewards of episodes `0, …, k - 1`. -/
def hist (R : PSRLRun F ρ f sel μ) (k : ℕ) (ω : Ω) : Hist S A τ k :=
  histOf sel R.Msamp R.st R.rw k ω

/-- `σ(H_{t_k})`. -/
abbrev histSigma (R : PSRLRun F ρ f sel μ) (k : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (R.hist k) inferInstance

/-- `σ(M*, M_k)`. -/
abbrev pairSigma (R : PSRLRun F ρ f sel μ) (k : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap R.Mstar inferInstance ⊔ MeasurableSpace.comap (R.Msamp k) inferInstance

/-- The regret of episode `k` (p. 3):
`Δ_k = ∑_s ρ(s) (V^{M*}_{µ*,1}(s) − V^{M*}_{µ_k,1}(s))`, `µ* = µ^{M*}`, `µ_k = µ^{M_k}`. -/
noncomputable def Δ (R : PSRLRun F ρ f sel μ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ s, ρ s * (value F (R.Mstar ω) (sel (R.Mstar ω)) 0 s
    - value F (R.Mstar ω) (sel (R.Msamp k ω)) 0 s)

/-- (3), p. 5: `Δ̃_k = ∑_s ρ(s) (V^{M_k}_{µ_k,1}(s) − V^{M*}_{µ_k,1}(s))`. -/
noncomputable def Δtilde (R : PSRLRun F ρ f sel μ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ s, ρ s * (value F (R.Msamp k ω) (sel (R.Msamp k ω)) 0 s
    - value F (R.Mstar ω) (sel (R.Msamp k ω)) 0 s)

/-- `Regret(T, π^PS_τ) = ∑_{k=1}^{⌈T/τ⌉} Δ_k` (p. 3), with 0-based episodes. -/
noncomputable def regret (R : PSRLRun F ρ f sel μ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range ⌈(T : ℝ) / τ⌉₊, R.Δ k ω

/-- The one-step Bellman error of (6), p. 6, at (0-based) step `j` of episode `k`:
`(T^k_{µ_k(·,j)} − T^*_{µ_k(·,j)}) V^k_{µ_k,j+1}(s_{k,j})`, where `T^k = T^{M_k}`,
`T^* = T^{M*}` and `V^k_{µ_k,j+1}` is the value of `µ_k` in `M_k` from the next step on. -/
noncomputable def bellmanErr (R : PSRLRun F ρ f sel μ) (k : ℕ) (j : Fin τ) (ω : Ω) : ℝ :=
  bellman F (R.Msamp k ω) (fun s => sel (R.Msamp k ω) s j)
      (value F (R.Msamp k ω) (sel (R.Msamp k ω)) ((j : ℕ) + 1)) (R.st k j.castSucc ω)
    - bellman F (R.Mstar ω) (fun s => sel (R.Msamp k ω) s j)
      (value F (R.Msamp k ω) (sel (R.Msamp k ω)) ((j : ℕ) + 1)) (R.st k j.castSucc ω)

end PSRLRun

end PosteriorSamplingRL.Regret


