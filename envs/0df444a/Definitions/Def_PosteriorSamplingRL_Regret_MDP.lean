-- Prove2me | Definitions.Def_PosteriorSamplingRL_Regret_MDP
-- name    : PosteriorSamplingRL_Regret_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:26.228822+00:00
-- url     : https://prove2.me/theorems/a3dd1b6e-9f75-4456-ac4e-c767233681d4
-- title:
--   §2, pp. 2–3; §5, p. 5 — Θ-parametrized finite MDPs, path-defined values V^M_{µ,i}, Bellman operator, optimal policies
-- statement:
--   This module fixes the model of §2 of Osband, Russo and Van Roy: a finite-horizon MDP $M=(\mathcal S,\mathcal A,R^M,P^M,\tau,\rho)$ whose reward distributions and transition probabilities are unknown and random.
--
--   1. **MDP family.** The states are $\mathcal S=\{0,\dots,S-1\}$ and the actions $\mathcal A=\{0,\dots,A-1\}$. MDPs are indexed by a parameter $\theta$ in a measurable space $\Theta$. For every $\theta$, state $s$ and action $a$, $P^\theta_a(\cdot\mid s)$ is a probability vector on $\mathcal S$, measurable in $\theta$, and $R^\theta_a(s)$ is a probability measure on $\mathbb R$ supported on $[0,1]$, depending measurably on $\theta$ (a Markov kernel from $\Theta$ to $\mathbb R$). A prior over MDPs is a measure on $\Theta$; taking $\Theta$ to be the space of MDPs itself shows that every prior is of this form.
--   2. **Mean reward.** $\overline R^\theta_a(s)=\int r\,R^\theta_a(s)(dr)$.
--   3. **Initial distribution.** $\rho$ is a probability vector on $\mathcal S$ (nonnegative entries summing to one).
--   4. **Policies.** A deterministic policy is a map $\mu:\mathcal S\times\{1,\dots,\tau\}\to\mathcal A$.
--   5. **Value.** For a policy $\mu$, a step $i$ and a state $s$,
--   $$
--   V^\theta_{\mu,i}(s)=\mathbb E_{\theta,\mu}\Big[\sum_{j=i}^{\tau}\overline R^\theta_{a_j}(s_j)\,\Big|\,s_i=s\Big],
--   $$
--   where $a_j=\mu(s_j,j)$ and $s_{j+1}\sim P^\theta_{a_j}(\cdot\mid s_j)$. The expectation is computed from the laws $\Pr_{\theta,\mu}(s_j=s'\mid s_i=s)$ of the visited states, obtained by composing the one-step transition matrices; $V^\theta_{\mu,\tau+1}=0$.
--   6. **Bellman operator.** For a stationary rule $d:\mathcal S\to\mathcal A$ and $V:\mathcal S\to\mathbb R$,
--   $$
--   \mathcal T^\theta_d V(s)=\overline R^\theta_{d(s)}(s)+\sum_{s'\in\mathcal S}P^\theta_{d(s)}(s'\mid s)\,V(s').
--   $$
--   7. **Optimality.** $\mu$ is optimal for $\theta$ if $V^\theta_{\mu,i}(s)\ge V^\theta_{\mu',i}(s)$ for every policy $\mu'$, every state $s$ and every step $i=1,\dots,\tau$.
--
--   These objects are the vocabulary of every statement of the mission: the regret compares values of optimal and sampled policies, and the analysis rewrites value differences with the Bellman operator.
--
--   **Formalization Note** States and actions are `Fin S` and `Fin A`; steps are 0-based, so Lean's `value F θ π j` is the paper's $V^\theta_{\mu,j+1}$, `value F θ π 0` is $V^\theta_{\mu,1}$ and `value F θ π τ` is $V^\theta_{\mu,\tau+1}=0$. The policy is written `π` in Lean (the paper's $\mu$). The value is defined from the state laws (`occ`, `stepDist`) and the sum of the page's definition, not by the Bellman recursion, so that the dynamic programming equation (Lemma 2) is a theorem. `stepKernel` and `rewardAt` are total: at steps $j\ge\tau$, which never enter `value`, they are the identity and $0$. The transition-kernel property is the published `FoundationsML.ReinforcementLearning.IsTransitionKernel`.
-- source:
--   arXiv:1306.0940v5, §2, pp. 2–3, and §5, p. 5

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace PosteriorSamplingRL.Regret

open MeasureTheory ProbabilityTheory FoundationsML.ReinforcementLearning

/-- A measurable family of finite MDPs `M_θ = (S, A, R^θ, P^θ, τ, ρ)` indexed by a parameter
`θ ∈ Θ` (arXiv:1306.0940v5, §2, p. 2). States are `Fin S`, actions `Fin A`.
`P θ s a s'` is `P^θ_a(s'|s)`, a probability vector in `s'` for every `(θ, s, a)`;
`ν s a θ` is the reward distribution `R^θ_a(s)`, a probability measure on `ℝ` supported on `[0, 1]`
for every `θ`. A prior over MDPs is a measure on `Θ`. -/
structure MDPFamily (S A : ℕ) (Θ : Type) [MeasurableSpace Θ] where
  /-- transition probabilities `P^θ_a(s'|s)` -/
  P : Θ → Fin S → Fin A → Fin S → ℝ
  P_kernel : ∀ θ, IsTransitionKernel (P θ)
  P_measurable : ∀ s a s', Measurable fun θ => P θ s a s'
  /-- reward distributions `R^θ_a(s)` -/
  ν : Fin S → Fin A → Kernel Θ ℝ
  ν_markov : ∀ s a, IsMarkovKernel (ν s a)
  ν_support : ∀ θ s a, ν s a θ (Set.Icc (0 : ℝ) 1)ᶜ = 0

/-- A probability distribution on a finite type (the initial state distribution `ρ`). -/
def IsDist {X : Type*} [Fintype X] (ρ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ ρ x) ∧ ∑ x, ρ x = 1

/-- A deterministic policy (the paper's `µ(s, i)`, `i = 1, …, τ`; written `π` in Lean); Lean step `j : Fin τ` is the paper's
step `i = j + 1` (p. 3). -/
abbrev Policy (S A τ : ℕ) := Fin S → Fin τ → Fin A

variable {S A τ : ℕ} {Θ : Type} [MeasurableSpace Θ]

/-- The mean reward `R̄^θ_a(s) = ∫ r dR^θ_a(s)(r)` (p. 3). -/
noncomputable def meanReward (F : MDPFamily S A Θ) (θ : Θ) (s : Fin S) (a : Fin A) : ℝ :=
  ∫ r, r ∂(F.ν s a θ)

/-- The mean reward collected at (0-based) step `j : ℕ` in state `s` under `π`; steps `j ≥ τ` never occur in the
definitions below (the transition is the identity there and the reward is `0`). -/
noncomputable def rewardAt (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) (j : ℕ) (s : Fin S) :
    ℝ :=
  if h : j < τ then meanReward F θ s (π s ⟨j, h⟩) else 0

/-- One-step transition of the Markov chain induced by `π` in `M_θ` at (0-based) step `j`:
`P^θ_{π(s,j)}(s'|s)` for `j < τ`, the identity for `j ≥ τ` (never used). -/
noncomputable def stepKernel (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) (j : ℕ)
    (s s' : Fin S) : ℝ :=
  if h : j < τ then F.P θ s (π s ⟨j, h⟩) s' else if s = s' then 1 else 0

/-- `occ F θ π i s n s' = Pr_{θ,π}(s_{i+n} = s' | s_i = s)`: the law of the state `n` steps after
step `i`, started from `s`, when `a_j = π(s_j, j)` and `s_{j+1} ∼ P^θ_{a_j}(·|s_j)`. -/
noncomputable def occ (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) (i : ℕ) (s : Fin S) :
    ℕ → Fin S → ℝ
  | 0 => fun s' => if s' = s then 1 else 0
  | n + 1 => fun s' => ∑ s'', occ F θ π i s n s'' * stepKernel F θ π (i + n) s'' s'

/-- `stepDist F θ π i s j s' = Pr_{θ,π}(s_j = s' | s_i = s)` for `j ≥ i`. -/
noncomputable def stepDist (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) (i : ℕ) (s : Fin S)
    (j : ℕ) (s' : Fin S) : ℝ :=
  occ F θ π i s (j - i) s'

/-- The path-defined value function (p. 3), in 0-based steps:
`value F θ π i s = E_{θ,π}[∑_{j=i}^{τ-1} R̄^θ_{a_j}(s_j) | s_i = s]`, i.e. the paper's
`V^θ_{π,i+1}(s)`. In particular `value F θ π 0 = V^θ_{π,1}` and `value F θ π τ = V^θ_{π,τ+1} = 0`. -/
noncomputable def value (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) (i : ℕ) (s : Fin S) : ℝ :=
  ∑ j ∈ Finset.Ico i τ, ∑ s', stepDist F θ π i s j s' * rewardAt F θ π j s'

/-- The Bellman operator (§5, p. 5): for a stationary decision rule `d : S → A` and
`V : S → ℝ`, `T^θ_d V(s) = R̄^θ_{d(s)}(s) + ∑_{s'} P^θ_{d(s)}(s'|s) V(s')`. -/
noncomputable def bellman (F : MDPFamily S A Θ) (θ : Θ) (d : Fin S → Fin A) (V : Fin S → ℝ)
    (s : Fin S) : ℝ :=
  meanReward F θ s (d s) + ∑ s', F.P θ s (d s) s' * V s'

/-- `π` is optimal for `M_θ` (p. 3): `V^θ_{π,i}(s) = max_{π'} V^θ_{π',i}(s)` for every state `s`
and every step `i = 1, …, τ` (Lean `j = i - 1 < τ`). -/
def IsOptimal (F : MDPFamily S A Θ) (θ : Θ) (π : Policy S A τ) : Prop :=
  ∀ (π' : Policy S A τ) (j : ℕ), j < τ → ∀ s, value F θ π' j s ≤ value F θ π j s

end PosteriorSamplingRL.Regret


