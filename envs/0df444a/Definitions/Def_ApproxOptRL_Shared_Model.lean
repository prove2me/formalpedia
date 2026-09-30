-- Prove2me | Definitions.Def_ApproxOptRL_Shared_Model
-- name    : ApproxOptRL_Shared_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:42:54.595567+00:00
-- url     : https://prove2.me/theorems/744981d4-1104-4fc0-acb8-352367259e26
-- title:
--   Kakade–Langford MDP layer: normalized value $V_\pi$, $Q_\pi$, advantage $A_\pi$, discounted future state distribution $d_{\pi,\mu}$, and $\eta_\mu$
-- statement:
--   This file fixes the objects of §2 of Kakade and Langford (ICML 2002) for a finite Markov decision process.
--
--   Let $S$ and $A$ be finite nonempty sets of states and actions, let $P(s';s,a)$ be the transition probabilities (for each $(s,a)$ a probability distribution over next states $s'$), let $\mathcal R : S\times A\to[0,R]$ be the reward function, and let $0\le\gamma<1$ be the discount factor. A stochastic policy $\pi(a;s)$ is, for each state $s$, a probability distribution over actions.
--
--   1. A **state distribution** $\mu$ is a vector of nonnegative weights on $S$ summing to $1$.
--   2. The **normalized value function** is
--   $$V_\pi(s) = (1-\gamma)\,E\Big[\sum_{t=0}^\infty \gamma^t\,\mathcal R(s_t,a_t)\,\Big|\,\pi,s\Big],$$
--   where $s_0=s$, $a_t\sim\pi(\cdot\,;s_t)$ and $s_{t+1}\sim P(\cdot\,;s_t,a_t)$.
--   3. The **state-action value** is $Q_\pi(s,a) = (1-\gamma)\mathcal R(s,a) + \gamma\,E_{s'\sim P(s';s,a)}[V_\pi(s')]$, and the **advantage** is $A_\pi(s,a) = Q_\pi(s,a) - V_\pi(s)$.
--   4. $\Pr(s_t=s;\pi,\mu)$ is the probability of being in $s$ at time $t$ when $s_0\sim\mu$ and $\pi$ is followed, and the **$\gamma$-discounted future state distribution** is
--   $$d_{\pi,\mu}(s) = (1-\gamma)\sum_{t=0}^\infty \gamma^t \Pr(s_t=s;\pi,\mu). \qquad (2.1)$$
--   5. The performance measure is $\eta_\mu(\pi) = E_{s\sim\mu}[V_\pi(s)]$.
--
--   These are the objects in which both missions of the series are stated, and the definition is reviewed once for both: `01-cpi` (Theorem 4.1, Corollary 4.2, Theorem 4.4 and Lemma 6.1; §2, p. 2 and §4, p. 4, used on pp. 4–6 and 8) and `02-policy-quality` (Lemma 6.1 and Theorem 6.2; §2, p. 2 and §4, p. 4, used on p. 6). Pages are PDF pages (the paper has no printed page numbers).
--
--   **Formalization Note** Policies are functions `π : S → A → ℝ` with `π s a` the paper's $\pi(a;s)$ (note the argument order), and `P s a s'` is the paper's $P(s';s,a)$. $V_\pi$ is $(1-\gamma)$ times the published unnormalized series `PolicyValue` (the series itself, not a Bellman fixed point). $d_{\pi,\mu}$ is written with `tsum`; under the standing hypotheses (a transition kernel, a policy, $0\le\gamma<1$) the series converges.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 2, §2 (value function, state-action value, advantage, eq. (2.1), η_D) and p. 4, §4 (η_μ)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace ApproxOptRL.Shared

open FoundationsML.ReinforcementLearning

/-- A state distribution on the finite state space `S`: nonnegative weights summing to one
(the start distribution `D` and the restart distribution `μ` of Kakade–Langford, ICML 2002, §2,
p. 2 and §4, p. 4). -/
def IsStateDist {S : Type} [Fintype S] (μ : S → ℝ) : Prop :=
  (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1

/-- The normalized value function of Kakade–Langford (ICML 2002, §2, p. 2):
`V_π(s) = (1 - γ) E[∑_{t ≥ 0} γ^t R(s_t, a_t) | π, s]`.
`PolicyValue π P r γ s` is the unnormalized series `∑' t, γ^t E[R(s_t,a_t) | s_0 = s]`.
Here `P s a s'` is the paper's `P(s'; s, a)` and `π s a` is the paper's `π(a; s)`. -/
noncomputable def value {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (s : S) : ℝ :=
  (1 - γ) * PolicyValue π P r γ s

/-- The state-action value (ICML 2002, §2, p. 2):
`Q_π(s, a) = (1 - γ) R(s, a) + γ E_{s' ∼ P(s'; s, a)}[V_π(s')]`. -/
noncomputable def qValue {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ) * r s a + γ * ∑ s', P s a s' * value P r γ π s'

/-- The advantage (ICML 2002, §2, p. 2): `A_π(s, a) = Q_π(s, a) - V_π(s)`. -/
noncomputable def advantage {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (s : S) (a : A) : ℝ :=
  qValue P r γ π s a - value P r γ π s

/-- `Pr(s_t = s; π, μ)`: the probability of being in state `s` at time `t` when `s_0 ∼ μ` and
the policy `π` is followed (ICML 2002, §2, p. 2, inside (2.1)). -/
noncomputable def stateProb {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (π : S → A → ℝ) (μ : S → ℝ) (t : ℕ) (s : S) : ℝ :=
  ∑ s₀, μ s₀ * OccupationDist π P s₀ t s

/-- The `γ`-discounted future state distribution, eq. (2.1) (ICML 2002, p. 2):
`d_{π,μ}(s) = (1 - γ) ∑_{t ≥ 0} γ^t Pr(s_t = s; π, μ)`.
`d_{π,s}` is this at the point mass `fun s' => if s' = s then 1 else 0`. -/
noncomputable def futureStateDist {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (γ : ℝ) (π : S → A → ℝ) (μ : S → ℝ) (s : S) : ℝ :=
  (1 - γ) * ∑' t : ℕ, γ ^ t * stateProb P π μ t s

/-- The performance measure `η_μ(π) = E_{s ∼ μ}[V_π(s)]` (ICML 2002, §2, p. 2 for `η_D`;
§4, p. 4 for `η_μ`). -/
noncomputable def eta {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (μ : S → ℝ) : ℝ :=
  ∑ s, μ s * value P r γ π s

end ApproxOptRL.Shared


