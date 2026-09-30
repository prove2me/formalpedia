-- Prove2me | Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
-- name    : ApproxOptRL_CPI_PolicyAdvantage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:43:36.208813+00:00
-- url     : https://prove2.me/theorems/438e270a-6a0d-4d25-9ab4-ccdf777a22fe
-- title:
--   Policy advantage $\mathbb A_{\pi,\mu}(\pi')$, $\mathrm{OPT}(\mathbb A_{\pi,\mu})$, the conservative update (4.1) and $\varepsilon$-greedy policy choosers
-- statement:
--   This file fixes the objects of §4 of Kakade and Langford (ICML 2002), in the setting of the MDP layer (finite states and actions, transition probabilities $P$, rewards in $[0,R]$, discount $0\le\gamma<1$, advantage $A_\pi$ and discounted future state distribution $d_{\pi,\mu}$).
--
--   1. The **policy advantage** of a policy $\pi'$ with respect to a policy $\pi$ and a state distribution $\mu$ is
--   $$\mathbb A_{\pi,\mu}(\pi') = E_{s\sim d_{\pi,\mu}}\big[E_{a\sim\pi'(a;s)}[A_\pi(s,a)]\big] = \sum_s d_{\pi,\mu}(s)\sum_a \pi'(a;s)\,A_\pi(s,a).$$
--   The states are weighted by $d_{\pi,\mu}$, the distribution of the **old** policy $\pi$.
--   2. $\mathrm{OPT}(\mathbb A_{\pi,\mu}) = \max_{\pi'}\mathbb A_{\pi,\mu}(\pi')$, the maximum over all stochastic policies $\pi'$.
--   3. The **conservative update** (4.1): for $\alpha\in[0,1]$, $\pi_{\mathrm{new}}(a;s) = (1-\alpha)\pi(a;s) + \alpha\pi'(a;s)$.
--   4. An **$\varepsilon$-greedy policy chooser** $G_\varepsilon$ (Definition 4.3) maps every policy $\pi$ to a policy $\pi' = G_\varepsilon(\pi)$ with
--   $$\mathbb A_{\pi,\mu}(\pi') \ge \mathrm{OPT}(\mathbb A_{\pi,\mu}) - \varepsilon.$$
--
--   The policy advantage measures how much $\pi'$ picks actions with large advantage on the states visited by $\pi$ from $\mu$; the greedy chooser is the oracle that conservative policy iteration calls.
--
--   **Formalization Note** $\mathrm{OPT}$ is the real supremum `sSup` of the set of values $\mathbb A_{\pi,\mu}(\pi')$ over policies $\pi'$. For a transition kernel, a policy $\pi$, a state distribution $\mu$ and bounded rewards this set is nonempty and bounded (since $|A_\pi|\le R$ and $d_{\pi,\mu}$ is a probability vector), and its maximum is attained by a deterministic greedy policy, so `sSup` is the paper's $\max$. The chooser is formalized for the fixed restart distribution $\mu$ (the paper never varies $\mu$), and is only constrained on inputs that are policies.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 4, §4 eq. (4.1) and §4.1 (policy advantage); p. 5, Definition 4.3

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
open ApproxOptRL.Shared

namespace ApproxOptRL.CPI

open FoundationsML.ReinforcementLearning

/-- The policy advantage of `π'` with respect to `π` and `μ` (ICML 2002, §4.1, p. 4):
`𝔸_{π,μ}(π') = E_{s ∼ d_{π,μ}}[E_{a ∼ π'(a;s)}[A_π(s, a)]]`.
The states are weighted by `d_{π,μ}`, the discounted future state distribution of the
**old** policy `π`. -/
noncomputable def policyAdvantage {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (μ : S → ℝ)
    (π' : S → A → ℝ) : ℝ :=
  ∑ s, futureStateDist P γ π μ s * ∑ a, π' s a * advantage P r γ π s a

/-- `OPT(𝔸_{π,μ}) = max_{π'} 𝔸_{π,μ}(π')` (ICML 2002, Definition 4.3, p. 5), the maximum over
all stochastic policies `π'`, written as the supremum of the set of attained values. For a
transition kernel, a policy `π`, a state distribution `μ` and bounded rewards this set is
nonempty and bounded (and the maximum is attained). -/
noncomputable def optPolicyAdvantage {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (μ : S → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ π' : S → A → ℝ, IsPolicy π' ∧ policyAdvantage P r γ π μ π' = x}

/-- The conservative update rule, eq. (4.1) (ICML 2002, p. 4):
`π_new(a; s) = (1 - α) π(a; s) + α π'(a; s)`. -/
def mixPolicy {S A : Type} (α : ℝ) (π π' : S → A → ℝ) : S → A → ℝ :=
  fun s a => (1 - α) * π s a + α * π' s a

/-- An `ε`-greedy policy chooser (ICML 2002, Definition 4.3, p. 5), for the fixed restart
distribution `μ`: a map `G` sending every policy `π` to a policy `G π` with
`𝔸_{π,μ}(G π) ≥ OPT(𝔸_{π,μ}) - ε`. -/
def IsGreedyChooser {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ) (ε : ℝ)
    (G : (S → A → ℝ) → (S → A → ℝ)) : Prop :=
  ∀ π : S → A → ℝ, IsPolicy π →
    IsPolicy (G π) ∧ optPolicyAdvantage P r γ π μ - ε ≤ policyAdvantage P r γ π μ (G π)

end ApproxOptRL.CPI


