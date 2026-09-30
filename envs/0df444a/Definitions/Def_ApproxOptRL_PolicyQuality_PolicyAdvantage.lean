-- Prove2me | Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
-- name    : ApproxOptRL_PolicyQuality_PolicyAdvantage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:56:59.049703+00:00
-- url     : https://prove2.me/theorems/890538d9-4cef-4807-a3a4-e5ce7522efd2
-- title:
--   Policy advantage $\mathbb A_{\pi,\mu}(\pi')$, its optimum $\mathrm{OPT}(\mathbb A_{\pi,\mu})$, and optimal policies (Kakade–Langford 2002)
-- statement:
--   In the setting of the discounted MDP layer (normalized values $V_\pi$, advantages $A_\pi$ and discounted future state distributions $d_{\pi,\mu}$), this module defines three objects of Kakade and Langford (ICML 2002).
--
--   1. The **policy advantage** of a policy $\pi'$ with respect to a policy $\pi$ and a state distribution $\mu$ (§4.1, p. 4):
--   $$\mathbb A_{\pi,\mu}(\pi') = E_{s\sim d_{\pi,\mu}}\Big[E_{a\sim\pi'(a;s)}\big[A_\pi(s,a)\big]\Big] = \sum_s d_{\pi,\mu}(s)\sum_a\pi'(a;s)A_\pi(s,a).$$
--   The states are weighted by the future state distribution of the current policy $\pi$, not of $\pi'$.
--   2. The **optimal policy advantage** (Definition 4.3, p. 5):
--   $$\mathrm{OPT}(\mathbb A_{\pi,\mu}) = \max_{\pi'}\mathbb A_{\pi,\mu}(\pi'),$$
--   the maximum over all stochastic policies $\pi'$.
--   3. An **optimal policy** (§2, p. 2): a stochastic policy $\pi^*$ with $V_\pi(s)\le V_{\pi^*}(s)$ for every stochastic policy $\pi$ and every state $s$, i.e. one that simultaneously maximizes the value at all states.
--
--   $\mathrm{OPT}(\mathbb A_{\pi,\mu})$ measures how much a single greedy step could still improve on $\pi$; Theorem 6.2 converts a small value of it into a bound on the suboptimality of $\pi$.
--
--   **Formalization Note** $\mathrm{OPT}$ is written as the supremum (`sSup`) of the set of values $\mathbb A_{\pi,\mu}(\pi')$ over policies $\pi'$. For a transition kernel, a policy $\pi$, a state distribution $\mu$ and bounded rewards this set is nonempty and bounded, and the maximum is attained (by a policy greedy with respect to $A_\pi$), so the supremum is the paper's maximum. Optimality is with respect to the paper's policy class of stationary stochastic policies $\pi(a;s)$.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 4, §4.1 (policy advantage); p. 5, Definition 4.3 (OPT); p. 2, §2 (optimal policy)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
open ApproxOptRL.Shared

namespace ApproxOptRL.PolicyQuality

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

/-- An optimal policy (ICML 2002, §2, p. 2: "a policy exists which simultaneously maximizes
`V_π(s)` for all states"): a stationary stochastic policy `πstar` whose normalized value is at
least that of every stationary stochastic policy `π`, at every state. -/
def IsOptimalPolicy {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (πstar : S → A → ℝ) : Prop :=
  IsPolicy πstar ∧ ∀ π : S → A → ℝ, IsPolicy π → ∀ s : S, value P r γ π s ≤ value P r γ πstar s

end ApproxOptRL.PolicyQuality


