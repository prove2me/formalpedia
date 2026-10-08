-- Prove2me | Definitions.Def_PolicyGradTheory_ProjGA_MDP
-- name    : PolicyGradTheory_ProjGA_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:55:57.281551+00:00
-- url     : https://prove2.me/theorems/d04145ad-4934-4fa6-a8b6-2b39317fc3ff
-- title:
--   §3, pp. 9–12 — finite MDP setting, V^π(ρ), advantage A^π and the discounted state visitation d^π_ρ of (4)
-- statement:
--   This module fixes the standing setting of §3 of Agarwal, Kakade, Lee and Mahajan and the derived quantities used throughout the paper.
--
--   Let $\mathcal S$ and $\mathcal A$ be finite sets of states and actions, $P(s'\mid s,a)$ a transition kernel, $r:\mathcal S\times\mathcal A\to[0,1]$ a reward function and $\gamma\in[0,1)$ a discount factor. For a policy $\pi$ with value function $V^\pi$ and state–action value function $Q^\pi$ (the published definitions `PolicyValue` and `QFunction`), the module defines:
--
--   1. **Distributions.** A function $\mu:X\to\mathbb R$ on a finite set is a probability distribution, $\mu\in\Delta(X)$, if $\mu(x)\ge 0$ for all $x$ and $\sum_x\mu(x)=1$.
--   2. **Finite MDP.** The data $(P,r,\gamma)$ form a finite MDP if every $P(\cdot\mid s,a)$ is a probability distribution, $0\le r(s,a)\le 1$ for all $(s,a)$, and $0\le\gamma<1$.
--   3. **Value at a start distribution.** $V^\pi(\rho)=\mathbb E_{s_0\sim\rho}[V^\pi(s_0)]=\sum_{s}\rho(s)V^\pi(s)$.
--   4. **Advantage.** $A^\pi(s,a)=Q^\pi(s,a)-V^\pi(s)$.
--   5. **Discounted state visitation distribution** (4):
--   $$
--   d^\pi_\rho(s)=\mathbb E_{s_0\sim\rho}\Big[(1-\gamma)\sum_{t=0}^{\infty}\gamma^t\,\Pr{}^\pi(s_t=s\mid s_0)\Big].
--   $$
--
--   These objects are the vocabulary of every result of the paper: the objective $V^\pi(\mu)$ that policy gradient methods maximize, the performance difference lemma, and the distribution mismatch coefficient $\|d^{\pi^\star}_\rho/\mu\|_\infty$.
--
--   **Formalization Note** $\Pr^\pi(s_t=s\mid s_0)$ is the published `OccupationDist`. The text of this module is shared verbatim by all six missions of the series (sub-namespace aside), so that the copies can be merged.
-- source:
--   arXiv:1908.00261v5, §3, pp. 9–12, (4)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

namespace PolicyGradTheory.ProjGA

open FoundationsML.ReinforcementLearning

/-- A probability distribution on a finite type: nonnegative weights summing to one
(the start distributions `ρ, µ ∈ ∆(S)` of arXiv:1908.00261v5, §3, p. 9). -/
def IsDist {X : Type*} [Fintype X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- The standing setting of §3 (p. 9): a finite MDP with transition kernel `P`
(`P s a s'` = P(s'|s,a)), rewards `r(s,a) ∈ [0,1]` and discount factor `γ ∈ [0,1)`. -/
def IsFiniteMDP {S A : Type*} [Fintype S] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) : Prop :=
  IsTransitionKernel P ∧ (∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) ∧ 0 ≤ γ ∧ γ < 1

/-- `V^π(ρ) = E_{s₀∼ρ}[V^π(s₀)]` (p. 10). -/
noncomputable def valueAt {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ) : ℝ :=
  ∑ s, ρ s * PolicyValue π P r γ s

/-- The advantage `A^π(s,a) = Q^π(s,a) − V^π(s)` (p. 10). -/
noncomputable def advantage {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) (a : A) : ℝ :=
  QFunction π P r γ s a - PolicyValue π P r γ s

/-- The discounted state visitation distribution (4) (p. 11):
`d^π_ρ(s) = E_{s₀∼ρ}[(1−γ) ∑_{t≥0} γ^t Pr^π(s_t = s | s₀)]`. -/
noncomputable def visitation {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (s : S) : ℝ :=
  (1 - γ) * ∑' t : ℕ, γ ^ t * ∑ s₀, ρ s₀ * OccupationDist π P s₀ t s

end PolicyGradTheory.ProjGA


