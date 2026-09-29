-- Prove2me | Definitions.Def_FoundationsRL_Contextual_regret
-- name    : FoundationsRL_Contextual_regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:59:20.412839+00:00
-- url     : https://prove2.me/theorems/d6ca01bb-5653-4f9c-82bb-11a82524c6ed
-- title:
--   Contextual bandit regret (Eq. 3.3)
-- statement:
--   This definition formalizes **regret** for the contextual bandit protocol (Eq. (3.3), Foster &
--   Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, p. 39).
--
--   Over $T$ rounds, a decision-maker observes a context $x_t \in X$, selects an action
--   $\pi_t \in \Pi = \{1,\dots,A\}$ according to a distribution $p_t \in \Delta(\Pi)$, and
--   observes a reward whose mean is $f^\star(x_t,\pi_t)$. Writing
--   $\pi^\star(x) := \arg\max_{\pi} f^\star(x,\pi)$ for the optimal action at context $x$, the
--   regret over the fixed (possibly adversarial) context sequence $x_1,\dots,x_T$ is
--
--   $$
--   \mathrm{Reg} := \sum_{t=1}^T f^\star(x_t, \pi^\star(x_t)) -
--   \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\bigl[f^\star(x_t,\pi_t)\bigr].
--   $$
--
--   This measures the gap between the reward of the best context-dependent policy and the
--   decision-maker's expected reward, and is the performance criterion for every contextual
--   bandit algorithm and result in this mission.
--
--   **Formalization Note** The optimal action $\pi^\star$ is supplied as a parameter `pistar`
--   together with the hypothesis that it is optimal for `fstar` at every context, rather than
--   constructed via an explicit argmax, following the same convention used for the greedy action
--   in `IsIGW`. The expectation $\mathbb{E}_{\pi_t \sim p_t}$ is the finite weighted sum
--   $\sum_a p_t(a) \cdot (\cdot)$, since $p_t$ is represented as an explicit probability vector on
--   the finite type `Fin A` rather than as a measure-theoretic distribution.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 39, Eq. (3.3)

import Mathlib

namespace FoundationsRL.Contextual

/-- Regret against the best-in-hindsight context-dependent policy, as defined for the
contextual bandit protocol (Foster & Rakhlin, *Foundations of Reinforcement Learning and
Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.3), p. 39):

`Reg := ∑_{t=1}^T fstar(x_t, pistar(x_t)) - ∑_{t=1}^T E_{π_t ∼ p_t}[fstar(x_t, π_t)]`,

the cumulative gap between the optimal policy's reward and the expected reward of the
decision-maker's realized action distributions `p : Fin T → Fin A → ℝ` (`p t` a probability
vector over `Fin A`) under context sequence `x` and ground-truth reward function `fstar`. -/
def regret {X : Type*} (A T : ℕ) (x : Fin T → X) (fstar : X → Fin A → ℝ) (pistar : X → Fin A)
    (p : Fin T → Fin A → ℝ) : ℝ :=
  ∑ t : Fin T, (fstar (x t) (pistar (x t)) - ∑ a : Fin A, p t a * fstar (x t) a)

end FoundationsRL.Contextual


