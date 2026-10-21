-- Prove2me | Definitions.Def_DouyinDQ_Bias_FiniteMDP
-- name    : DouyinDQ_Bias_FiniteMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:16.18132+00:00
-- url     : https://prove2.me/theorems/f7be5f99-3422-4a91-877c-215f6b344543
-- title:
--   Finite Markov decision process, stationary policies, and induced transition and reward
-- statement:
--   A **finite Markov decision process** has finite state and action sets $S$ and $A$, one transition matrix $P_a$ for each action, a conditional mean reward $r(s,a)$, and an initial state law $\rho$. Its standing conditions are
--   $$P_a(s,s')\ge0,\qquad \sum_{s'}P_a(s,s')=1,\qquad \rho(s)\ge0,\qquad \sum_s\rho(s)=1.$$
--   A stationary policy $\pi$ assigns nonnegative action probabilities summing to one at each state. It induces $P_\pi(s,s')=\sum_a\pi(s,a)P_a(s,s')$ and $r_\pi(s)=\sum_a\pi(s,a)r(s,a)$.
--
--   These common objects underlie every result in the mission. The reward is its conditional mean because the claims about expected total reward and estimator bias depend only on that mean.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, pp. 3–4, §3; p. 7, §5.1

import Mathlib

namespace DouyinDQ.Bias

/-- A finite Markov decision process with action-dependent transition matrices,
conditional mean rewards, and an initial state distribution. -/
structure MDP (S A : Type) [Fintype S] [Fintype A] where
  P : A → Matrix S S ℝ
  r : S → A → ℝ
  ρ : S → ℝ

/-- The transition matrices and initial law are stochastic. -/
def MDP.Standing {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) : Prop :=
  (∀ a s s', 0 ≤ M.P a s s') ∧
  (∀ a s, ∑ s', M.P a s s' = 1) ∧
  (∀ s, 0 ≤ M.ρ s) ∧
  ∑ s, M.ρ s = 1

/-- A stationary randomized policy. -/
def IsPolicy {S A : Type} [Fintype S] [Fintype A]
    (π : S → A → ℝ) : Prop :=
  (∀ s a, 0 ≤ π s a) ∧ ∀ s, ∑ a, π s a = 1

/-- The transition matrix induced by a policy. -/
def Ppol {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (π : S → A → ℝ) : Matrix S S ℝ :=
  fun s s' => ∑ a, π s a * M.P a s s'

/-- The conditional mean reward under a policy. -/
def rpol {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (π : S → A → ℝ) : S → ℝ :=
  fun s => ∑ a, π s a * M.r s a

end DouyinDQ.Bias


