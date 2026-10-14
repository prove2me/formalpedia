-- Prove2me | Definitions.Def_FirstPriceLearning_GraphFeedback_BanditModel
-- name    : FirstPriceLearning_GraphFeedback_BanditModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:15.208196+00:00
-- url     : https://prove2.me/theorems/d577341e-8afa-47a2-9d02-0becb47f4a03
-- title:
--   Definitions 1–2: mean rewards and the regrets (4) and (5) of bandits with graph feedback and cross learning
-- statement:
--   This module fixes the mean rewards and regrets of Definition 1 (stochastic multi-armed bandits with graph feedback, p. 11) and Definition 2 (stochastic contextual bandits with graph feedback and cross learning, p. 14).
--
--   The action space is $\mathcal A = [K]$ and the context space $\mathcal C = [M]$. In Definition 1 nature draws iid reward vectors $r_t = (r_{t,a})_{a \in \mathcal A}$ from a joint law $P$ supported on $[0,1]^K$; the mean reward of action $a$ is $R_a = \mathbb E_P[r_a]$. For a sequence of actions $\pi = (a_1, \dots, a_T)$ the regret (4) is
--   $$
--   R_T(\pi) = \sum_{t=1}^T \Big(\max_{a \in \mathcal A} R_a - R_{a_t}\Big).
--   $$
--   In Definition 2 nature draws iid reward vectors $r_t = (r_{t,c,a})_{c \in \mathcal C, a \in \mathcal A}$ from a joint law $P$ supported on $[0,1]^{M \times K}$, the mean rewards are $R_{c,a} = \mathbb E_P[r_{c,a}]$, and for a context sequence $(c_1, \dots, c_T)$ and actions $(a_1, \dots, a_T)$ the regret (5) is
--   $$
--   R_T(\pi) = \sum_{t=1}^T \Big(\max_{a \in \mathcal A} R_{c_t,a} - R_{c_t,a_t}\Big).
--   $$
--   Both regrets are pseudo-regrets: they compare mean rewards, not realized rewards.
--
--   **Formalization Note** Actions are `Fin K`, contexts `Fin M`, rounds `Fin T` (paper round $t$ is Lean index $t-1$). The law $P$ is a measure on `Fin K → ℝ` resp. `Fin M → Fin K → ℝ`; the theorems assume it is a probability measure carried by $[0,1]^K$ resp. $[0,1]^{M\times K}$. The maximum over actions is a supremum over the finite type `Fin K`, nonempty since every theorem assumes $K \ge 1$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 11, Definition 1, (4); p. 14, Definition 2, (5)

import Mathlib

open MeasureTheory

namespace FirstPriceLearning.GraphFeedback

/-! Stochastic bandits with graph feedback (Definition 1, p. 11) and stochastic contextual
bandits with graph feedback and cross learning (Definition 2, p. 14) of Han, Zhou, Weissman,
arXiv:2003.09795v7: the mean rewards and the (pseudo-)regrets (4) and (5).

Actions are `Fin K`, contexts `Fin M`, rounds `Fin T` (paper time `t ∈ [T]` is Lean `t + 1`).
A reward vector of Definition 1 is an element of `Fin K → ℝ`; one of Definition 2 is an element
of `Fin M → Fin K → ℝ`, i.e. `(r_{c,a})_{c ∈ C, a ∈ A}`. The joint reward law `P` is a probability
measure on these vectors, supported on `[0,1]^K` resp. `[0,1]^{M × K}`; the theorems state these
hypotheses. The feedback graph is the relation `E` of `FeedbackGraph`. -/

/-- The mean reward `R_a = ∫ r_a dP` of action `a` (Definition 1). -/
noncomputable def meanRewardMAB {K : ℕ} (P : Measure (Fin K → ℝ)) (a : Fin K) : ℝ :=
  ∫ x, x a ∂P

/-- The regret (4) of the action sequence `(a_1, …, a_T)` for the mean rewards `R`:
`R_T(π) = ∑_{t=1}^T (max_{a ∈ A} R_a − R_{a_t})`. -/
noncomputable def regretMAB {K T : ℕ} (R : Fin K → ℝ) (a : Fin T → Fin K) : ℝ :=
  ∑ t, ((⨆ b : Fin K, R b) - R (a t))

/-- The mean reward `R_{c,a} = ∫ r_{c,a} dP` of action `a` under context `c` (Definition 2). -/
noncomputable def meanReward {M K : ℕ} (P : Measure (Fin M → Fin K → ℝ)) (c : Fin M)
    (a : Fin K) : ℝ :=
  ∫ x, x c a ∂P

/-- The regret (5) of the action sequence `(a_1, …, a_T)` against the context sequence
`(c_1, …, c_T)`: `R_T(π) = ∑_{t=1}^T (max_{a ∈ A} R_{c_t,a} − R_{c_t,a_t})`. -/
noncomputable def regret {M K T : ℕ} (P : Measure (Fin M → Fin K → ℝ)) (c : Fin T → Fin M)
    (a : Fin T → Fin K) : ℝ :=
  ∑ t, ((⨆ b : Fin K, meanReward P (c t) b) - meanReward P (c t) (a t))

end FirstPriceLearning.GraphFeedback


