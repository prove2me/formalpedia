-- Prove2me | Definitions.Def_AggStatePG_qDist
-- name    : AggStatePG_qDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:57.968649+00:00
-- url     : https://prove2.me/theorems/d6d3eb66-a208-4c99-9f02-49ee4b71d127
-- title:
--   State-action value $Q_\pi(s,d)$ of an action distribution
-- statement:
--   For a policy $\pi$, a state $s$ and an action distribution $d\in\Delta(\mathcal A)$, the **state-action value function** is
--   $$Q_\pi(s,d)=r(s,d)+\gamma\sum_{s'\in\mathcal S}P(s'\mid s,d)\,V_\pi(s')=\sum_{a\in\mathcal A}d_a\,Q_\pi(s,a),$$
--   the expected total discounted reward of sampling an action from $d$ in state $s$ and following $\pi$ thereafter. For $d=e_a$ it is $Q_\pi(s,a)$.
--
--   **Formalization Note** Defined as $\sum_a d_aQ_\pi(s,a)$ with the published `QFunction`; the two expressions agree by linearity in $d$. The page prints $V_\pi(s)$ inside the sum over $s'$; $V_\pi(s')$ is meant.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §2, p.5 (definition of Q_π(s,d))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

open FoundationsML.ReinforcementLearning

namespace AggStatePG

/-- The **state-action value of an action distribution** `Q_π(s,d)` (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §2, p.5):
`Q_π(s,d) = r(s,d) + γ ∑_{s'} P(s'|s,d) V_π(s')` for `d ∈ Δ(A)`, the expected total discounted reward
of sampling an action from `d` in state `s` and applying `π` thereafter.

**Formalization Note.** Written as `∑_a d_a Q_π(s,a)` with `Q_π(s,a)` the published `QFunction`
(`r(s,a) + γ ∑_{s'} P(s'|s,a) V_π(s')`); the two expressions are equal by linearity of
`r(s,d)` and `P(s'|s,d)` in `d` (p.4), and `Q_π(s, e_a) = Q_π(s,a)`. The page prints `V_π(s)` inside the
sum; the sum over `s'` shows `V_π(s')` is meant. -/
noncomputable def qDist {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) (d : A → ℝ) : ℝ :=
  ∑ a : A, d a * QFunction π P r γ s a

end AggStatePG


