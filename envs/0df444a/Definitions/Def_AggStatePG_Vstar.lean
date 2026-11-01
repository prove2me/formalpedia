-- Prove2me | Definitions.Def_AggStatePG_Vstar
-- name    : AggStatePG_Vstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:56.427925+00:00
-- url     : https://prove2.me/theorems/f6c5992e-e7b0-426c-811c-d106cb125911
-- title:
--   Optimal value function $V^*$
-- statement:
--   For a finite MDP with discount factor $\gamma\in(0,1)$, the **optimal value function** is
--   $$V^*(s)=\max_{\pi\in\Pi}V_\pi(s),$$
--   where $\Pi$ is the set of stationary randomized policies and $V_\pi(s)=\mathbb E^\pi_s\big[\sum_{t\ge0}\gamma^t r(s_t,a_t)\big]$. A policy $\pi^*$ is optimal if $V_{\pi^*}(s)=V^*(s)$ for every $s$.
--
--   **Formalization Note** Written as the supremum of $\{V_\pi(s):\pi\in\Pi\}$. With a nonempty action set this set is nonempty and bounded by $\max|r|/(1-\gamma)$, and an optimal deterministic policy attains it, so the supremum is the paper's maximum.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §2, p.4 (V* and optimal policy)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

open FoundationsML.ReinforcementLearning

namespace AggStatePG

/-- The **optimal value function** `V*(s) = max_{π ∈ Π} V_π(s)` (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §2, p.4),
where `Π` is the set of stationary randomized policies and
`V_π(s) = E^π_s[∑_{t ≥ 0} γ^t r(s_t, a_t)]` (`PolicyValue`).

**Formalization Note.** Written as `sSup` of the set of values `{V_π(s) : π ∈ Π}`. For `γ ∈ (0,1)`
and a finite MDP with a nonempty action set this set is nonempty and bounded (by `max |r| / (1-γ)`),
and the supremum is attained by an optimal deterministic policy (p.4, "It is known that an optimal
deterministic policy exists"), so it is the paper's maximum. -/
noncomputable def Vstar {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) : ℝ :=
  sSup {v : ℝ | ∃ π : S → A → ℝ, IsPolicy π ∧ PolicyValue π P r γ s = v}

end AggStatePG


