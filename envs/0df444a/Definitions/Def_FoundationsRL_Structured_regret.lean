-- Prove2me | Definitions.Def_FoundationsRL_Structured_regret
-- name    : FoundationsRL_Structured_regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:16:44.134976+00:00
-- url     : https://prove2.me/theorems/cfc05374-d0df-4259-a95e-e5e4e154922f
-- title:
--   Regret for the structured bandit protocol (Eq. 4.3)
-- statement:
--   This definition formalizes **regret** for the structured decision-making protocol of
--   Chapter 4 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
--   Decision Making*, arXiv:2312.16730v1, Eq. (4.3), p. 57). Fix a finite decision space
--   $\Pi$, a ground-truth mean reward function $f^\star : \Pi \to \mathbb{R}$, and an optimal
--   decision $\pi^\star$. Over a horizon $T$, at each round $t = 1,\dots,T$ the decision-maker
--   plays a distribution $p_t \in \Delta(\Pi)$ over decisions. The regret is
--
--   $$
--   \mathrm{Reg} := \sum_{t=1}^T f^\star(\pi^\star) - \sum_{t=1}^T \mathbb{E}_{\pi \sim p_t}[f^\star(\pi)].
--   $$
--
--   `regret fstar piStar T p` computes exactly this quantity, where `p t` is the round-`t`
--   decision weighting (a function `S → ℝ`, not required by this definition itself to be a
--   genuine probability distribution — callers that need that state it separately, matching
--   how the book's own Eq. (4.3) is written generically before any particular algorithm's
--   `p_t` is plugged in).
--
--   **Formalization Note** Rounds are indexed by `Fin T` (0-based), a convention shift from
--   the book's 1-indexed $t=1,\dots,T$ with no effect on the value of the sum.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (4.3), p. 57

import Mathlib

namespace FoundationsRL.Structured

/-- Regret for the structured bandit protocol (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (4.3), p. 57):

`Reg := ∑_{t=1}^T f⋆(π⋆) − ∑_{t=1}^T E_{π_t ∼ p_t}[f⋆(π_t)]`,

the cumulative gap between the optimal decision's reward and the expected reward of the
decision-maker's realized action distributions `p : Fin T → S → ℝ` (`p t` a probability vector
over the decision space `Π`) under the ground-truth mean reward function `fstar` and optimal
decision `piStar`. -/
noncomputable def regret {S : Type*} [Fintype S] (fstar : S → ℝ) (piStar : S) (T : ℕ)
    (p : Fin T → S → ℝ) : ℝ :=
  ∑ t : Fin T, (fstar piStar - ∑ π : S, p t π * fstar π)

end FoundationsRL.Structured


