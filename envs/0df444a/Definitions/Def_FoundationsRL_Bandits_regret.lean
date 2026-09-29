-- Prove2me | Definitions.Def_FoundationsRL_Bandits_regret
-- name    : FoundationsRL_Bandits_regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:55:44.923918+00:00
-- url     : https://prove2.me/theorems/e8d417ba-903b-4f03-bfdd-610a96c75134
-- title:
--   Multi-armed bandit regret (Eq. 2.3)
-- statement:
--   Fix a decision space $\Pi = \{1,\dots,A\}$ and a mean reward function
--   $f^\star : \Pi \to \mathbb{R}$, together with a decision $\pi^\star$ attaining
--   $\max_{\pi} f^\star(\pi)$. For a horizon $T$ and a sequence of per-round decision
--   distributions $p_1,\dots,p_T$ (where $p_t(\pi)$ is the probability the learner
--   selects $\pi$ at round $t$), the **regret** is
--
--   $$\mathrm{Reg} := \sum_{t=1}^T f^\star(\pi^\star) - \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\bigl[f^\star(\pi_t)\bigr].$$
--
--   This is Foster & Rakhlin's Eq. (2.3): the cumulative gap between always playing
--   the best decision and the learner's actual (possibly randomized) choices.
--   Sublinear regret, $\mathrm{Reg}/T \to 0$, is the basic desideratum for every
--   bandit algorithm in the chapter.
--
--   **Formalization Note.** `p : ℕ → Fin A → ℝ` gives each round's decision weights
--   directly as reals rather than through a `PMF`; callers that need `p t` to be a
--   genuine probability vector (nonnegative, summing to $1$) supply that as a separate
--   hypothesis where it matters. A deterministic algorithm's decision at round $t$ is
--   recovered as the point mass `fun a => if a = pi t then 1 else 0`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 22, Eq. (2.3)

import Mathlib

namespace FoundationsRL.Bandits

/-- The multi-armed bandit regret (Foster–Rakhlin, Eq. (2.3), p. 22),
`Reg := Σ_{t=1}^T f⋆(π⋆) − Σ_{t=1}^T E_{π_t ∼ p_t}[f⋆(π_t)]`,
for a mean reward function `fStar`, an optimal decision `piStar`, a horizon `T`,
and a sequence of per-round decision distributions `p : ℕ → Fin A → ℝ`
(`p t a` is the probability of playing `a` at round `t`; callers supply that
`p t` is a genuine probability vector when that fact is needed). -/
noncomputable def regret {A : ℕ} (fStar : Fin A → ℝ) (piStar : Fin A) (T : ℕ)
    (p : ℕ → Fin A → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, (fStar piStar - ∑ a : Fin A, p t a * fStar a)

end FoundationsRL.Bandits


