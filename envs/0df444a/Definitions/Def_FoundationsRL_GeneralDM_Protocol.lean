-- Prove2me | Definitions.Def_FoundationsRL_GeneralDM_Protocol
-- name    : FoundationsRL_GeneralDM_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:20:34.808341+00:00
-- url     : https://prove2.me/theorems/e573d0de-75ab-4545-8108-32908580bc73
-- title:
--   The DMSO protocol's mean reward function (Eq. 6.2) and general regret (Eq. 6.3)
-- statement:
--   This bundle formalizes the basic quantities of the Decision Making with Structured
--   Observations (DMSO) protocol (Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making*, arXiv:2312.16730v1, §6.1, p. 94), the general decision-making
--   framework that Chapter 6 introduces to subsume the contextual-bandit, structured-bandit and
--   episodic-RL protocols of earlier chapters.
--
--   Fix a finite decision space $S$ (the book's $\Pi$) and a finite outcome type $Y$ (the joint
--   reward/observation space $R \times O$), and a reward-extraction map $\mathrm{rew} : Y \to
--   \mathbb{R}$ reading off the reward coordinate of an outcome. For a model $m : S \to (Y \to
--   \mathbb{R})$ assigning to each decision a conditional distribution over outcomes, the mean
--   reward function is
--   $$
--   f^m(\pi) := \mathbb{E}_{m,\pi}[r] = \sum_{y \in Y} m(\pi)(y) \cdot \mathrm{rew}(y).
--   $$
--
--   Given a horizon $T$, the decision-maker's realized action distributions $p : \mathrm{Fin}\,T
--   \to (S \to \mathbb{R})$, a fixed ground-truth reward function $f^\star$, and an optimal
--   decision $\pi^\star$, the regret is
--   $$
--   \mathrm{Reg} := \sum_{t=1}^T f^\star(\pi^\star) - \sum_{t=1}^T \mathbb{E}_{\pi \sim p_t}[f^\star(\pi)],
--   $$
--   the same form as the regret of the earlier bandit chapters (Eq. (6.3) is definitionally the
--   same expression as Eq. (4.3)), now stated for the general DMSO protocol's decision space and
--   reward function.
--
--   **Formalization Note** Rounds are indexed by `Fin T` (0-based), a convention shift from the
--   book's 1-indexed $t = 1, \dots, T$ with no effect on the value of the sum. `regret` is
--   restated here (not imported from Chapter 4's mission) because draft items cannot import other
--   chunks' drafts.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.1, p. 94, Eqs. (6.2)-(6.3)

import Mathlib

namespace FoundationsRL.GeneralDM

/-- The mean reward function `f^M` of a model `m : S → Y → ℝ` in the Decision Making with
Structured Observations (DMSO) protocol (Foster & Rakhlin, *Foundations of Reinforcement Learning
and Interactive Decision Making*, arXiv:2312.16730v1, §6.1, p. 94): given a fixed reward-extraction
map `rew : Y → ℝ` reading off the reward coordinate of a joint reward/observation outcome `y ∈ Y`,

`f^M(π) := E_{M,π}[r] = Σ_y m(π)(y) · rew(y)`,

where `m π : Y → ℝ` is the model's conditional outcome distribution at decision `π`. -/
noncomputable def fM {S Y : Type*} [Fintype S] [Fintype Y] (rew : Y → ℝ) (m : S → Y → ℝ)
    (π : S) : ℝ :=
  ∑ y, m π y * rew y

/-- Regret for the general DMSO protocol (Foster & Rakhlin, arXiv:2312.16730v1, Eq. (6.3), p. 94):

`Reg := Σ_{t=1}^T f⋆(π⋆) − Σ_{t=1}^T E_{π_t ∼ p_t}[f⋆(π_t)]`,

the cumulative gap between the optimal decision's reward and the expected reward of the
decision-maker's realized action distributions `p : Fin T → S → ℝ` (`p t` a probability vector
over the decision space `S`) under a fixed reward function `fstar` and optimal decision `piStar`.
As in the earlier bandit missions of this series, rounds are indexed by `Fin T` (0-based), a
convention shift from the book's 1-indexed `t = 1, …, T` with no effect on the value of the sum. -/
noncomputable def regret {S : Type*} [Fintype S] (fstar : S → ℝ) (piStar : S) (T : ℕ)
    (p : Fin T → S → ℝ) : ℝ :=
  ∑ t : Fin T, (fstar piStar - ∑ π : S, p t π * fstar π)

end FoundationsRL.GeneralDM


