-- Prove2me | Definitions.Def_IAFTRL_Run
-- name    : IAFTRL_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:56.174854+00:00
-- url     : https://prove2.me/theorems/42d71c9e-f9c3-4a5a-9c09-60f7e12e1425
-- title:
--   Random variables of a linear-bandit interaction
-- statement:
--   A **run** on a sample space $\Omega$ collects, for every round, the random variables of the interaction between a learner and an environment:
--   - the index $A_t$ of the action played;
--   - the observed feedback $Y_t\in\mathbb R$;
--   - the loss vector $\theta_t\in\mathbb R^d$ chosen by the environment;
--   - the learner's sampling distribution $p_t$ on the actions;
--   - the pre-action σ-algebra $\mathcal G_t$: everything that has happened before the action of round $t$ is drawn (earlier rounds, $\theta_t$, the environment's pre-action randomness).
--
--   What makes such a family an execution of IA-FTRL is the predicate `IsIAFTRLRun`.
--
--   **Formalization Note** Rounds are 0-based: Lean round $t$ is the paper's round $t+1$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, p.5; Algorithm 1, p.18; Appendix J.1, p.204

import Mathlib

namespace IAFTRL

/-- **The random variables of a linear-bandit interaction.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, p.5 and
Algorithm 1, p.18: in round `t` the environment selects a loss vector `θ_t`, the learner computes a
sampling distribution `p_t`, draws `A_t ∼ p_t` and observes the feedback `Y_t`; Appendix J.1, p.204:
the pre-action filtration.

A `Run d K Ω` on a sample space `Ω` consists of, for every round `t`:
- `A t : Ω → Fin K`, the index of the action played;
- `Y t : Ω → ℝ`, the observed feedback;
- `θs t : Ω → ℝ^d`, the loss vector chosen by the environment;
- `p t : Ω → ℝ^K`, the learner's sampling distribution;
- `G t`, the pre-action σ-algebra of round `t` (everything that has happened before the action of
  round `t` is drawn: earlier rounds, `θ_t`, the environment's pre-action randomness).

What makes such a family an execution of IA-FTRL is the predicate `IsIAFTRLRun`.

**Formalization Note.** Rounds are 0-based: Lean round `t` is the paper's round `t + 1`. -/
structure Run (d K : ℕ) (Ω : Type*) where
  /-- The index of the action `A_{t+1}` played in (0-based) round `t`. -/
  A : ℕ → Ω → Fin K
  /-- The observed feedback `Y_{t+1}`. -/
  Y : ℕ → Ω → ℝ
  /-- The loss vector `θ_{t+1}`. -/
  θs : ℕ → Ω → (Fin d → ℝ)
  /-- The sampling distribution `p_{t+1}`. -/
  p : ℕ → Ω → (Fin K → ℝ)
  /-- The pre-action σ-algebra of round `t + 1`. -/
  G : ℕ → MeasurableSpace Ω

end IAFTRL


