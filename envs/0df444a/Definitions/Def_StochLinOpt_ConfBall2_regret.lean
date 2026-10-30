-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_regret
-- name    : StochLinOpt_ConfBall2_regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:49:38.86649+00:00
-- url     : https://prove2.me/theorems/f97d5b3f-022d-4e45-b52c-c19f1775c635
-- title:
--   Cumulative regret $R_T$
-- statement:
--   For a mean vector $\mu$, an optimal decision $x^*\in\operatorname{argmin}_{x\in D}\mu^\top x$ and decisions $x_1,x_2,\dots$, the **cumulative regret** after $T$ rounds is
--
--   $$R_T=\sum_{t=1}^T\bigl(\mu^\top x_t-\mu^\top x^*\bigr).$$
--
--   **Formalization Note** The optimality of $x^*$ is a hypothesis of the statements that use $R_T$; $R_0=0$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §2, p. 3

import Mathlib
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Cumulative regret `R_T`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §2, p. 3: "If x1, . . . , xT are the decisions made in
the game, then define the cumulative regret by RT = Σ_{t=1}^T (µ†xt − µ†x∗) where x∗ ∈ D is an
optimal decision for µ").

`regret μ xstar x T = ∑_{t=1}^T (μ ⬝ x_t − μ ⬝ x*)`.

**Formalization Note** Rounds are 1-based (`Finset.Icc 1 T`); `R_0 = 0`. The optimality of
`xstar` is a hypothesis of the statements that use `regret`. -/
def regret {n : ℕ} (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar)

end StochLinOpt.ConfBall2


