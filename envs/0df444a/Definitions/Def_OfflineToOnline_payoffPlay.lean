-- Prove2me | Definitions.Def_OfflineToOnline_payoffPlay
-- name    : OfflineToOnline_payoffPlay
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:13.617782+00:00
-- url     : https://prove2.me/theorems/a8d790ad-2cba-4ed6-9098-ffa73af08590
-- title:
--   Payoff-based Blackwell strategy and its play
-- statement:
--   A **payoff-based strategy** for player 1 (a Blackwell algorithm $\mathrm{AlgB}$) chooses its action at round $t$ from the history of its own past actions and the realized vector payoffs:
--
--   $$
--   x_t=\mathrm{AlgB}\big(x_1,\dots,x_{t-1},\ \boldsymbol p(x_1,y_1),\dots,\boldsymbol p(x_{t-1},y_{t-1})\big).
--   $$
--
--   Its **play** against a sequence $y_1,y_2,\dots$ of player 2 actions is the sequence $x_1,x_2,\dots$ defined by this recursion. Online-IG (Algorithm 2) runs one copy of such an algorithm per subproblem and feeds it exactly this information.
--
--   **Formalization Note** Rounds are $0$-indexed: round $t$ sees the history of rounds $0,\dots,t-1$. Strategies are deterministic; against a deterministic strategy an adaptive player 2 is the same as a fixed sequence of actions.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 3, p.12; Remark 2, p.13; Algorithm 2, p.21

import Mathlib

namespace OfflineToOnline

/-- A deterministic, payoff-based player 1 strategy (a Blackwell algorithm `AlgB`, Algorithm 2,
p.21, and Remark 2, p.13): at round `t` it maps the history of its own past actions and the
realized vector payoffs, `(x_s, p(x_s, y_s))_{s < t}`, to an action. -/
abbrev PayoffStrategy (m d : ℕ) : Type :=
  (t : ℕ) → (Fin t → (Fin m → ℝ) × (Fin d → ℝ)) → (Fin m → ℝ)

/-- The play of a payoff-based strategy `A` against a sequence `y` of player 2 actions:
`x_t = A_t((x_s, p(x_s, y_s))_{s < t})`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 3, p.12; Algorithm 2, p.21 ("θ_t^(i) ← AlgB^(i)(θ_1^(i), …, θ_{t−1}^(i),
p(θ_1^(i), y_1^(i)), …, p(θ_{t−1}^(i), y_{t−1}^(i)))").

Formalization Note: rounds are `0`-indexed. Against a deterministic strategy, an adaptive player 2
is the same as a fixed sequence `y`. -/
noncomputable def payoffPlay {m k d : ℕ} (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ))
    (A : PayoffStrategy m d) (y : ℕ → Fin k → ℝ) : ℕ → Fin m → ℝ
  | t => A t (fun s => (payoffPlay p A y s.1, p (payoffPlay p A y s.1) (y s.1)))
termination_by t => t
decreasing_by exact s.2

end OfflineToOnline


