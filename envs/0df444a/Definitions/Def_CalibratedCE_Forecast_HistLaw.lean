-- Prove2me | Definitions.Def_CalibratedCE_Forecast_HistLaw
-- name    : CalibratedCE_Forecast_HistLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:35:25.639187+00:00
-- url     : https://prove2.me/theorems/292a9120-8f9f-4a1d-b6fc-5c340f8e7639
-- title:
--   Law of the history when a randomized forecaster faces a learning opponent
-- statement:
--   Player 1 uses a **randomized forecaster** $F$: to each history $h$ (the forecasts and plays of the previous rounds) it assigns a probability distribution $F(h)$ on forecasts $p\in\mathbb R^n$. Player 2 uses a **learning rule** $A$: to each history $h$ it assigns a probability distribution $A(h)$ on its strategies $\{0,\dots,n-1\}$; a deterministic rule is one whose $A(h)$ are point masses, and a fixed sequence of plays is a rule that reads the round number off the length of $h$.
--
--   Round $t+1$ is played as follows: given the history $h$ of the first $t$ rounds, the forecast $p$ is drawn from $F(h)$ and the play $j$ from $A(h)$, **independently**, and $(p,j)$ is appended to $h$. The **law of the first $t$ rounds** $\mathbb P_{F,A}^t$ is the distribution on histories so obtained:
--
--   $$
--   \mathbb P^0_{F,A} = \delta_{()}, \qquad
--   \mathbb P^{t+1}_{F,A}(h') = \sum_{h,\,p,\,j:\ h' = h\,(p,j)} \mathbb P^t_{F,A}(h)\,F(h)(p)\,A(h)(j).
--   $$
--
--   Independence of the two draws given the past is the simultaneity of the stage game: player 2 does not see the forecast of the current round. An opponent who could see it would defeat every forecaster (Oakes 1985, quoted on p. 46).
--
--   **Formalization Note** Distributions are Mathlib `PMF`s (discrete probability distributions); the law is built by `PMF.bind` and `PMF.map`, so no σ-algebra on histories is needed. Rounds are counted from $0$: `histLaw F A t` is the law of the list of the first $t$ (forecast, play) pairs.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 49, Theorem 3 (randomized forecast against any learning rule of player 2)

import Mathlib

namespace CalibratedCE.Forecast

/-- The law of the history of the first `t` rounds when player 1 uses the randomized forecaster
`F` and player 2 uses the (possibly randomized) learning rule `A`. A history is the list of
(forecast, player 2's play) pairs, oldest first. In each round, given the history `h` so far,
the forecast is drawn from `F h` and player 2's play from `A h`, independently: player 2 does not
see the current forecast. -/
noncomputable def histLaw {n : ℕ} (F : List ((Fin n → ℝ) × Fin n) → PMF (Fin n → ℝ))
    (A : List ((Fin n → ℝ) × Fin n) → PMF (Fin n)) :
    ℕ → PMF (List ((Fin n → ℝ) × Fin n))
  | 0 => PMF.pure []
  | t + 1 => (histLaw F A t).bind fun h =>
      (F h).bind fun p => (A h).map fun j => h ++ [(p, j)]

end CalibratedCE.Forecast


