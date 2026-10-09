-- Prove2me | Definitions.Def_ReinfRegGames_TimeAvg_TimeAverage
-- name    : ReinfRegGames_TimeAvg_TimeAverage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:38.79622+00:00
-- url     : https://prove2.me/theorems/050d0dbd-c0f7-4ccc-b3f7-b46da4395e28
-- title:
--   Theorem 6.1 / Proposition 6.2, pp. 25–26 — the time average x̄(t) = t⁻¹∫₀ᵗ x(s) ds
-- statement:
--   For a trajectory of mixed profiles $x(t)$ (one probability vector $x_k(t)$ per player $k$) and a time $t > 0$, the **time average** is the profile
--   $$\bar x(t) = \frac1t \int_0^t x(s)\,ds, \qquad \bar x_{k\alpha}(t) = \frac1t \int_0^t x_{k\alpha}(s)\,ds .$$
--
--   Time averages are the objects whose long-run behaviour Theorem 6.1 and Proposition 6.2 describe: even when the trajectory $x(t)$ itself cycles, $\bar x(t)$ can converge to the set of Nash equilibria.
--
--   **Formalization Note** The average is defined coordinatewise with the interval integral. Only $t > 0$ is meaningful; at $t = 0$ Lean's convention $0^{-1} = 0$ gives the value $0$, and no statement of the mission uses that value (all are limits as $t \to \infty$).
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 25–26, Theorem 6.1 and Proposition 6.2

import Mathlib

namespace ReinfRegGames.TimeAvg

/-- The time average `x̄(t) = t⁻¹ ∫₀ᵗ x(s) ds` of a trajectory of mixed profiles `x(t)`
(Theorem 6.1 and Proposition 6.2, arXiv:1407.6267v2, pp. 25–26), coordinatewise:
`x̄_{kα}(t) = t⁻¹ ∫₀ᵗ x_{kα}(s) ds`. Only `t > 0` is meaningful (at `t = 0` Lean's `0⁻¹ = 0`
gives the junk value `0`); the statements of the mission only use `t → ∞`. -/
noncomputable def timeAvg {ι : Type*} {A : ι → Type*} (x : ℝ → ∀ k, A k → ℝ) (t : ℝ) :
    ∀ k, A k → ℝ :=
  fun k α => t⁻¹ * ∫ s in (0 : ℝ)..t, x s k α

end ReinfRegGames.TimeAvg


