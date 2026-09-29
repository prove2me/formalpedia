-- Prove2me | Definitions.Def_CalibratedCE_Forecast_IsDist
-- name    : CalibratedCE_Forecast_IsDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:34:42.386879+00:00
-- url     : https://prove2.me/theorems/dd6bb4eb-14ae-4825-aa8e-818ae9b54914
-- title:
--   Probability vector on a finite set (Section 2)
-- statement:
--   Let $\alpha$ be a finite set. A vector $p = (p_a)_{a\in\alpha}\in\mathbb R^{\alpha}$ is a **probability vector** (a mixed strategy, or a forecast of the opponent's play) when
--
--   $$
--   p_a \ge 0 \ \text{ for every } a\in\alpha, \qquad \sum_{a\in\alpha} p_a = 1 .
--   $$
--
--   Foster and Vohra's forecasts are probability vectors over the opponent's pure strategies: "a forecast … is a probability distribution over S(2)" (pp. 43–44). Every forecast, every grid point and every weight vector of the Appendix is required to be a probability vector.
--
--   **Formalization Note** The predicate is stated for an arbitrary finite type; it is used with $\alpha = \mathrm{Fin}\,n$ (the opponent's strategies) and $\alpha = \mathrm{Fin}\,k$ (the $k$ forecasts of the Appendix).
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), pp. 43–44, Section 2 (forecasts as probability distributions)

import Mathlib

namespace CalibratedCE.Forecast

/-- `p` is a probability vector on the finite set `α`: nonnegative entries summing to `1`. -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

end CalibratedCE.Forecast


