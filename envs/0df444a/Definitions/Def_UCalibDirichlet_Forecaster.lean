-- Prove2me | Definitions.Def_UCalibDirichlet_Forecaster
-- name    : UCalibDirichlet_Forecaster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:11.73944+00:00
-- url     : https://prove2.me/theorems/e9682075-33ae-4a83-9c51-eaf3f9b31de0
-- title:
--   Randomized forecaster
-- statement:
--   In each round $t=1,\dots,T$ a forecaster (randomly) announces a distribution $P_t\in\Delta_K$ over the $K$ labels; the outcome $i_t$ is then revealed. A forecaster is described here by the law of its forecast in each round as a function of the outcomes $i_1,\dots,i_{t-1}$ observed so far.
--
--   **Formalization Note** Against a fixed outcome sequence the expected regret depends on a randomized forecaster only through the law of each forecast given the past outcomes (its internal randomization is integrated out), so this description loses nothing. Validity (each law is a probability measure on the simplex) is a separate predicate.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1, p.1

import Mathlib

open MeasureTheory

namespace UCalibDirichlet

/-- **A (randomized) forecaster.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), §1, p.1: "At time `t = 1, …, T`, a forecaster (randomly) announces a distribution
`P_t ∈ Δ_K` …. Simultaneously, an adversary chooses the actual outcome `i_t ∈ [K]` for this round
that could depend on the history (but not `P_t`). Finally, the outcome `i_t` is revealed to the
forecaster."

A `Forecaster K` maps a round index `t` and the outcomes `i_1, …, i_t` seen so far (a history
`Fin t → Fin K`) to the law of the forecast announced next, a measure on `Fin K → ℝ`.

**Formalization Note.** The regret (2) against a fixed outcome sequence depends on the
forecaster only through the law of each forecast `P_{t+1}` given the past outcomes (expectation
is linear, and the forecaster's internal randomization is integrated out), so a forecaster is
encoded by these laws. Validity (probability measures carried by `Δ_K`) is `IsForecaster`. -/
abbrev Forecaster (K : ℕ) : Type := (t : ℕ) → (Fin t → Fin K) → Measure (Fin K → ℝ)

end UCalibDirichlet


