-- Prove2me | Definitions.Def_OmniMix_Supplement_MeasForecaster
-- name    : OmniMix_Supplement_MeasForecaster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:32:20.172348+00:00
-- url     : https://prove2.me/theorems/2d6d0076-978b-4cd4-8964-c2c81a26fbcf
-- title:
--   General online forecaster with probability-measure forecasts
-- statement:
--   Fix a context space $X$ and a horizon $T$. In each round $t=1,\dots,T$ nature reveals a context $x_t\in X$, the learner forecasts, and nature reveals an outcome $y_t\in\{0,1\}$. A **(general) online forecaster** is a rule that, in round $t$, maps the history $(x_1,y_1),\dots,(x_{t-1},y_{t-1})$ and the current context $x_t$ to a forecast distribution $D_t$, an arbitrary Borel probability measure on $[0,1]$; the prediction $P_t$ is drawn from $D_t$.
--
--   This is the forecaster class of the paper's lower bounds (Theorems 1.1 and 1.3), which hold for every online forecaster.
--
--   **Formalization Note** Rounds are numbered $0,\dots,T-1$. A forecaster with its own internal randomness $\omega$ is covered: on a fixed sequence the regret is linear in the $D_t$ and its benchmark term does not depend on $\omega$, so the expected regret over $\omega$ equals the regret of the averaged forecaster $\bar D_t=\mathbb E_\omega D_t^\omega$, which is again of this form.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 (PDF p.3); App. A.1, p.20 (PDF p.22)

import Mathlib

namespace OmniMix.Supplement

/-- **General (measure-valued) online forecaster.** Liu–Luo–Ratliff, *Omniprediction for All
Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1: "the learner then makes a prediction
`P_t ∈ [0, 1]` … `P_t` … is generally random; we let `D_t` be the distribution over `[0, 1]` from
which `P_t` is drawn", and App. A.1, p.20: "Fix an arbitrary, possibly randomized forecaster `A`".

A `MeasForecaster X T` maps, for each round `t < T`, the history of the first `t` context–outcome
pairs and the current context `x_t` to an arbitrary Borel probability measure `D_t` on `[0,1]`.

**Formalization Note.** This is the forecaster type of the lower bounds (Theorems 1.1 and 1.3),
which quantify over every online forecaster; the base mission's `OmniMix.Forecaster` allows only
finitely supported forecasts. Rounds are 0-based. A randomized forecaster with internal seed `ω`
is covered: on a fixed (oblivious) sequence the regret is linear in the `D_t` and its comparator
term does not depend on `ω`, so `E_ω[Reg]` equals the regret of the seed-averaged forecaster
`D̄_t = E_ω D_t^ω`, which is again a `MeasForecaster`. -/
def MeasForecaster (X : Type*) (T : ℕ) : Type _ :=
  (t : Fin T) → (Fin t.val → X × Bool) → X → MeasureTheory.ProbabilityMeasure unitInterval

end OmniMix.Supplement


