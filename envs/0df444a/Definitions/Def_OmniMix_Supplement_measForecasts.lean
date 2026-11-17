-- Prove2me | Definitions.Def_OmniMix_Supplement_measForecasts
-- name    : OmniMix_Supplement_measForecasts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:32:51.722292+00:00
-- url     : https://prove2.me/theorems/5da5dd92-91da-45b0-856c-3763d308957c
-- title:
--   Forecast measures $D_t$ produced on a sequence
-- statement:
--   Given a general online forecaster $A$, contexts $x_1,\dots,x_T$ and outcomes $y_1,\dots,y_T$, the **forecast of round $t$** is the probability measure $D_t$ that $A$ outputs on the history $(x_s,y_s)_{s<t}$ and the current context $x_t$.
--
--   It turns a forecaster and a sequence into the sequence of forecast measures that the regret is evaluated on.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_OmniMix_Supplement_MeasForecaster

namespace OmniMix.Supplement

/-- **The forecasts `D_t` of a measure-valued forecaster on a sequence.** Liu–Luo–Ratliff,
*Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1.

Given contexts `x` and outcomes `y`, round `t`'s forecast is the forecaster's output on the history
`(x_s, y_s)_{s < t}` and the current context `x_t`. -/
def measForecasts {X : Type*} {T : ℕ} (A : MeasForecaster X T) (x : Fin T → X) (y : Fin T → Bool)
    (t : Fin T) : MeasureTheory.ProbabilityMeasure unitInterval :=
  A t (fun s => (x ⟨s.val, s.isLt.trans t.isLt⟩, y ⟨s.val, s.isLt.trans t.isLt⟩)) (x t)

end OmniMix.Supplement


