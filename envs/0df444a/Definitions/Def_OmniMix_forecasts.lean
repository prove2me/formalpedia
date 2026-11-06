-- Prove2me | Definitions.Def_OmniMix_forecasts
-- name    : OmniMix_forecasts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:09.567465+00:00
-- url     : https://prove2.me/theorems/77e6fcee-f608-412d-a545-070c41b0b6d1
-- title:
--   Forecasts produced on a sequence
-- statement:
--   Given a forecaster and a context–outcome sequence $(x_t,y_t)_{t}$, the forecast of round $t$ is the forecaster's output on the history $(x_s,y_s)_{s<t}$ and the current context $x_t$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1

import Mathlib
import Definitions.Def_OmniMix_Forecaster

namespace OmniMix

/-- **The forecasts `D_t` produced on a sequence.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1.

Given contexts `x` and outcomes `y`, round `t`'s forecast is the forecaster's output on the history
`(x_s, y_s)_{s < t}` and the current context `x_t`. -/
def forecasts {X : Type*} {T : ℕ} (A : Forecaster X T) (x : Fin T → X) (y : Fin T → Bool)
    (t : Fin T) : FinDist :=
  A t (fun s => (x ⟨s.val, s.isLt.trans t.isLt⟩, y ⟨s.val, s.isLt.trans t.isLt⟩)) (x t)

end OmniMix


