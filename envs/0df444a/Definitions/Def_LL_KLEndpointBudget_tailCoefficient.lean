-- Prove2me | Definitions.Def_LL_KLEndpointBudget_tailCoefficient
-- name    : LL_KLEndpointBudget_tailCoefficient
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:55:23.099572+00:00
-- url     : https://prove2.me/theorems/49f8a50e-5899-41ae-9941-bcf44084b271
-- title:
--   Brun-Titchmarsh tail coefficient
-- statement:
--   For real $\delta,u,X$, the number $2(1+\delta)(e^{u}-1)\,\dfrac{\log\bigl(e^{u}X(1+\delta)\bigr)}{\log\bigl(X(e^{u}-1)\bigr)}\,X$.

import Mathlib

namespace LL_KLEndpointBudget

noncomputable section

open Real Set MeasureTheory

noncomputable def tailCoefficient (δ u X : ℝ) : ℝ :=
  2 * (1 + δ) * (Real.exp u - 1) *
    (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) * X

end

end LL_KLEndpointBudget


