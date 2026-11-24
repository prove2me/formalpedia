-- Prove2me | Definitions.Def_LL_Task580_etaT2
-- name    : LL_Task580_etaT2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:51:57.935944+00:00
-- url     : https://prove2.me/theorems/2ba924cc-172c-465b-beea-b06c4c39a92f
-- title:
--   The weight $t^2e^{-t^2/2}$ on $t>0$
-- statement:
--   For real $t$, the value is $t^2e^{-t^2/2}$ when $t>0$ and $0$ otherwise.

import Mathlib

namespace LL_Task580

noncomputable section

noncomputable def etaT2 (t : ℝ) : ℝ := if 0 < t then t ^ 2 * Real.exp (-(t ^ 2) / 2) else 0

end

end LL_Task580


