-- Prove2me | Definitions.Def_LL_KLEndpointBudget_PrintedRow
-- name    : LL_KLEndpointBudget_PrintedRow
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:47:24.106418+00:00
-- url     : https://prove2.me/theorems/1d9fe75c-cc72-4c70-a6ae-6dd6ac1fe3af
-- title:
--   A printed row of Table 2
-- statement:
--   A record of seven natural numbers: the log index $k$ (with $k=0$ standing for $x_0=4\cdot10^{18}$), the weight exponent $m$, $\delta$ in units of $10^{-12}$, the height, $\sigma$ in hundredths, $a$ in units of $10^{-4}$, and the gap denominator $\Delta$.

import Mathlib

namespace LL_KLEndpointBudget

noncomputable section

open Real

structure PrintedRow where
  logIndex : ℕ
  m : ℕ
  deltaUnits : ℕ
  height : ℕ
  sigmaUnits : ℕ
  aUnits : ℕ
  gapDenom : ℕ
  deriving DecidableEq, Repr

end

end LL_KLEndpointBudget


