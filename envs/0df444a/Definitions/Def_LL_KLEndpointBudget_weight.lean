-- Prove2me | Definitions.Def_LL_KLEndpointBudget_weight
-- name    : LL_KLEndpointBudget_weight
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:54:33.740257+00:00
-- url     : https://prove2.me/theorems/2a3d495d-09e7-42e8-a2f8-9767b6c978d2
-- title:
--   Polynomial weight $w_m(t)=(4t(1-t))^m$
-- statement:
--   For $m\in\mathbb N$ and real $t$, $w_m(t)=(4t(1-t))^m$.

import Mathlib

namespace LL_KLEndpointBudget

noncomputable section

open Real Set MeasureTheory intervalIntegral

def weight (m : ℕ) (t : ℝ) : ℝ := (4 * t * (1 - t)) ^ m

end

end LL_KLEndpointBudget


