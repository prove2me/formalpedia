-- Prove2me | Definitions.Def_LL_KLEndpointBudget_lowZeroBudget
-- name    : LL_KLEndpointBudget_lowZeroBudget
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:52:49.765959+00:00
-- url     : https://prove2.me/theorems/d99d5c4d-b8a0-47bc-b287-6dcd05d41219
-- title:
--   Budget for the zeros of height at most $3.061\cdot10^{10}$
-- statement:
--   A function $\mathbb N\to\mathbb R$ giving for each log index $k\in\{0,43,\dots,57\}$ a fixed decimal budget (for example $0.58620$ at $k=0$ and $0.01602$ at $k=57$) and $0$ at every other index.

import Mathlib

namespace LL_KLEndpointBudget

noncomputable section

open Real Set MeasureTheory

noncomputable def lowZeroBudget : ℕ → ℝ
  | 0 => 0.58620 | 43 => 0.57871 | 44 => 0.56710 | 45 => 0.54479
  | 46 => 0.51919 | 47 => 0.47893 | 48 => 0.44157 | 49 => 0.40912
  | 50 => 0.35074 | 51 => 0.27324 | 52 => 0.18750 | 53 => 0.11754
  | 54 => 0.07173 | 55 => 0.04355 | 56 => 0.02638 | 57 => 0.01602
  | _ => 0

end

end LL_KLEndpointBudget


