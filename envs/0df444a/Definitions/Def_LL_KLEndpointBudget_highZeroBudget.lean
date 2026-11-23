-- Prove2me | Definitions.Def_LL_KLEndpointBudget_highZeroBudget
-- name    : LL_KLEndpointBudget_highZeroBudget
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:53:06.699528+00:00
-- url     : https://prove2.me/theorems/978be550-e665-4cfa-9bf0-9ea7722e72f4
-- title:
--   Budget for the zeros of height above $3.061\cdot10^{10}$
-- statement:
--   A function $\mathbb N\to\mathbb R$ giving for each log index $k\in\{0,43,\dots,57\}$ a fixed decimal budget (for example $0.02561$ at $k=0$ and $0.05926$ at $k=57$) and $0$ at every other index.

import Mathlib

namespace LL_KLEndpointBudget

noncomputable section

open Real Set MeasureTheory

noncomputable def highZeroBudget : ℕ → ℝ
  | 0 => 0.02561 | 43 => 0.03815 | 44 => 0.01118 | 45 => 0.00764
  | 46 => 0.01257 | 47 => 0.03821 | 48 => 0.03820 | 49 => 0.01473
  | 50 => 0.02260 | 51 => 0.03496 | 52 => 0.04548 | 53 => 0.05308
  | 54 => 0.05622 | 55 => 0.05902 | 56 => 0.05819 | 57 => 0.05926
  | _ => 0

end

end LL_KLEndpointBudget


