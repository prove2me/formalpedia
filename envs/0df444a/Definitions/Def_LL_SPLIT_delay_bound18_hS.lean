-- Prove2me | Definitions.Def_LL_SPLIT_delay_bound18_hS
-- name    : LL_SPLIT_delay_bound18_hS
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:04:18.839231+00:00
-- url     : https://prove2.me/theorems/0a6fd03e-5abd-4e60-921a-ec50363ea93a
-- title:
--   The piecewise exponential weight $h(s)$
-- statement:
--   For real $s$, $h(s)=e^{-2}$ if $s\le 2$, $h(s)=e^{-s}$ if $2<s\le 3$, and $h(s)=\frac3s e^{-s}$ if $s>3$.

import Mathlib

namespace LL_SPLIT_delay_bound18

noncomputable section

open Real

noncomputable def hS (s : ℝ) : ℝ :=
  if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 / s * exp (-s)

end

end LL_SPLIT_delay_bound18


