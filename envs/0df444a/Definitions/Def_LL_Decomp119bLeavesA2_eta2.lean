-- Prove2me | Definitions.Def_LL_Decomp119bLeavesA2_eta2
-- name    : LL_Decomp119bLeavesA2_eta2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:35:38.36403+00:00
-- url     : https://prove2.me/theorems/94601d85-80bf-4c77-9071-b2d93a678376
-- title:
--   Helfgott's weight $\eta_2(t)=4\max(\log 2-|\log 2t|,0)$
-- statement:
--   For real $t$, $\eta_2(t)=4\max(\log 2-|\log 2t|,0)$ when $t>0$ and $\eta_2(t)=0$ otherwise; it is supported on $[1/4,1]$ with peak $4\log 2$ at $t=1/2$.

import Mathlib

namespace LL_Decomp119bLeavesA2

noncomputable section

open scoped ArithmeticFunction

noncomputable def eta2 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

end

end LL_Decomp119bLeavesA2


